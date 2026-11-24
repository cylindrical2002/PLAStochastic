#!/usr/bin/env python3
"""Parallel multi-range downloader and MD5 verifier for the four standard SOSD 200M uint64 datasets."""

from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import os
from pathlib import Path
import subprocess
import urllib.request

DATASETS = {
    "wiki_ts_200M_uint64": (
        "4f1402b1c476d67f77d2da4955432f7d",
        "https://dataverse.harvard.edu/api/access/datafile/:persistentId?persistentId=doi:10.7910/DVN/JGVF9A/SVN8PI",
    ),
    "fb_200M_uint64": (
        "3b0f820caa0d62150e87ce94ec989978",
        "https://dataverse.harvard.edu/api/access/datafile/:persistentId?persistentId=doi:10.7910/DVN/JGVF9A/EATHF7",
    ),
    "books_200M_uint64": (
        "aeedc7be338399ced89d0bb82287e024",
        "https://dataverse.harvard.edu/api/access/datafile/:persistentId?persistentId=doi:10.7910/DVN/JGVF9A/A6HDNT",
    ),
    "osm_cellids_200M_uint64": (
        "a7f6b8d2df09fcda5d9cfbc87d765979",
        "https://dataverse.harvard.edu/api/access/datafile/:persistentId?persistentId=doi:10.7910/DVN/JGVF9A/8FX9BV",
    ),
}

CHUNK_SIZE = 16 * 1024 * 1024  # 16 MiB


class _NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None


def resolve_s3_url_and_size(dataverse_url: str) -> tuple[str, int]:
    opener = urllib.request.build_opener(_NoRedirect)
    req = urllib.request.Request(
        dataverse_url, headers={"Range": "bytes=0-0", "User-Agent": "curl/8.0"}
    )
    try:
        with opener.open(req, timeout=20) as resp:
            s3_url = resp.geturl()
    except urllib.error.HTTPError as e:
        if e.code in (301, 302, 303, 307, 308):
            s3_url = e.headers["Location"]
        else:
            raise

    probe = urllib.request.Request(s3_url, headers={"Range": "bytes=0-0", "User-Agent": "curl/8.0"})
    with urllib.request.urlopen(probe, timeout=20) as resp:
        cr = resp.headers["Content-Range"]
        total = int(cr.split("/")[-1])
        return s3_url, total


def fetch_range(url: str, out_path: Path, start: int, end: int) -> int:
    for attempt in range(4):
        try:
            req = urllib.request.Request(
                url, headers={"Range": f"bytes={start}-{end}", "User-Agent": "curl/8.0"}
            )
            with urllib.request.urlopen(req, timeout=60) as resp:
                data = resp.read()
            expected = end - start + 1
            if len(data) != expected:
                raise RuntimeError(f"Short read {len(data)} != {expected}")
            fd = os.open(out_path, os.O_WRONLY)
            try:
                os.pwrite(fd, data, start)
            finally:
                os.close(fd)
            return len(data)
        except Exception:
            if attempt == 3:
                raise
    return 0


def md5_file(path: Path) -> str:
    h = hashlib.md5()
    with path.open("rb") as f:
        while True:
            buf = f.read(8 * 1024 * 1024)
            if not buf:
                break
            h.update(buf)
    return h.hexdigest()


def ensure_dataset(name: str, out_dir: Path, workers: int) -> None:
    expected_md5, url = DATASETS[name]
    raw_path = out_dir / name
    if raw_path.is_file() and raw_path.stat().st_size == 8 + 200_000_000 * 8:
        got = md5_file(raw_path)
        if got == expected_md5:
            print(f"[OK] {name} already present and MD5 verified ({got}).", flush=True)
            return

    zst_path = out_dir / f"{name}.zst"
    s3_url, total_size = resolve_s3_url_and_size(url)
    print(f"[DOWNLOAD] {name}.zst ({total_size / 1e6:.1f} MB) with {workers} workers...", flush=True)

    with zst_path.open("wb") as f:
        f.truncate(total_size)

    ranges = []
    pos = 0
    while pos < total_size:
        end = min(pos + CHUNK_SIZE - 1, total_size - 1)
        ranges.append((pos, end))
        pos = end + 1

    done_bytes = 0
    with ThreadPoolExecutor(max_workers=workers) as ex:
        futs = [ex.submit(fetch_range, s3_url, zst_path, s, e) for s, e in ranges]
        for fut in as_completed(futs):
            done_bytes += fut.result()

    print(f"[DECOMPRESS] {zst_path.name} -> {raw_path.name} ...", flush=True)
    subprocess.run(["zstd", "-d", "-f", "--rm", str(zst_path), "-o", str(raw_path)], check=True)
    got_md5 = md5_file(raw_path)
    if got_md5 != expected_md5:
        raise RuntimeError(f"MD5 mismatch for {name}: got {got_md5}, expected {expected_md5}")
    print(f"[VERIFIED] {name}: {raw_path.stat().st_size} bytes, md5={got_md5}", flush=True)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument(
        "--datasets",
        nargs="+",
        default=list(DATASETS.keys()),
        choices=list(DATASETS.keys()),
        help="Subset of SOSD 200M datasets to download (default: all four).",
    )
    ap.add_argument(
        "--out-dir",
        type=Path,
        default=Path(__file__).resolve().parent / "sosd_data",
        help="Destination directory for decompressed SOSD binary files.",
    )
    ap.add_argument("--workers", type=int, default=16, help="Parallel HTTP range workers.")
    args = ap.parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    for name in args.datasets:
        ensure_dataset(name, args.out_dir, args.workers)


if __name__ == "__main__":
    main()
