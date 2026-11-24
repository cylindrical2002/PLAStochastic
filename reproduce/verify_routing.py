#!/usr/bin/env python3
"""Exact rational verification of O'Rourke ALG-OPT, CSR bucket routing, and Lemma 5.1.

Verifies on deterministic, clustered, adversarial, and pseudo-random strictly increasing
key arrays across eps in {2, 3, 4, 8}:
  1. The O(n) convex-hull shrinking-cone segmentation matches the exact O(n^2) rational
     Fourier-Motzkin feasibility oracle bit-for-bit on every prefix.
  2. Complete-coverage RE-PGM with CSR boundary-crossing bucket tables returns the exact
     predecessor rank for every stored key, adjacent midpoint, and out-of-range query.
  3. Lemma 5.1 holds at every layer l >= 0:
       sum_j b_{l,j} <= M_{l+1} - 1,
       (1/n) sum_{i=0}^{n-1} b_{l, j_l(p_i)} <= ((N_l - 1) * Delta_l) / n < 1.
"""

from __future__ import annotations

from bisect import bisect_right
from dataclasses import dataclass
from fractions import Fraction
import random


def prefix_feasible_oracle(keys: list[Fraction], eps: Fraction) -> bool:
    """Exact O(m^2) Fourier-Motzkin rational feasibility check for a prefix."""
    m = len(keys)
    if m <= 2:
        return True
    s_min = None
    s_max = None
    for i in range(m):
        for j in range(i + 1, m):
            dx = keys[j] - keys[i]
            lo = (Fraction(j - i) - 2 * eps) / dx
            hi = (Fraction(j - i) + 2 * eps) / dx
            if s_min is None or lo > s_min:
                s_min = lo
            if s_max is None or hi < s_max:
                s_max = hi
    assert s_min is not None and s_max is not None
    return s_min <= s_max


@dataclass(frozen=True)
class Segment:
    start: int
    end: int  # exclusive
    slope: Fraction
    intercept: Fraction


def alg_opt_exact(keys: list[Fraction], eps: Fraction) -> list[Segment]:
    """Exact O(n) shrinking-cone greedy segmentation (ALG-OPT) in rational arithmetic."""
    n = len(keys)
    assert n >= 1 and eps >= 1
    segments: list[Segment] = []
    s = 0
    while s < n:
        if s == n - 1:
            segments.append(Segment(s, n, Fraction(0), Fraction(0)))
            break

        # Lower convex hull of U_k = (x_{s+k}, k + eps); edge slopes strictly increase.
        uh: list[tuple[Fraction, Fraction]] = [(keys[s], eps)]
        # Upper convex hull of L_k = (x_{s+k}, k - eps); edge slopes strictly decrease.
        lh: list[tuple[Fraction, Fraction]] = [(keys[s], -eps)]
        uh_ptr = 0
        lh_ptr = 0
        s_min: Fraction | None = None
        s_max: Fraction | None = None

        e = s + 1
        while e < n:
            k = Fraction(e - s)
            xk = keys[e]
            u_pt = (xk, k + eps)
            l_pt = (xk, k - eps)

            # Tangent from l_pt to lower hull uh maximizes slope(U_i, L_k).
            while uh_ptr + 1 < len(uh):
                x0, y0 = uh[uh_ptr]
                x1, y1 = uh[uh_ptr + 1]
                if (l_pt[1] - y1) * (xk - x0) >= (l_pt[1] - y0) * (xk - x1):
                    uh_ptr += 1
                else:
                    break
            cand_min = (l_pt[1] - uh[uh_ptr][1]) / (xk - uh[uh_ptr][0])

            # Tangent from u_pt to upper hull lh minimizes slope(L_i, U_k).
            while lh_ptr + 1 < len(lh):
                x0, y0 = lh[lh_ptr]
                x1, y1 = lh[lh_ptr + 1]
                if (u_pt[1] - y1) * (xk - x0) <= (u_pt[1] - y0) * (xk - x1):
                    lh_ptr += 1
                else:
                    break
            cand_max = (u_pt[1] - lh[lh_ptr][1]) / (xk - lh[lh_ptr][0])

            next_min = cand_min if (s_min is None or cand_min > s_min) else s_min
            next_max = cand_max if (s_max is None or cand_max < s_max) else s_max
            if next_min > next_max:
                break

            s_min = next_min
            s_max = next_max

            # Push u_pt onto lower convex hull uh (strictly increasing edge slopes).
            while len(uh) >= 2:
                x0, y0 = uh[-2]
                x1, y1 = uh[-1]
                if (y1 - y0) * (xk - x0) >= (u_pt[1] - y0) * (x1 - x0):
                    uh.pop()
                else:
                    break
            if uh_ptr >= len(uh):
                uh_ptr = len(uh) - 1
            uh.append(u_pt)

            # Push l_pt onto upper convex hull lh (strictly decreasing edge slopes).
            while len(lh) >= 2:
                x0, y0 = lh[-2]
                x1, y1 = lh[-1]
                if (y1 - y0) * (xk - x0) <= (l_pt[1] - y0) * (x1 - x0):
                    lh.pop()
                else:
                    break
            if lh_ptr >= len(lh):
                lh_ptr = len(lh) - 1
            lh.append(l_pt)

            e += 1

        assert s_min is not None and s_max is not None
        slope = (s_min + s_max) / 2
        b_lo = max(Fraction(idx - s) - eps - slope * keys[idx] for idx in range(s, e))
        b_hi = min(Fraction(idx - s) + eps - slope * keys[idx] for idx in range(s, e))
        assert b_lo <= b_hi
        intercept = (b_lo + b_hi) / 2
        segments.append(Segment(s, e, slope, intercept))
        s = e

    return segments


@dataclass
class RELayer:
    pivots: list[Fraction]
    delta: int
    d_stride: int
    segments: list[Segment]
    left_seg: list[int]
    offsets: list[int]
    boundary_keys: list[Fraction]
    boundary_segs: list[int]


class REPGMIndex:
    """Complete-coverage RE-PGM index with CSR boundary-crossing bucket routing."""

    def __init__(self, keys: list[Fraction], eps: int) -> None:
        assert len(keys) >= 2 and eps >= 2
        self.keys = keys
        self.eps = eps
        self.eps_frac = Fraction(eps)
        self.layers: list[RELayer] = []

        pivots = list(keys)
        delta = 1
        while len(pivots) > 1:
            n_l = len(pivots)
            segs = alg_opt_exact(pivots, self.eps_frac)
            m_next = len(segs)
            d_l = n_l // m_next
            assert d_l >= 1
            n_next = (n_l + d_l - 1) // d_l
            next_pivots = [pivots[j * d_l] for j in range(n_next)]

            # Build CSR header and internal boundary slice per bucket B_{l,j}.
            left_seg: list[int] = []
            offsets: list[int] = [0]
            boundary_keys: list[Fraction] = []
            boundary_segs: list[int] = []

            seg_idx = 0
            for j in range(n_next):
                left_rank = j * d_l
                right_rank = (j + 1) * d_l if j + 1 < n_next else n_l
                while seg_idx + 1 < m_next and segs[seg_idx + 1].start <= left_rank:
                    seg_idx += 1
                left_seg.append(seg_idx)
                m_scan = seg_idx + 1
                while m_scan < m_next and segs[m_scan].start < right_rank:
                    boundary_keys.append(pivots[segs[m_scan].start])
                    boundary_segs.append(m_scan)
                    m_scan += 1
                offsets.append(len(boundary_keys))

            self.layers.append(
                RELayer(
                    pivots=pivots,
                    delta=delta,
                    d_stride=d_l,
                    segments=segs,
                    left_seg=left_seg,
                    offsets=offsets,
                    boundary_keys=boundary_keys,
                    boundary_segs=boundary_segs,
                )
            )
            pivots = next_pivots
            delta *= d_l

    def predecessor(self, q: Fraction) -> int:
        """Return max {i in 0..n-1 : keys[i] <= q}, or -1 if q < keys[0]."""
        if q < self.keys[0]:
            return -1
        j = 0  # Singleton top layer N_H = 1 starts at bucket j = 0.
        for l in range(len(self.layers) - 1, -1, -1):
            layer = self.layers[l]
            b_start = layer.offsets[j]
            b_end = layer.offsets[j + 1]
            if b_start == b_end:
                seg_id = layer.left_seg[j]
            else:
                pos = bisect_right(layer.boundary_keys, q, b_start, b_end)
                seg_id = layer.left_seg[j] if pos == b_start else layer.boundary_segs[pos - 1]

            seg = layer.segments[seg_id]
            pred_local = int(seg.slope * q + seg.intercept)
            pred_rank = seg.start + pred_local

            lo_bucket = j * layer.d_stride
            hi_bucket = min(len(layer.pivots), (j + 1) * layer.d_stride) - 1
            lo = max(seg.start, lo_bucket)
            hi = min(seg.end - 1, hi_bucket)
            clamped = min(max(pred_rank, lo), hi)

            win_lo = max(lo, clamped - self.eps - 1)
            win_hi = min(hi, clamped + self.eps + 1)
            j = bisect_right(layer.pivots, q, win_lo, win_hi + 1) - 1
            assert j >= lo_bucket
        return j


def check_oracle_equivalence(rng: random.Random) -> int:
    """Verify O(n) shrinking-cone segmentation against the O(n^2) rational oracle."""
    checked = 0
    for trial in range(120):
        n = rng.randint(5, 45)
        eps = Fraction(rng.choice([1, 2, 3, 4]))
        keys: list[Fraction] = []
        cur = Fraction(0)
        mode = trial % 3
        for i in range(n):
            if mode == 0:
                step = Fraction(rng.randint(1, 20), rng.randint(1, 5))
            elif mode == 1:
                step = Fraction(1 if i % 7 else 50)
            else:
                step = Fraction((i + 1) * (i + 1))
            cur += step
            keys.append(cur)

        segs = alg_opt_exact(keys, eps)
        s = 0
        for seg in segs:
            assert seg.start == s
            assert prefix_feasible_oracle(keys[s:seg.end], eps)
            if seg.end < n:
                assert not prefix_feasible_oracle(keys[s : seg.end + 1], eps)
            for idx in range(seg.start, seg.end):
                err = abs(Fraction(idx - seg.start) - (seg.slope * keys[idx] + seg.intercept))
                assert err <= eps
            s = seg.end
            checked += 1
        assert s == n
    return checked


def check_routing_and_lemma51(rng: random.Random) -> tuple[int, int]:
    """Verify exact predecessor routing and Lemma 5.1 across diverse key families."""
    instances = 0
    queries = 0
    for eps in (2, 3, 4, 8):
        for n in (17, 64, 129, 300):
            families: list[list[Fraction]] = [
                # Uniform arithmetic progression with jitter
                [Fraction(10 * i + rng.randint(0, 9)) for i in range(n)],
                # Strongly curved convex spacing (quadratic rank-to-key)
                [Fraction(i * i + i) for i in range(n)],
                # Burst / clustered adversarial jumps
                [],
            ]
            cur = Fraction(0)
            for i in range(n):
                cur += Fraction(1 if (i % 11 != 0) else 10_000)
                families[2].append(cur)

            for keys in families:
                idx = REPGMIndex(keys, eps)
                instances += 1

                # Check Lemma 5.1 deterministic invariants at every layer.
                for layer in idx.layers:
                    n_l = len(layer.pivots)
                    m_next = len(layer.segments)
                    total_boundaries = len(layer.boundary_keys)
                    assert total_boundaries <= m_next - 1

                    # Stored-key amortized boundary count in queried bucket.
                    boundary_sum = 0
                    for key in keys:
                        bucket_j = min(
                            (bisect_right(layer.pivots, key) - 1) // layer.d_stride,
                            len(layer.left_seg) - 1,
                        )
                        b_lj = layer.offsets[bucket_j + 1] - layer.offsets[bucket_j]
                        boundary_sum += b_lj

                    avg_b = Fraction(boundary_sum, n)
                    bound_mid = Fraction(layer.d_stride * layer.delta * (m_next - 1), n)
                    bound_rhs = Fraction((n_l - 1) * layer.delta, n)
                    assert avg_b <= bound_mid <= bound_rhs < 1

                # Exhaustively query all stored keys, midpoints, and out-of-range points.
                test_queries = [keys[0] - 5, keys[-1] + 5]
                for i, k in enumerate(keys):
                    test_queries.append(k)
                    if i + 1 < n:
                        test_queries.append((k + keys[i + 1]) / 2)

                for q in test_queries:
                    got = idx.predecessor(q)
                    expected = bisect_right(keys, q) - 1
                    assert got == expected, f"Mismatch at q={q}: got={got}, expected={expected}"
                    queries += 1

    return instances, queries


def main() -> None:
    rng = random.Random(20261124)
    seg_checks = check_oracle_equivalence(rng)
    instances, queries = check_routing_and_lemma51(rng)
    print(f"PASS [O'Rourke vs rational LP oracle]: {seg_checks} segments verified exactly.")
    print(
        f"PASS [RE-PGM CSR routing & Lemma 5.1]: {instances} index hierarchies, "
        f"{queries} exact predecessor queries verified (0 errors)."
    )


if __name__ == "__main__":
    main()
