#!/usr/bin/env python3
"""Finite-parameter height recurrence check (re_check.py) for Section 5.3 / Table 3.

Evaluates how accurately the finite-step squaring (Model G RE), two-phase (Model K RE),
and stationary fanout + curvature (Model K EP) recurrences initialized from measured
base stride d_0 = floor(n / M_1) and top-layer median threshold Theta = 3.2 predict
the exact empirical integer hierarchy height H across:
  - n in {10^5, 10^6} (--quick, default) or {10^5, 10^6, 10^7, 10^8} (--full)
  - eps in {2, 4, 8, 16, 32, 64, 128}
"""

from __future__ import annotations

import argparse
import math
from pathlib import Path
import subprocess

KAPPA_OPT = 3.5371705652521226
ALPHA_OPT = 0.1780964691224734
RHO_STAR = 0.25710
THETA_TOP = 3.2  # Median normalized Brownian lifetime threshold for single-segment termination

HERE = Path(__file__).resolve().parent
POPDYN_BIN = HERE / "popdyn"
POPDYN_SRC = HERE / "popdyn.cpp"


def ensure_popdyn() -> Path:
    if not POPDYN_BIN.is_file():
        subprocess.run(
            ["g++", "-O3", "-std=c++17", str(POPDYN_SRC), "-o", str(POPDYN_BIN)],
            check=True,
        )
    return POPDYN_BIN


def predict_gre(n: int, eps: int, m1: int, v0: float, theta: float = THETA_TOP) -> int:
    """Finite-step Model G (RE) squaring recurrence initialized from d_0 = floor(n / M_1)."""
    if m1 <= 1:
        return 1
    d0 = n // m1
    n_l = (n + d0 - 1) // d0
    delta_l = d0
    h = 1
    a_scale = theta * eps * eps / v0
    while n_l > 1:
        if n_l <= 2 * eps + 1:
            return h + 1
        m_hat = n_l / (a_scale * delta_l)
        if m_hat < 1.0:
            return h + 1
        m_next = max(2, int(round(m_hat)))
        d_l = max(1, n_l // m_next)
        n_l = (n_l + d_l - 1) // d_l
        delta_l *= d_l
        h += 1
    return h


def predict_kre(n: int, eps: int, m1: int, delta: float = 0.8, theta: float = THETA_TOP) -> int:
    """Finite-step Model K (RE) two-phase recurrence initialized from d_0 = floor(n / M_1)."""
    if m1 <= 1:
        return 1
    d0 = n // m1
    n_l = (n + d0 - 1) // d0
    h = 1
    while n_l > 1:
        if n_l <= 2 * eps + 1:
            return h + 1
        m_noise = (n_l * n_l) / (theta * eps * eps * n)
        span = (n_l - 1) / (n_l + 1)
        m_curv = span * math.sqrt(delta * (n_l - 1) / (8.0 * eps))
        m_hat = math.hypot(m_noise, m_curv)
        if m_hat < 1.0:
            return h + 1
        m_next = max(2, int(round(m_hat)))
        d_l = max(1, n_l // m_next)
        n_l = (n_l + d_l - 1) // d_l
        h += 1
    return h


def predict_kep(eps: int, m1: int, delta: float = 0.8) -> int:
    """Finite-step Model K (EP) recurrence initialized from M_1."""
    if m1 <= 1:
        return 1
    n_l = m1
    h = 1
    c_eps = (KAPPA_OPT / ALPHA_OPT) * (eps + RHO_STAR) ** 2
    while n_l > 1:
        if n_l <= 2 * eps + 1:
            return h + 1
        m_noise = n_l / c_eps
        span = (n_l - 1) / (n_l + 1)
        m_curv = span * math.sqrt(delta * (n_l - 1) / (8.0 * eps))
        m_hat = math.hypot(m_noise, m_curv)
        if m_hat < 1.0:
            return h + 1
        n_l = max(2, int(round(m_hat)))
        h += 1
    return h


def evaluate_grid(full: bool) -> None:
    bin_path = ensure_popdyn()
    n_values = [10**5, 10**6, 10**7, 10**8] if full else [10**5, 10**6]
    eps_values = [2, 4, 8, 16, 32, 64, 128]

    regimes = [
        ("Model G (RE)", [("exp", "RE", 1.0), ("unif", "RE", 1.0 / 3.0)]),
        ("Model K (RE)", [("linear08", "RE", 0.0)]),
        ("Model K (EP)", [("linear08", "EP", 0.0)]),
    ]

    print(f"{'Regime':<16} {'Runs':>6} {'Exact Match':>18} {'Max Error':>11}")
    print("-" * 55)
    for label, specs in regimes:
        total = 0
        exact = 0
        max_err = 0
        mismatches: list[str] = []
        for fam, mode, v0 in specs:
            for n in n_values:
                trials = (5 if n <= 10**7 else 1) if full else 3
                for eps in eps_values:
                    for trial in range(1, trials + 1):
                        seed = 1000 * trial + eps
                        out = subprocess.check_output(
                            [str(bin_path), "eval-run", mode, fam, str(n), str(eps), str(seed)],
                            text=True,
                        ).strip()
                        h_emp, m1, n_penult = map(int, out.split())
                        if fam in ("exp", "unif"):
                            h_pred = predict_gre(n, eps, m1, v0)
                        elif mode == "RE":
                            h_pred = predict_kre(n, eps, m1)
                        else:
                            h_pred = predict_kep(eps, m1)

                        err = abs(h_pred - h_emp)
                        total += 1
                        exact += int(err == 0)
                        max_err = max(max_err, err)
                        if err != 0:
                            mismatches.append(
                                f"{fam} {mode} n={n} eps={eps}: emp={h_emp}, pred={h_pred} (N_{{H-1}}={n_penult})"
                            )
        pct = 100.0 * exact / total
        match_str = f"{exact}/{total} ({pct:5.1f}%)"
        print(f"{label:<16} {total:>6} {match_str:>18} {max_err:>9} layers")
        for m in mismatches:
            print(f"  [boundary] {m}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--quick", action="store_true", help="Fast grid n in {10^5, 10^6} (default)")
    group.add_argument("--full", action="store_true", help="Full paper grid n in {10^5..10^8}")
    args = parser.parse_args()
    evaluate_grid(full=args.full)


if __name__ == "__main__":
    main()
