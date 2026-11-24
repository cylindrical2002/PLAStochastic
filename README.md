# PLAStochastic: Formalization & Reproducibility Artifacts for *The Anatomy of Piecewise-Linear Learned Indexes*

This repository contains the Lean 4 formalization library **`PLAStochastic`** (2,682 modules) and the C++17 / Python 3 numerical and routing reproduction suite accompanying the paper:

> **The Anatomy of Piecewise-Linear Learned Indexes**

Every formalized public theorem in `PLAStochastic` builds with **zero `sorry` placeholders** and depends exclusively on Lean 4's three standard logical axioms (`propext`, `Classical.choice`, `Quot.sound`).

---

## 1. Mapping Between Paper Results and Lean 4 Packages

To import all formalized theorems at once:

```lean
import PLAStochastic
```

Or import individual result facades under `PLAStochastic.Results`:

| Package | Paper Result | Public Module | Primary Formalized Declarations |
|---|---|---|---|
| `B-MOM` | Theorem 3.1 ($\kappa_{\mathrm{opt}}, \alpha_{\mathrm{opt}}$, all integer moments) | [`PLAStochastic.Results.BrownianMoments`](PLAStochastic/Results/BrownianMoments.lean) | `BrownianAffine.optimalUnitLifetime_moment_eq`, `BrownianAffine.anchoredUnitLifetime_moment_eq_coeff_readout`, `BrownianAffine.optimalUnitLifetime_variance_eq_constant` |
| `S-SCALE` | Theorem 3.3(1) (Swing $\kappa_2 E$ and $c_k E \log E$ laws) | [`PLAStochastic.Results.SwingScale`](PLAStochastic/Results/SwingScale.lean) | `SwingRepair.swing_transient_coefficients`, `SwingRepair.nativeTransientMarginProb_tendsto_entranceLaw`, `SwingRepair.theorem_4_4_swing_gaussian` |
| `S-BRACKET` | Theorem 3.3(2) (Alternating parity brackets & $(3/4)^{k-3}$ rate) | [`PLAStochastic.Results.SwingConstant`](PLAStochastic/Results/SwingConstant.lean) | `SwingRepair.swing_transient_brackets`, `SwingRepair.slopeStationaryLaw_invariant` |
| `P-GEP` | Theorem 4.1 (Model G Endpoint Promotion additive $O(1)$ height) | [`PLAStochastic.Results.GEP`](PLAStochastic/Results/GEP.lean) | `PGM.H_G_EP_additive_law`, `PGM.H_G_EP_additive`, `PGM.sum_abs_log_segMean_sub_le` |
| `P-KEP` | Theorem 4.1 (Model K Endpoint Promotion additive $O_f(1)$ height) | [`PLAStochastic.Results.KEP`](PLAStochastic/Results/KEP.lean) | `PGM.H_K_EP_additive_law`, `PGM.H_K_EP_additive`, `PGM.H_K_EP` |
| `P-CEPS` | Theorem 4.2 (All-orders asymptotic expansion of $C_\varepsilon / \varepsilon^2$) | [`PLAStochastic.Results.CEPS`](PLAStochastic/Results/CEPS.lean) | `PGM.gepC_asymptoticExpansion` |
| `P-GRE` | Theorem 4.3 (Model G Rank-Equispaced Promotion height & exact $\lceil y_n \rceil$) | [`PLAStochastic.Results.GRE`](PLAStochastic/Results/GRE.lean) | `PGM.G_RE_exact`, `PGM.G_RE_exact_integral`, `PGM.G_RE_exact_limit` |
| `P-KRE` | Theorem 4.4 (Uniform two-phase $\Phi(n,\varepsilon,\delta)$ over $\mathfrak{F}_\delta$ & exact $h_K(z_n)$) | [`PLAStochastic.Results.KRE`](PLAStochastic/Results/KRE.lean) | `PGM.K_RE_uniform_integral`, `PGM.K_RE_exact_integral`, `PGM.K_RE_exact_probability` |

Detailed mathematical statements, hypotheses, and quantifier orders are documented in [`THEOREMS.md`](THEOREMS.md) and [`FORMALIZED.md`](FORMALIZED.md). Library layering rules are documented in [`MODULES.md`](MODULES.md).

---

## 2. Building & Auditing the Lean 4 Formalization

### Prerequisites
- [`elan`](https://github.com/leanprover/elan) (automatically selects the pinned toolchain `leanprover/lean4:v4.33.1` from [`lean-toolchain`](lean-toolchain)).
- Python 3.9+ (for structure, signature, and axiom audit scripts).

### Step-by-Step Verification

1. **Fast source-graph, layering, and `sorry`-free structural check** (runs in `< 5` seconds without building):
   ```bash
   python3 scripts/check_structure.py
   ```

2. **Fetch precompiled Mathlib4 cache and build `PLAStochastic`**:
   ```bash
   bash setup.sh
   # Equivalent manual build once Mathlib cache is present:
   lake build PLAStochastic
   ```
   *(Do **not** run `lake update`; [`lake-manifest.json`](lake-manifest.json) pins the exact Mathlib4 revision `0df444a360eaa60ab8c11dca51a86af692955474`.)*

3. **Full end-to-end build, public signature check, and transitive `collectAxioms` audit**:
   ```bash
   LEAN_NUM_THREADS=2 bash scripts/lean-locked.sh python3 verify.py --output /tmp/pla-lean-audit
   ```
   This builds the entire library with `-DwarningAsError=true`, checks all public declarations in [`scripts/theorem_inventory.py`](scripts/theorem_inventory.py), and verifies via `Lean.collectAxioms` that every compiled declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`.

---

## 3. Reproducing the Routing & Numerical Evaluation (`reproduce/`)

The [`reproduce/`](reproduce/) directory provides standalone C++17 and Python 3 implementations of exact O'Rourke shrinking-cone segmentation (`ALG-OPT`), one-pass streaming fitters (`Anchored`, `ShrinkingCone`, `GreedySplineCorridor`, `Native Swing`), Endpoint Promotion (`EP`), Rank-Equispaced Promotion (`RE`), Compressed Sparse Row (CSR) boundary-crossing bucket routing (Section 5.1, Lemma 5.1 & Theorem 5.2), population-dynamics fanout/variance tracking (Figures 3 & 5), two-phase curvature scans (Figures 4 & 5), finite-parameter height prediction recurrences (Table 4), and 200M-key SOSD real-world benchmarks (Table 5):

```bash
# 1. Exact rational verification of CSR bucket routing and Lemma 5.1 (< 5s, pure Python 3)
python3 reproduce/verify_routing.py

# 2. Compile the O(n) C++17 segmentation & population-dynamics engine
g++ -O3 -std=c++17 reproduce/popdyn.cpp -o reproduce/popdyn

# 3. Finite-step height recurrence accuracy check (re_check.py)
python3 reproduce/re_check.py --quick   # Fast grid up to n = 10^6 (~5s)
python3 reproduce/re_check.py --full    # Full paper grid up to n = 10^8 (Table 4)

# 4. Multi-layer variance collapse, finite-eps fanout, and curvature scan
./reproduce/popdyn variance             # Reproduces Figure 3(b) relative variance trajectories
./reproduce/popdyn fanout               # Reproduces Figure 5(a) stationary EP ratio vs (1 + rho_*/eps)^2
./reproduce/popdyn trajectory           # Reproduces Figure 5(b) n = 10^8 layer contraction
./reproduce/popdyn delta-scan           # Reproduces Figures 4(b) & 5(c) curvature phase transition

# 5. Single-layer fitter spectrum & 200M-key SOSD real-world benchmark suite (Table 5)
g++ -O3 -march=native -std=c++17 reproduce/sosd_bench.cpp -o reproduce/sosd_bench
./reproduce/sosd_bench synthetic-fitters   # Optimal, Anchored, ShrinkingCone, RadixSpline, Native Swing
./reproduce/sosd_bench swing-gaussian      # Gaussian-walk three-regime & alternating Swing brackets
python3 reproduce/download_sosd.py         # Downloads & MD5-verifies books, fb, osm, wiki (200M uint64)
./reproduce/sosd_bench sosd                # Full EP-PGM vs RE-PGM vs Flat Bins & fitters on SOSD 200M
```

Reference CSV tables corresponding to the paper's figures and SOSD / fitter evaluations are included under [`reproduce/data/`](reproduce/data/).

---

## License

Released under the [Apache License 2.0](LICENSE).
