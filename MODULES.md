# Module Architecture & Layering (`PLAStochastic`)

`PLAStochastic` is organized as a single Lake package defining one unified Lean 4 library (`PLAStochastic`) across **2,682 local `.lean` modules**, pinned to `leanprover/lean4:v4.33.1` and Mathlib4 commit `0df444a360eaa60ab8c11dca51a86af692955474`.

```text
PLAStochastic/
├── PLAStochastic.lean          # Root entry importing all 8 public Results facades
├── PLAStochastic/
│   ├── Results/        (8)     # Public theorem facades (B-MOM, S-SCALE, S-BRACKET, P-GRE, P-KRE, P-GEP, P-KEP, P-CEPS)
│   ├── ForMathlib/   (360)     # General mathematics (Analysis, MeasureTheory, NumberTheory, Probability, Topology)
│   ├── Brownian/      (45)     # Standard Brownian motion: Construction, Markov, PathLaw, Hitting, Killed kernels
│   ├── Affine/       (196)     # Affine approximation errors, lifetimes, Mellin/spectral zeta moments
│   ├── Swing/        (368)     # Native Swing filter: entrance law, slope Markov kernel, parity brackets
│   └── Index/       (1704)     # PGM / PLA hierarchies: ALG-OPT, EP & RE height theorems, CEPS expansion
├── scripts/
│   ├── check_structure.py      # Acyclicity, subject-layering, forbidden-token, and SHA-256 provenance checker
│   ├── theorem_inventory.py    # Public declaration resolver and premise-free P-CEPS signature check
│   ├── verify_package.py       # Full Lake build + Lean.collectAxioms audit across all compiled declarations
│   └── lean-locked.sh          # Shared flock wrapper for concurrent-safe Lake invocations
├── reproduce/                  # C++17 & Python 3 empirical segmentation and CSR bucket-routing reproduction scripts
├── migration.json              # Per-module SHA-256 provenance and import graph manifest
├── verification.json           # Package verification specification
└── lean-toolchain · lakefile.toml · lake-manifest.json · setup.sh · verify.py
```

## Subject-Area Layering Rules

[`scripts/check_structure.py`](scripts/check_structure.py) strictly enforces a DAG of allowed cross-area imports:

| Area | Allowed Local Imports | Core Contents |
|---|---|---|
| `ForMathlib` | `ForMathlib` | Mellin transforms, analytic continuation at $\Gamma$ poles, quadratic spectral zeta & $\zeta'(-2k)$, Kesten–Rogozin anti-concentration, Rényi order statistics, Doeblin/Wasserstein Markov contraction, Sparre Andersen fluctuation, Wald identities |
| `Brownian` | `ForMathlib`, `Brownian` | Projective Brownian construction, strong Markov property, hitting laws, killed heat kernels |
| `Affine` | `ForMathlib`, `Brownian`, `Affine` | Shrinking-cone / Chebyshev affine error functionals, exit lifetimes $\tau_{\mathrm{an}}, \tau_{\mathrm{opt}}$, survival image series, all-orders moment recurrences |
| `Swing` | `ForMathlib`, `Brownian`, `Affine`, `Swing` | Constrained-SSE Swing stream, first-restart entrance law $\rho$, slope chain $\mathsf{T}$, renewal potential, parity brackets |
| `Index` | `ForMathlib`, `Brownian`, `Affine`, `Index` | `ALG-OPT` greedy segmentation, `Model G` & `Model K`, `GRE` / `KRE` doubly logarithmic & two-phase heights, `GEP` / `KEP` exact-denominator additive bounds, `CEPS` all-orders expansion |
| `Results` | All areas | Eight concise facade modules re-exporting the paper's main theorems |

Note that `Swing` and `Index` are mutually independent: neither imports the other, while both build on `ForMathlib`, `Brownian`, and `Affine`. Furthermore, no module file (`Foo.lean`) is permitted to coexist with a same-named directory (`Foo/`), and `check_structure.py` scans all `.lean` sources outside comments/strings to forbid `sorry`, `admit`, `axiom`, and `sorryAx` before compilation even begins.
