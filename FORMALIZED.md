# Formalized Statements & Quantifiers (`PLAStochastic`)

This document records the exact mathematical models, hypotheses, quantifier orders, and Lean 4 declarations for the eight public result modules in `PLAStochastic.Results`. Every compiled declaration in the transitive closure is audited by `verify.py` (`Lean.collectAxioms`) to depend solely on Lean 4's three standard logical axioms (`propext`, `Classical.choice`, `Quot.sound`), with zero `sorry`s or custom axioms.

## Overview

| Package | Formalized Scope | Primary Declarations | Public Module |
|---|---|---|---|
| `B-MOM` | All integer moments $q \ge 1$ of $\tau_{\mathrm{an}}$ and $\tau_{\mathrm{opt}}$ via polynomial recurrences and odd-$\zeta$ readouts; variance and fourth central moment of $\tau_{\mathrm{opt}}$ | `anchoredUnitLifetime_moment_eq_coeff_readout`, `optimalUnitLifetime_moment_eq`, `optimalUnitLifetime_variance_eq_constant` | [`PLAStochastic/Results/BrownianMoments.lean`](PLAStochastic/Results/BrownianMoments.lean) |
| `S-SCALE` | Second-segment $\Theta(E)$ bounds and $\mathbb{E}L_{2,E}/E \to \kappa_2$; limiting entrance law $\rho$; subsequent-segment $\mathbb{E}L_{k,E}/(E\log E) \to c_k$ and geometric limsup bound; stationary constant $\gamma$ | `swing_transient_coefficients`, `nativeTransientMarginProb_tendsto_entranceLaw`, `theorem_4_4_swing_gaussian` | [`PLAStochastic/Results/SwingScale.lean`](PLAStochastic/Results/SwingScale.lean) |
| `S-BRACKET` | Alternating parity brackets $c_4 \le c_6 \le \cdots \le \gamma \le \cdots \le c_5 \le c_3$ and Wasserstein-$1$ rate $(3/4)^{k-3}$ | `swing_transient_brackets`, `slopeStationaryLaw_invariant` | [`PLAStochastic/Results/SwingConstant.lean`](PLAStochastic/Results/SwingConstant.lean) |
| `P-GRE` | Model G RE height window, exact integer $\lceil y \rceil$ outside rounding windows, integral form, and limit form | `G_RE_exact`, `G_RE_exact_integral`, `G_RE_exact_limit` | [`PLAStochastic/Results/GRE.lean`](PLAStochastic/Results/GRE.lean) |
| `P-KRE` | Model K RE uniform two-phase law over $\mathfrak{F}_\delta$; fixed non-constant density exact integer $h_K(z_N)$ in probability and expectation | `K_RE_uniform`, `K_RE_uniform_integral`, `K_RE_exact`, `K_RE_exact_probability`, `K_RE_exact_integral` | [`PLAStochastic/Results/KRE.lean`](PLAStochastic/Results/KRE.lean) |
| `P-GEP` | Model G EP unconditional all-$n \ge 2$ additive $O(1)$ height bound with exact denominator $\log C_\varepsilon$ | `H_G_EP_additive`, `H_G_EP_additive_law`, `sum_abs_log_segMean_sub_le` | [`PLAStochastic/Results/GEP.lean`](PLAStochastic/Results/GEP.lean) |
| `P-KEP` | General Model K EP unconditional all-$N \ge 2$ additive $O_f(1)$ height bound with the same $\log C_\varepsilon$ | `H_K_EP_additive`, `H_K_EP_additive_law`, `H_K_EP` | [`PLAStochastic/Results/KEP.lean`](PLAStochastic/Results/KEP.lean) |
| `P-CEPS` | Unique all-orders asymptotic expansion of $C_\varepsilon / \varepsilon^2$ with $a_0 = \kappa_{\mathrm{opt}} / \alpha_{\mathrm{opt}}$ | `gepC_asymptoticExpansion` | [`PLAStochastic/Results/CEPS.lean`](PLAStochastic/Results/CEPS.lean) |

## Reading Conventions

- **Expectations**: Real-valued Bochner integrals (`∫ ω, ... ∂P`). Stopping times and segment counts take values in $[0, \infty]$ or $\mathbb{N} \cup \{\infty\}$; finiteness a.s. and $L^p$ integrability are proved as companion lemmas so that all stated expectations are genuine finite integrals.
- **Logarithms and Zeta**: `Real.log` denotes the natural logarithm; $\zeta(s)$ is `(riemannZeta s).re`.
- **Joint scaling (`HEIGHT`)**: Quantifies over all sequences $n_k \to \infty$ in $\mathbb{N}$ and $\varepsilon_k \to \infty$ in $\mathbb{R}$ satisfying $\log \varepsilon_k / \log n_k \to 0$. Constants quantified *before* the `HEIGHT` sequence are uniform across all admissible scaling trajectories.
- **Sample-space independence**: Law-level theorems (`H_G_EP_additive_law`, `H_K_EP_additive_law`, `K_RE_uniform_integral`, `K_RE_exact_probability`, `K_RE_exact_integral`) choose their constants $(\varepsilon_0, K)$ solely from the gap distribution $\nu_0$ or density $f$, uniformly over every measurable space $\Omega$, probability measure $P$, and i.i.d. realization (`iIndepFun` + `HasLaw`).
- **Hierarchy height**: Defined as `sInf {ℓ | 1 ≤ ℓ ∧ N_ℓ = 1}`.

---

## 1. `B-MOM`: Moments of Brownian Affine Lifetimes

Namespace: `BrownianAffine`. Sole hypothesis: Mathlib's `IsBrownianReal B μ` on $(\Omega, \mu)$.

- `anchoredUnitLifetime B` and `optimalUnitLifetime B` ([`PLAStochastic/Affine/Lifetime/UnitMoments.lean`](PLAStochastic/Affine/Lifetime/UnitMoments.lean)) represent the first exit times $\tau_{\mathrm{an}}$ and $\tau_{\mathrm{opt}}$ of the uniform approximation distances in $C([0, t])$ to $\operatorname{span}\{s\}$ and $\operatorname{span}\{s, 1\}$, respectively.
- **Anchored all-orders readout** (`anchoredUnitLifetime_moment_eq_coeff_readout`, [`PLAStochastic/Affine/Moments/Anchored/Recurrence.lean`](PLAStochastic/Affine/Moments/Anchored/Recurrence.lean)): via `anchoredRecurrencePoly` ($V_0=1, V_1=3X, V_{q+2}=2XV_{q+1}-(X^2+4X)V_q$),
  $$\mathbb{E}[\tau_{\mathrm{an}}^q] = \frac{1}{2^q (q-1)!}\sum_{j=1}^q [X^j]V_q \,(2j)!\,(2^{2j+1}-1)\frac{\zeta(2j+1)}{\pi^{2j}} \qquad (q \ge 1).$$
- **Optimal all-orders readout** (`optimalUnitLifetime_moment_eq`, [`PLAStochastic/Affine/Moments/Optimal/AllOrders/Moments.lean`](PLAStochastic/Affine/Moments/Optimal/AllOrders/Moments.lean)): via `optimalSpectralPoly` ($U_0=1, U_1=X, U_{n+2}=2XU_{n+1}-(X^2-X)U_n$), `optimalZetaWeight`, and `optimalMomentReadout`, proves $\mathbb{E}[\tau_{\mathrm{opt}}] = \frac{40\zeta(3)}{\pi^2} - \frac{4}{3}$ and the exact closed-form odd-$\zeta$ readout for every integer $q \ge 2$.
- **First four moments and strict positivity of variance** ([`PLAStochastic/Affine/Moments/Optimal/FirstFourMoments.lean`](PLAStochastic/Affine/Moments/Optimal/FirstFourMoments.lean)): `optimalUnitLifetime_variance_eq_constant` and `optimalVarianceConstant_pos` certify $\operatorname{Var}(\tau_{\mathrm{opt}}) = m_2 - m_1^2 > 0$.

---

## 2. `S-SCALE` & `S-BRACKET`: Native Swing Asymptotics

Namespace: `SwingRepair`. Sole hypothesis: $X_0, X_1, \dots$ are i.i.d. $\mathcal{N}(0, 1)$ variables on $(\Omega, \mu)$.

- `nativeStream` ([`PLAStochastic/Swing/Algorithm/Stream.lean`](PLAStochastic/Swing/Algorithm/Stream.lean)) formalizes the exact constrained-SSE Swing filter with recording anchor and rejected-sample carry, without `max_lag`.
- `LeadingCoefficient.theorem_4_3_swing_gaussian`: proves uniqueness of the invariant margin measure $\nu$ of $\mathsf{K} = \mathsf{A}\mathsf{B}$ and convergence of the stationary mean segment length $C_E / (E \log E) \to \gamma = 4\int_{(0,\infty)} V\,d\nu > 0$.
- `nativeTransientMarginProb_tendsto_entranceLaw`: weak convergence of the first restart margin $R_{1,E} = E - |x_1|$ to the explicit entrance law $\rho$ as $E \to \infty$.
- `swing_transient_coefficients` and `swing_transient_brackets` ([`PLAStochastic/Swing/Transient/Coefficients/Exact.lean`](PLAStochastic/Swing/Transient/Coefficients/Exact.lean)): prove $\mathbb{E}[L_{2,E}]/E \to \kappa_2 > 0$, $\mathbb{E}[L_{k,E}]/(E\log E) \to c_k = \alpha_2 \mathsf{T}^{k-3} h > 0$ for every fixed $k \ge 3$, the monotone odd/even parity brackets around $\gamma$, and the explicit contraction $|c_k - \gamma| \le L_h W_1(\alpha_2, \lambda) (3/4)^{k-3}$.

---

## 3. `P-GRE`, `P-KRE`, `P-GEP`, `P-KEP`, & `P-CEPS`: Learned Index Hierarchies

Namespace: `PGM`.

- **Algorithms**: `prefixAffineFeasible` ([`PLAStochastic/Index/Algorithm/AffineFeasible.lean`](PLAStochastic/Index/Algorithm/AffineFeasible.lean)) defines exact $\pm\varepsilon$ rank-prediction feasibility; `ALG-OPT` ([`Segmentation.lean`](PLAStochastic/Index/Algorithm/Segmentation.lean)) repeatedly takes the longest feasible prefix; `epHeight` ([`EndpointHierarchy.lean`](PLAStochastic/Index/Algorithm/EndpointHierarchy.lean)) and `reHeight` ([`RankHierarchy.lean`](PLAStochastic/Index/Algorithm/RankHierarchy.lean)) define the Endpoint Promotion and complete-coverage Rank-Equispaced Promotion hierarchies ($d_\ell = \lfloor N_\ell / M_{\ell+1} \rfloor$, $N_{\ell+1} = \lceil N_\ell / d_\ell \rceil$).
- **Stochastic Models**:
  - `GapLaw P g μ₀ σ₀ κ₀` ([`GapLaw.lean`](PLAStochastic/Index/Model/GapLaw.lean)): i.i.d. gaps in $L^3$ with mean $\mu_0 > 0$, variance $\sigma_0^2 > 0$, and third central absolute moment $\le \kappa_0$ (plus $g_0 > 0$ a.s. for `P-GEP`).
  - `DensityK f A B f₋ f₊ L_f` ([`ModelK/Density.lean`](PLAStochastic/Index/ModelK/Density.lean)): density $f$ on $[A, B]$ with $0 < f_- \le f \le f_+$, Lipschitz constant $L_f$, and $\int_A^B f = 1$; keys `kKeys X N` are the sorted order statistics of $N$ i.i.d. draws.
- **`P-GRE`** ([`PLAStochastic/Index/GRE/Exact/Main.lean`](PLAStochastic/Index/GRE/Exact/Main.lean)): `G_RE_exact`, `G_RE_exact_integral`, and `G_RE_exact_limit`.
- **`P-KRE`** ([`PLAStochastic/Index/KRE/Uniform/Main.lean`](PLAStochastic/Index/KRE/Uniform/Main.lean), [`PLAStochastic/Index/KRE/Exact/Integral.lean`](PLAStochastic/Index/KRE/Exact/Integral.lean)): `K_RE_uniform`, `K_RE_uniform_integral`, `K_RE_exact`, `K_RE_exact_probability`, and `K_RE_exact_integral`.
- **`P-GEP`** ([`PLAStochastic/Index/GEP/Additive/LawForm.lean`](PLAStochastic/Index/GEP/Additive/LawForm.lean)): `H_G_EP_additive_law`, `H_G_EP_additive`, `sum_abs_log_segMean_sub_le`, and `tendsto_log_lawC_expPM_orbit` (proving convergence of the exact stationary compression limit `gepC ε`).
- **`P-KEP`** ([`PLAStochastic/Index/KEP/Additive/LawForm.lean`](PLAStochastic/Index/KEP/Additive/LawForm.lean)): `H_K_EP_additive_law` and `H_K_EP_additive` (all-$N \ge 2$ unconditional additive $O_f(1)$ bound under general `DensityK` with the identical denominator `gepC ε`).
- **`P-CEPS`** ([`PLAStochastic/Index/CEPS/Final/Unconditional.lean`](PLAStochastic/Index/CEPS/Final/Unconditional.lean)): `gepC_asymptoticExpansion` (unconditional existence and uniqueness of the all-orders asymptotic coefficient sequence $(a_j)_{j \ge 0}$ for `gepC ε / ε^2`, with $a_0 = \kappa_{\mathrm{opt}} / \alpha_{\mathrm{opt}}$, verified against a premise-free signature check in `scripts/theorem_inventory.py`).
