import PLAStochastic.Index.CEPS.Assembly.Output
import PLAStochastic.ForMathlib.Analysis.Asymptotics.ScaledComposition

/-!
# WP11a: the normal-side premises of S-10 and S-11

Scaling of `research/2026-10-02-lean-ceps/blueprint-CS.md` §1.5 and (3.11): `b = 1/w = h/2`,
`h = ε⁻¹`. The scaled normal transform is a function `Gn eps ν z = Ĝ(b, z)`, so that
`Ĝ_w(t) = Gn eps ν (4 ε² t)`. The coefficients of its `b`-expansion are only used on the
imaginary axis, `Gk j p y = Ĝ_j(iy; p)`.

The premises below are the exact forms in which the kernel-specific packages (S-9, C-10, C-11)
are to be supplied; `Glue.T5`, `Glue.T1Low`, `Glue.T1Mid` turn them into `CepsT5`, `CepsT1Low`,
`CepsT1Mid`. Every premise is uniform over `CepsInputClass` with the quantifier order of the
interfaces (`∃ m ∀ D θ vlo vhi η ∃ r > 0 …`).

* `CepsNormalClose`: S-9, `‖E e^{-tS_T} - Ĝ_w(t)‖ ≤ K εᵖ e^{-cε}` for `t = iy`, `|y| ≤ t₀`;
* `CepsNormalTaylor`: the second-order Taylor bound of `Ĝ(b, ·)` at `0` along the imaginary
  axis with derivative `Dn = ∂_z Ĝ(b, 0)` (it contains `Ĝ(b, 0) = 1`);
* `CepsNormalMeanExpansion`: `-∂_z Ĝ(b, 0) = ∑_{k ≤ P} bᵏ C_k(J ν) + O(h^{P+1})` ((F23));
* `CepsNormalLowExpansion`: C-10 on the imaginary axis, `|y| ≤ R ε²` (`b √|z| ≤ ε₁`);
* `CepsNormalCoeffReg`: the coefficients are `C^{N+1}` on the axis with polynomial bounds;
* `CepsNormalMid`: C-11, `‖Ĝ(b, iy)‖ ≤ K (1+|y|)^d e^{-c√|y|}` for `U ≤ |y| ≤ R ε²`.

`cepsLowCoeff` is the composed low-band coefficient `Φ_k(u; p)` of S-11.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

/-- The actual transform `E e^{-t S_T}` of the first segment. -/
def cepsActualTransform (eps : ℝ) (ν : ProbabilityMeasure ℝ) (t : ℂ) : ℂ :=
  ∫ g, Complex.exp (-t * stopSum eps g) ∂(iidLaw ν)

/-- The input class shrinks when the derivative budget grows or the radius decreases. -/
theorem CepsInputClass.mono {D θ vlo vhi η : ℝ} {m m' : ℕ} {r r' : ℝ}
    {ν : ProbabilityMeasure ℝ} (h : CepsInputClass D θ vlo vhi m' η r' ν) (hm : m ≤ m')
    (hr : r' ≤ r) : CepsInputClass D θ vlo vhi m η r ν := by
  obtain ⟨f, hf0, hfc, hν, hs⟩ := h.density
  exact ⟨h.reg, h.reference.mono_order hm,
    ⟨f, hf0, hfc.mono_order hm, hν, (cepsSobolev_mono_order hm _ _).trans (hs.trans hr)⟩⟩

/-- **S-9 (shape).** The actual transform is exponentially close to the normal one on a fixed
segment of the imaginary axis. -/
def CepsNormalClose (Gn : ℝ → ProbabilityMeasure ℝ → ℂ → ℂ) : Prop :=
  ∃ m : ℕ, ∀ D θ vlo vhi η : ℝ, 0 < D → 0 < θ → 0 < vlo → vlo ≤ vhi → 0 < η →
    ∃ r : ℝ, 0 < r ∧ ∃ K c t₀ eps₀ : ℝ, 0 < c ∧ 0 < t₀ ∧ ∃ p : ℕ, ∀ eps : ℝ, eps₀ ≤ eps →
      ∀ ν : ProbabilityMeasure ℝ, CepsInputClass D θ vlo vhi m η r ν →
        ∀ y : ℝ, |y| ≤ t₀ →
          ‖cepsActualTransform eps ν (Complex.I * y) -
              Gn eps ν (Complex.I * ((4 * eps ^ 2 * y : ℝ) : ℂ))‖ ≤
            K * eps ^ p * Real.exp (-c * eps)

/-- The second-order Taylor bound of `Ĝ(b, ·)` at `0` along the imaginary axis, with
derivative `Dn eps ν = ∂_z Ĝ(b, 0)`; at `y = 0` it gives `Ĝ(b, 0) = 1`. -/
def CepsNormalTaylor (Gn : ℝ → ProbabilityMeasure ℝ → ℂ → ℂ)
    (Dn : ℝ → ProbabilityMeasure ℝ → ℂ) : Prop :=
  ∃ m : ℕ, ∀ D θ vlo vhi η : ℝ, 0 < D → 0 < θ → 0 < vlo → vlo ≤ vhi → 0 < η →
    ∃ r : ℝ, 0 < r ∧ ∃ M y₀ eps₀ : ℝ, 0 < y₀ ∧ ∃ q : ℕ, ∀ eps : ℝ, eps₀ ≤ eps →
      ∀ ν : ProbabilityMeasure ℝ, CepsInputClass D θ vlo vhi m η r ν →
        ∀ y : ℝ, |y| ≤ y₀ →
          ‖Gn eps ν (Complex.I * y) - 1 - Complex.I * y * Dn eps ν‖ ≤ M * eps ^ q * y ^ 2

/-- The `b`-expansion of `-∂_z Ĝ(b, 0)` through the jets (C-10 at `z = 0`, (F23)). -/
def CepsNormalMeanExpansion (J : CepsJetData) (Dn : ℝ → ProbabilityMeasure ℝ → ℂ)
    (Cs : ℕ → (ℕ → ℝ) → ℝ) : Prop :=
  ∀ P : ℕ, ∃ m : ℕ, ∀ D θ vlo vhi η : ℝ, 0 < D → 0 < θ → 0 < vlo → vlo ≤ vhi → 0 < η →
    ∃ r : ℝ, 0 < r ∧ ∃ K eps₀ : ℝ, ∀ eps : ℝ, eps₀ ≤ eps →
      ∀ ν : ProbabilityMeasure ℝ, CepsInputClass D θ vlo vhi m η r ν →
        ‖Dn eps ν + ∑ k ∈ Finset.range (P + 1),
            ((((2 * eps)⁻¹) ^ k * Cs k (J.jet ν) : ℝ) : ℂ)‖ ≤ K * (eps⁻¹) ^ (P + 1)

/-- **C-10 on the imaginary axis.** `Ĝ(b, iy) = ∑_{j ≤ N} bʲ Ĝ_j(iy; J ν) + O(h^{N+1} (1+|y|)^d)`
for `|y| ≤ R ε²`. -/
def CepsNormalLowExpansion (J : CepsJetData) (Gn : ℝ → ProbabilityMeasure ℝ → ℂ → ℂ)
    (Gk : ℕ → (ℕ → ℝ) → ℝ → ℂ) : Prop :=
  ∀ N : ℕ, ∃ m : ℕ, ∀ D θ vlo vhi η : ℝ, 0 < D → 0 < θ → 0 < vlo → vlo ≤ vhi → 0 < η →
    ∃ r : ℝ, 0 < r ∧ ∃ K R eps₀ : ℝ, 0 < R ∧ ∃ d : ℕ, ∀ eps : ℝ, eps₀ ≤ eps →
      ∀ ν : ProbabilityMeasure ℝ, CepsInputClass D θ vlo vhi m η r ν →
        ∀ y : ℝ, |y| ≤ R * eps ^ 2 →
          ‖Gn eps ν (Complex.I * y) - ∑ j ∈ Finset.range (N + 1),
              ((((2 * eps)⁻¹) ^ j : ℝ) : ℂ) * Gk j (J.jet ν) y‖ ≤
            K * (eps⁻¹) ^ (N + 1) * (1 + |y|) ^ d

/-- The coefficients `y ↦ Ĝ_j(iy; J ν)` are `C^{N+1}` with polynomially bounded derivatives,
uniformly over the class. -/
def CepsNormalCoeffReg (J : CepsJetData) (Gk : ℕ → (ℕ → ℝ) → ℝ → ℂ) : Prop :=
  ∀ N : ℕ, ∃ m : ℕ, ∀ D θ vlo vhi η : ℝ, 0 < D → 0 < θ → 0 < vlo → vlo ≤ vhi → 0 < η →
    ∃ r : ℝ, 0 < r ∧ ∃ B : ℝ, ∃ d : ℕ,
      ∀ ν : ProbabilityMeasure ℝ, CepsInputClass D θ vlo vhi m η r ν →
        ∀ j ≤ N, ContDiff ℝ (N + 1) (Gk j (J.jet ν)) ∧
          ∀ i ≤ N + 1, ∀ y : ℝ, ‖iteratedDeriv i (Gk j (J.jet ν)) y‖ ≤ B * (1 + |y|) ^ d

/-- **C-11 (mid band).** -/
def CepsNormalMid (Gn : ℝ → ProbabilityMeasure ℝ → ℂ → ℂ) : Prop :=
  ∃ m : ℕ, ∀ D θ vlo vhi η : ℝ, 0 < D → 0 < θ → 0 < vlo → vlo ≤ vhi → 0 < η →
    ∃ r : ℝ, 0 < r ∧ ∃ K c U R eps₀ : ℝ, 0 < c ∧ 0 < R ∧ ∃ d : ℕ, ∀ eps : ℝ, eps₀ ≤ eps →
      ∀ ν : ProbabilityMeasure ℝ, CepsInputClass D θ vlo vhi m η r ν →
        ∀ y : ℝ, U ≤ |y| → |y| ≤ R * eps ^ 2 →
          ‖Gn eps ν (Complex.I * y)‖ ≤ K * (1 + |y|) ^ d * Real.exp (-c * Real.sqrt |y|)

/-- The composed low-band coefficient `Φ_k(u; p)` of S-11: the `k`-th `h`-coefficient of
`∑_j (h/2)ʲ Ĝ_j(i(-4u)/s; p)` with `s = ∑ hᵏ c_k(p)`, Taylor-expanded at `y₀ = -4u/c₀(p)`. -/
def cepsLowCoeff (Gk : ℕ → (ℕ → ℝ) → ℝ → ℂ) (sc : ℕ → (ℕ → ℝ) → ℝ) (k : ℕ) (u : ℝ)
    (p : ℕ → ℝ) : ℂ :=
  lowCompCoeff (fun j y => (2⁻¹ : ℂ) ^ j * Gk j p y) (fun i => sc i p) (-4 * u) k

/-! ## Exponentially small terms -/

/-- `εᵖ e^{-cε} ≤ K ε^{-n}` for `ε ≥ 1`. -/
theorem exists_pow_mul_exp_neg_le (p n : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ eps : ℝ, 1 ≤ eps → eps ^ p * Real.exp (-c * eps) ≤ K * (eps⁻¹) ^ n := by
  refine ⟨((p + n).factorial : ℝ) / c ^ (p + n), by positivity, fun eps heps => ?_⟩
  have he0 : 0 < eps := lt_of_lt_of_le one_pos heps
  have h1 := Real.pow_div_factorial_le_exp (c * eps) (mul_nonneg hc.le he0.le) (p + n)
  have hf : (0 : ℝ) < ((p + n).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hexp : Real.exp (-c * eps) = (Real.exp (c * eps))⁻¹ := by
    rw [← Real.exp_neg]; ring_nf
  rw [hexp, inv_pow, ← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _)
    (pow_pos he0 n)]
  rw [div_le_iff₀ hf, mul_pow] at h1
  calc eps ^ p * eps ^ n = eps ^ (p + n) := (pow_add _ _ _).symm
    _ ≤ (p + n).factorial / c ^ (p + n) * Real.exp (c * eps) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        nlinarith [h1]

end

end PGM
