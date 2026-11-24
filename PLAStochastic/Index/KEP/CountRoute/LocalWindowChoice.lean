import PLAStochastic.Index.KEP.CountRoute.WindowChoice

/-!
# A local Poisson tail suffices for the original additive-height reduction

The nonhomogeneous layer comparison applies above a polynomial scale cutoff.
The window reduction only needs its exponential tail in that same regime. This
module keeps the original height conclusion and original window objects while
removing the unnecessary demand for a tail below the layer-comparison cutoff.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Renyi
open scoped ENNReal unitInterval NNReal Nat

/-- The true Poisson block tail is needed only above a polynomial layer cutoff. -/
def KepPoissonLocalExpTail (Q : ℝ → ℝ) (eps0 R r A c : ℝ) : Prop :=
  ∀ eps, eps0 ≤ eps → ∀ L, 1 ≤ L → ∀ M : ℕ,
    (R * eps ^ r) * kepReferenceSpan eps L < ((M + 1 : ℕ) : ℝ) →
    ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ p : I,
      0 < (p : ℝ) → (p : ℝ) ≤ 1 / 2 → kepReferenceSpan eps L ≤ M * p →
      (poissonWindow M p).real (tailEvent eps Q u L) ≤
        A * Real.exp (-(c * (M * p / kepReferenceSpan eps L)))

theorem kepPoissonTail_of_localExpTail {Q : ℝ → ℝ} {eps0 R r A c : ℝ}
    (heps0 : kepReferenceClassicalThreshold ≤ eps0) (hr : 0 ≤ r)
    (hA : 0 ≤ A) (hc : 0 < c)
    (hT : KepPoissonLocalExpTail Q eps0 R r A c) :
    KepPoissonTail Q eps0 (max 8 R) r (8 * A / c ^ 2 + 4) := by
  intro eps heps L hL M hlt u hu0 hu1
  have hm4 : 4 ≤ kepReferenceSpan eps L := kepReferenceSpan_ge_four (heps0.trans heps) hL
  set m := kepReferenceSpan eps L with hm
  have hm0 : 0 < m := by linarith
  have he2 : 2 ≤ eps := ((le_max_left _ _).trans heps0).trans heps
  have he1 : 1 ≤ eps := by linarith
  have hpow : 1 ≤ eps ^ r := Real.one_le_rpow he1 hr
  have hloc : (R * eps ^ r) * kepReferenceSpan eps L < ((M + 1 : ℕ) : ℝ) := by
    apply lt_of_le_of_lt _ hlt
    gcongr
    exact le_max_right 8 R
  have hmult : 8 * m ≤ (max 8 R * eps ^ r) * m := by
    have hR8 : (8 : ℝ) ≤ max 8 R := le_max_left _ _
    apply mul_le_mul_of_nonneg_right _ hm0.le
    exact hR8.trans (le_mul_of_one_le_right (by linarith) hpow)
  push_cast at hlt
  have hM : 4 * m ≤ M := by linarith
  have hMpos : (0 : ℝ) < M := by linarith
  have hdiv : 0 < m / M := div_pos hm0 hMpos
  set q : ℝ := Real.sqrt (m / M) with hq
  have hq0 : 0 < q := Real.sqrt_pos.2 hdiv
  have hq_sq : q ^ 2 = m / M := Real.sq_sqrt hdiv.le
  have hq_le : q ≤ 1 / 2 := by
    rw [hq, show (1 / 2 : ℝ) = Real.sqrt ((1 / 2) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by rw [div_le_iff₀ hMpos]; linarith)
  have hq1 : q ≤ 1 := hq_le.trans (by norm_num)
  refine ⟨⟨q, hq0.le, hq1⟩, hq0, hq_le, ?_⟩
  set s : ℝ := M * q / m with hs
  have hs_sq : s ^ 2 = M / m := by
    rw [hs, div_pow, mul_pow, hq_sq]
    field_simp
  have hs0 : 0 ≤ s := by positivity
  have hs_pos : 0 < s := by
    rcases hs0.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, zero_pow two_ne_zero] at hs_sq
      exact absurd hs_sq.symm (div_pos hMpos hm0).ne'
  have hmass : m ≤ M * q := by
    have h1 : 1 ≤ s := by
      rw [← Real.sqrt_sq hs0, ← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by rw [hs_sq, le_div_iff₀ hm0]; linarith)
    rw [hs, le_div_iff₀ hm0] at h1
    linarith
  have hτ := hT eps heps L hL M hloc u hu0 hu1 ⟨q, hq0.le, hq1⟩ hq0 hq_le hmass
  simp only at hτ
  have hexp : Real.exp (-(c * s)) ≤ 2 * m / (c ^ 2 * M) := by
    have h1 := Real.quadratic_le_exp_of_nonneg (mul_nonneg hc.le hs0)
    have h2 : (c * s) ^ 2 / 2 ≤ Real.exp (c * s) := by nlinarith [mul_nonneg hc.le hs0]
    have h3 : 0 < (c * s) ^ 2 / 2 := by positivity
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity)]
    calc (2 * m / (c ^ 2 * M))⁻¹ = (c * s) ^ 2 / 2 := by
          rw [mul_pow, hs_sq]
          field_simp
      _ ≤ Real.exp (c * s) := h2
  set τ := (poissonWindow M ⟨q, hq0.le, hq1⟩).real (tailEvent eps Q u L) with hτdef
  have hτ' : τ ≤ A * (2 * m / (c ^ 2 * M)) :=
    hτ.trans (mul_le_mul_of_nonneg_left hexp hA)
  have hτnn : 0 ≤ τ := measureReal_nonneg
  have hsq : (Real.sqrt τ + q) ^ 2 ≤ 2 * τ + 2 * q ^ 2 := by
    have := Real.sq_sqrt hτnn
    nlinarith [sq_nonneg (Real.sqrt τ - q)]
  have hM1 : (M : ℝ) + 1 ≤ 2 * M := by linarith
  have hpos : 0 ≤ (4 * A / c ^ 2 + 2) * m := by positivity
  calc (Real.sqrt τ + q) ^ 2 ≤ 2 * τ + 2 * q ^ 2 := hsq
    _ ≤ 2 * (A * (2 * m / (c ^ 2 * M))) + 2 * (m / M) := by rw [hq_sq]; gcongr
    _ = (4 * A / c ^ 2 + 2) * m / M := by field_simp; ring
    _ ≤ (8 * A / c ^ 2 + 4) * m / ((M + 1 : ℕ) : ℝ) := by
      push_cast
      rw [div_le_div_iff₀ hMpos (by positivity),
        show (8 * A / c ^ 2 + 4) = 2 * (4 * A / c ^ 2 + 2) by ring]
      calc (4 * A / c ^ 2 + 2) * m * (M + 1)
          ≤ (4 * A / c ^ 2 + 2) * m * (2 * M) := mul_le_mul_of_nonneg_left hM1 hpos
        _ = 2 * (4 * A / c ^ 2 + 2) * m * M := by ring

end

end PGM
