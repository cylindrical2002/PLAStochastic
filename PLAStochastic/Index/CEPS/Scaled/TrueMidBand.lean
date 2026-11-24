import PLAStochastic.Index.CEPS.Scaled.TrueTransformBudget

/-! # Explicit fixed-domain mid-band estimate for the actual normal expression

This supplies the analytic norm estimate before the class-independent normal
transform has been chosen and identified. The physical cutoff is fixed before
the scale and frequency, and no Taylor order enters the constants.
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrueNormalExpression_polynomial_frequency_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m) {b δ : ℝ}
    (hb : 0 < b) (hδ : δ ≤ dom.trueDecayScaleBase M / 4) {z : ℂ} (hz : z.re = 0)
    (hbz : b * (1 + Real.sqrt ‖z‖) < dom.trueTransformFrequencyBase M) :
    ‖cepsScaledTrueNormalExpression dom ρW b δ z‖ ≤
      (8 * dom.trueTransformFrequencyConstant M) * (1 + ‖z‖) ^ 3 *
        Real.exp (-dom.entranceBridgeDecayRate * Real.sqrt ‖z‖) := by
  have h := cepsScaledTrueNormalExpression_frequency_budget dom hW hθ hD hf hη hM hm hb hδ hz hbz
  have hs := Real.sqrt_nonneg ‖z‖
  have hs2 := Real.sq_sqrt (norm_nonneg z)
  have hpoly : (1 + Real.sqrt ‖z‖) ^ 5 ≤ 8 * (1 + ‖z‖) ^ 3 := by
    have hbase : (1 + Real.sqrt ‖z‖) ^ 2 ≤ 2 * (1 + ‖z‖) := by nlinarith [sq_nonneg (Real.sqrt ‖z‖ - 1)]
    calc
      _ ≤ (1 + Real.sqrt ‖z‖) ^ 6 := pow_le_pow_right₀ (by linarith) (by norm_num)
      _ = ((1 + Real.sqrt ‖z‖) ^ 2) ^ 3 := by ring
      _ ≤ (2 * (1 + ‖z‖)) ^ 3 := pow_le_pow_left₀ (by positivity) hbase _
      _ = _ := by ring
  exact h.trans ((mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpoly (trueTransformFrequencyConstant_nonneg dom hθ hD M))
      (Real.exp_pos _).le).trans_eq (by ring))

include hW hθ hD in
theorem cepsScaledTrueNormalExpression_mid_band {M : ℝ} (hM0 : 0 ≤ M) {δ : ℝ}
    (hδ : δ ≤ dom.trueDecayScaleBase M / 4) :
    ∃ K c R eps₀ : ℝ, 0 ≤ K ∧ 0 < c ∧ 0 < R ∧ 0 < eps₀ ∧
      ∀ eps : ℝ, eps₀ ≤ eps → ∀ {m : ℕ} {η : ℝ},
        CepsSobolevClass m η fW → 2 * dom.c₀ ≤ η → cepsSobolev m η fW ≤ M → 2 ≤ m →
          ∀ y : ℝ, |y| ≤ R * eps ^ 2 →
            ‖cepsScaledTrueNormalExpression dom ρW ((2 * eps)⁻¹) δ (I * y)‖ ≤
              K * (1 + |y|) ^ 3 * Real.exp (-c * Real.sqrt |y|) := by
  let B := dom.trueTransformFrequencyBase M
  have hB : 0 < B := trueTransformFrequencyBase_pos dom hW hθ hD hM0
  refine ⟨8 * dom.trueTransformFrequencyConstant M, dom.entranceBridgeDecayRate,
    B ^ 2 / 4, max 1 (2 / B), mul_nonneg (by norm_num)
      (trueTransformFrequencyConstant_nonneg dom hθ hD M),
    (entranceBridgePolynomial_constants dom hW hθ hD 0 M).2,
    by positivity, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro eps heps m η hf hη hM hm y hy
  have heps1 : 1 ≤ eps := (le_max_left _ _).trans heps
  have heps0 : 0 < eps := zero_lt_one.trans_le heps1
  have hepsB : 2 / B ≤ eps := (le_max_right _ _).trans heps
  have hbeps : 2 ≤ B * eps := by
    have := (div_le_iff₀ hB).mp hepsB
    nlinarith
  have hyroot : Real.sqrt |y| ≤ B * eps / 2 := by
    have hysq := Real.sq_sqrt (abs_nonneg y)
    have hys := Real.sqrt_nonneg |y|
    nlinarith [mul_pos hB heps0]
  have hsmall : (2 * eps)⁻¹ * (1 + Real.sqrt |y|) < B := by
    rw [inv_mul_lt_iff₀ (mul_pos (by norm_num) heps0)]
    nlinarith
  have hz : (I * (y : ℂ)).re = 0 := by simp
  have hn : ‖I * (y : ℂ)‖ = |y| := by rw [norm_mul, norm_I, one_mul, norm_real, Real.norm_eq_abs]
  have h := cepsScaledTrueNormalExpression_polynomial_frequency_budget dom hW hθ hD hf hη hM hm
    (b := (2 * eps)⁻¹) (δ := δ) (z := I * (y : ℂ))
    (inv_pos.2 (mul_pos (by norm_num) heps0)) hδ hz (by simpa only [hn] using hsmall)
  simpa only [hn] using h

end PGM
