import PLAStochastic.Index.CEPS.Scaled.NormalSeries

/-! # Full low-frequency bands for the fixed-domain actual normal expansion -/

noncomputable section
open Complex Set Metric MeasureTheory Finset PowerSeries
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrueNormalExpression_low_band (N : ℕ) {M δ : ℝ} (hM0 : 0 ≤ M)
    (hδ : 0 < δ) (hδactual : δ ≤ dom.trueDecayScaleBase M / 4) :
    ∃ K R eps₀ : ℝ, 0 ≤ K ∧ 0 < R ∧ 1 ≤ eps₀ ∧
      ∀ eps : ℝ, eps₀ ≤ eps → ∀ {m : ℕ} {η : ℝ},
        CepsSobolevClass m η fW → 2 * dom.c₀ ≤ η → cepsSobolev m η fW ≤ M → N + 3 ≤ m →
          ∀ y : ℝ, |y| ≤ R * eps ^ 2 →
            ‖cepsScaledTrueNormalExpression dom ρW ((2 * eps)⁻¹) δ (I * y) -
              ∑ j ∈ range (N + 1), ((((2 * eps)⁻¹) ^ j : ℝ) : ℂ) *
                coeff j (cepsScaledNormalSeries dom ρW N (I * y))‖ ≤
              K * (eps⁻¹) ^ (N + 1) * (1 + |y|) ^ (N + 4) := by
  let B := dom.normalSeriesScaleBase N M
  let C := dom.normalSeriesBudgetConstant N M δ
  have hB : 0 < B := normalSeriesScaleBase_pos dom hW hθ hD N hM0
  have hC : 0 ≤ C := normalSeriesBudgetConstant_nonneg dom hW hθ hD N hM0 hδ
  refine ⟨C * 2 ^ (N + 4), B ^ 2 / 4, max 1 (2 / B), by positivity,
    by positivity, le_max_left _ _, ?_⟩
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
  have ht := (cepsScaledTrueNormalExpression_seriesApprox dom hW hθ hD
    (b := (2 * eps)⁻¹) (z := I * (y : ℂ)) hf hη hM N hm
    hδ hδactual (inv_pos.mpr (mul_pos (by norm_num) heps0)) hz
      (by simpa only [hn] using hsmall)).2
  have htSum : truncEval (cepsScaledNormalSeries dom ρW N (I * y)) N ((2 * eps)⁻¹) =
      ∑ j ∈ range (N + 1), ((((2 * eps)⁻¹) ^ j : ℝ) : ℂ) *
        coeff j (cepsScaledNormalSeries dom ρW N (I * y)) := by
    simp only [truncEval, ofReal_pow, mul_comm]
  rw [htSum, hn] at ht
  have hpow : (1 + Real.sqrt |y|) ^ (2 * N + 8) ≤ 2 ^ (N + 4) * (1 + |y|) ^ (N + 4) := by
    have hs := Real.sq_sqrt (abs_nonneg y)
    have hs0 := Real.sqrt_nonneg |y|
    have hp : (1 + Real.sqrt |y|) ^ 2 ≤ 2 * (1 + |y|) := by nlinarith [sq_nonneg (Real.sqrt |y| - 1)]
    calc
      _ = ((1 + Real.sqrt |y|) ^ 2) ^ (N + 4) := by rw [← pow_mul]; congr 1
      _ ≤ (2 * (1 + |y|)) ^ (N + 4) := pow_le_pow_left₀ (by positivity) hp _
      _ = _ := mul_pow _ _ _
  have hscale : (2 * eps)⁻¹ ≤ eps⁻¹ := by
    apply inv_anti₀ heps0
    linarith
  apply ht.trans
  calc
    _ ≤ C * (2 ^ (N + 4) * (1 + |y|) ^ (N + 4)) * (eps⁻¹) ^ (N + 1) := by
      gcongr
    _ = _ := by ring

end PGM
