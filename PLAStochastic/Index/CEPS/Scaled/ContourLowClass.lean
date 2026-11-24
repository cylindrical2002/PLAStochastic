import PLAStochastic.Index.CEPS.Scaled.ContourLowBand

/-! # Class-uniform low-frequency windows at every positive Sobolev weight -/

noncomputable section
open Complex Set Metric MeasureTheory Finset PowerSeries
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrueNormalExpression_contour_series_budget_class (N : ℕ)
    {η' M M' δ : ℝ} (hη' : 0 < η') (hM : 0 ≤ M) (hM' : 0 ≤ M')
    (hδ : 0 < δ) (hδactual : δ ≤ dom.trueDecayScaleBase M / 4) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 < B ∧ ∀ {ρW' : Measure ℝ} {fW' : ℝ → ℝ},
      IsStepLaw ρW' fW' D θ v → ∀ {m m' : ℕ} {η : ℝ},
      CepsSobolevClass m η fW' → 2 * dom.c₀ ≤ η → cepsSobolev m η fW' ≤ M → 2 ≤ m →
      CepsSobolevClass m' η' fW' → cepsSobolev m' η' fW' ≤ M' → N + 3 ≤ m' →
      ∀ {b : ℝ}, 0 < b → ∀ {z : ℂ}, z.re = 0 → b * (1 + Real.sqrt ‖z‖) < B →
        SeriesApprox (cepsScaledTrueNormalExpression dom ρW' b δ z)
          (cepsScaledNormalSeries (dom.contour η' hη') ρW' N z) N b
          (C * (1 + Real.sqrt ‖z‖) ^ (2 * N + 8)) := by
  let dom' := dom.contour η' hη'
  let δ' := min δ (dom'.trueDecayScaleBase M' / 8)
  let B := min (dom.trueDecayScaleBase M / 4)
    (min (dom'.trueDecayScaleBase M' / 4) (dom'.normalSeriesScaleBase N M'))
  let C := dom'.normalSeriesBudgetConstant N M' δ' +
    (cepsMarkedDiscountBound D θ / (θ / 2)) * dom.trueCutoffTailIntegralConstant M δ' (N + 1)
  have hBase := trueDecayScaleBase_pos dom hW hθ hD hM
  have hBase' := trueDecayScaleBase_pos dom' hW hθ hD hM'
  have hSer := normalSeriesScaleBase_pos dom' hW hθ hD N hM'
  have hδ' : 0 < δ' := lt_min hδ (by positivity)
  have hδle : δ' ≤ δ := min_le_left _ _
  have hδsmall : δ' ≤ dom'.trueDecayScaleBase M' / 4 :=
    (min_le_right _ _).trans (by linarith)
  have hC : 0 ≤ C := add_nonneg (normalSeriesBudgetConstant_nonneg dom' hW hθ hD N hM' hδ')
    (mul_nonneg (div_nonneg (cepsMarkedDiscountBound_pos hD hθ).le (half_pos hθ).le)
      (trueCutoffTailIntegralConstant_nonneg dom M hδ' (N + 1)))
  refine ⟨C, B, hC, by dsimp [B]; positivity, ?_⟩
  intro ρW' fW' hW' m m' η hf hη hMf hm hf' hMf' hm' b hb z hz hsmall
  have hbz := hsmall.trans_le (min_le_left _ _)
  have hbz' := hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hSeries := hsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hEndSmall : b * (1 + Real.sqrt ‖z‖) < dom'.trueEndpointScaleBase M' / 2 :=
    hSeries.trans_le (min_le_left _ _)
  have hEnd : (b : ℂ) ∈ ball (0 : ℂ) (dom'.trueEndpointScaleRadius M' z) := by
    rw [mem_ball_zero_iff, norm_real, Real.norm_eq_abs, abs_of_pos hb]
    unfold CepsCanonDomain.trueEndpointScaleRadius
    apply (lt_div_iff₀ (by positivity)).mpr
    nlinarith [mul_nonneg hb.le (Real.sqrt_nonneg ‖z‖)]
  have hDsc : b * (1 + Real.sqrt ‖z‖) < cepsDiscountFrequencyBase D θ := by
    have hDhalf := hSeries.trans_le ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
    exact hDhalf.trans_le (half_le_self (cepsDiscountFrequencyBase_pos hD hθ).le)
  exact cepsScaledTrueNormalExpression_shrink_seriesApprox dom hW' hθ hD
    (lt_min dom.c₀_pos (half_pos hη')) (min_le_left _ _) hf hη hMf hm
    hf' (dom.two_contour_c₀_le hη') hMf' N hm' hb hδ' hδle hδactual hδsmall
    hz hbz hbz' hEnd hDsc hSeries

include hW hθ hD in
theorem cepsScaledTrueNormalExpression_contour_low_band_class (N : ℕ)
    {η' M M' δ : ℝ} (hη' : 0 < η') (hM : 0 ≤ M) (hM' : 0 ≤ M')
    (hδ : 0 < δ) (hδactual : δ ≤ dom.trueDecayScaleBase M / 4) :
    ∃ K R eps₀ : ℝ, 0 ≤ K ∧ 0 < R ∧ 1 ≤ eps₀ ∧
      ∀ eps : ℝ, eps₀ ≤ eps → ∀ {ρW' : Measure ℝ} {fW' : ℝ → ℝ},
      IsStepLaw ρW' fW' D θ v → ∀ {m m' : ℕ} {η : ℝ},
        CepsSobolevClass m η fW' → 2 * dom.c₀ ≤ η → cepsSobolev m η fW' ≤ M → 2 ≤ m →
        CepsSobolevClass m' η' fW' → cepsSobolev m' η' fW' ≤ M' → N + 3 ≤ m' →
          ∀ y : ℝ, |y| ≤ R * eps ^ 2 →
            ‖cepsScaledTrueNormalExpression dom ρW' ((2 * eps)⁻¹) δ (I * y) -
              ∑ j ∈ range (N + 1), ((((2 * eps)⁻¹) ^ j : ℝ) : ℂ) *
                coeff j (cepsScaledNormalSeries (dom.contour η' hη') ρW' N (I * y))‖ ≤
              K * (eps⁻¹) ^ (N + 1) * (1 + |y|) ^ (N + 4) := by
  obtain ⟨C, B, hC, hB, hbudget⟩ := cepsScaledTrueNormalExpression_contour_series_budget_class
    dom hW hθ hD N hη' hM hM' hδ hδactual
  refine ⟨C * 2 ^ (N + 4), B ^ 2 / 4, max 1 (2 / B), by positivity,
    by positivity, le_max_left _ _, ?_⟩
  intro eps heps ρW' fW' hW' m m' η hf hη hMf hm hf' hMf' hm' y hy
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
  have ht := (hbudget (b := (2 * eps)⁻¹) (z := I * (y : ℂ)) hW' hf hη hMf hm hf' hMf' hm'
    (inv_pos.mpr (mul_pos (by norm_num) heps0)) hz (by simpa only [hn] using hsmall)).2
  have htSum : truncEval (cepsScaledNormalSeries (dom.contour η' hη') ρW' N (I * y)) N ((2 * eps)⁻¹) =
      ∑ j ∈ range (N + 1), ((((2 * eps)⁻¹) ^ j : ℝ) : ℂ) *
        coeff j (cepsScaledNormalSeries (dom.contour η' hη') ρW' N (I * y)) := by
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
