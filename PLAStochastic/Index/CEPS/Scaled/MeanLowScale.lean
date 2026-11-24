import PLAStochastic.Index.CEPS.Scaled.ContourMean

/-! # Uniform inverse-epsilon remainders for the fixed genuine normal slope -/

noncomputable section
open Complex Set Metric MeasureTheory Finset PowerSeries
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrueNormalSlope_contour_mean_expansion (N : ℕ)
    {η' M M' δ : ℝ} (hη' : 0 < η') (hM : 0 ≤ M) (hM' : 0 ≤ M')
    (hδ : 0 < δ) (hδactual : δ ≤ dom.trueDecayScaleBase M / 4) :
    ∃ K eps₀ : ℝ, 0 ≤ K ∧ 1 ≤ eps₀ ∧
      ∀ eps : ℝ, eps₀ ≤ eps → ∀ {ρW' : Measure ℝ} {fW' : ℝ → ℝ},
        IsStepLaw ρW' fW' D θ v → ∀ {m m' : ℕ} {η : ℝ},
        CepsSobolevClass m η fW' → 2 * dom.c₀ ≤ η → cepsSobolev m η fW' ≤ M → 2 ≤ m →
        CepsSobolevClass m' η' fW' → cepsSobolev m' η' fW' ≤ M' → N + 3 ≤ m' →
          ‖cepsScaledTrueNormalSlope dom ρW' (2 * eps)⁻¹ δ +
            ∑ j ∈ range (N + 1), ((((2 * eps)⁻¹) ^ j : ℝ) : ℂ) *
              coeff j (cepsScaledMeanSeries (dom.contour η' hη') ρW' N)‖ ≤
            K * (eps⁻¹) ^ (N + 1) := by
  obtain ⟨C, B, hC, hB, hbudget⟩ := cepsScaledTrueNormalSlope_contour_series_budget
    dom hW hθ hD N hη' hM hM' hδ hδactual
  refine ⟨C, max 1 (1 / B), hC, le_max_left _ _, ?_⟩
  intro eps heps ρW' fW' hW' m m' η hf hη hMf hm hf' hMf' hm'
  have heps1 : 1 ≤ eps := (le_max_left _ _).trans heps
  have heps0 : 0 < eps := zero_lt_one.trans_le heps1
  have hepsB : 1 / B ≤ eps := (le_max_right _ _).trans heps
  have hbeps : 1 ≤ B * eps := by
    have ht := (div_le_iff₀ hB).mp hepsB
    nlinarith
  have hb : 0 < (2 * eps)⁻¹ := inv_pos.mpr (mul_pos (by norm_num) heps0)
  have hbB : (2 * eps)⁻¹ < B := by
    rw [inv_eq_one_div]
    exact (div_lt_iff₀ (mul_pos (by norm_num) heps0)).mpr (by nlinarith)
  have ht := (hbudget hW' hf hη hMf hm hf' hMf' hm' hb hbB).2
  have hSum : truncEval (cepsScaledMeanSeries (dom.contour η' hη') ρW' N) N ((2 * eps)⁻¹) =
      ∑ j ∈ range (N + 1), ((((2 * eps)⁻¹) ^ j : ℝ) : ℂ) *
        coeff j (cepsScaledMeanSeries (dom.contour η' hη') ρW' N) := by
    simp only [truncEval, ofReal_pow, mul_comm]
  rw [show -cepsScaledTrueNormalSlope dom ρW' (2 * eps)⁻¹ δ -
      truncEval (cepsScaledMeanSeries (dom.contour η' hη') ρW' N) N ((2 * eps)⁻¹) =
      -(cepsScaledTrueNormalSlope dom ρW' (2 * eps)⁻¹ δ +
        truncEval (cepsScaledMeanSeries (dom.contour η' hη') ρW' N) N ((2 * eps)⁻¹)) by ring,
    norm_neg, hSum] at ht
  have hscale : (2 * eps)⁻¹ ≤ eps⁻¹ := by
    apply inv_anti₀ heps0
    linarith
  exact ht.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb.le hscale _) hC)

end PGM
