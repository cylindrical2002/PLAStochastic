import PLAStochastic.Index.CEPS.Scaled.NormalZeroFrequencyTaylor

/-! # A fixed frequency window for the actual normal Taylor estimate -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.trueNormalFixedTaylorConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (M δ : ℝ) : ℝ :=
  dom.trueNormalZeroTaylorConstant M δ +
    4 * (32 * dom.trueTransformFrequencyConstant M + 1 +
      2 * dom.trueEndpointZeroFrequencyConstant / dom.trueHalfZeroFrequencyBase +
        dom.truePairIntegralConstant M) / dom.trueEndpointZeroFrequencyBase ^ 2

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem trueNormalFixedTaylorConstant_nonneg (M : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    0 ≤ dom.trueNormalFixedTaylorConstant M δ := by
  have := trueNormalZeroTaylorConstant_nonneg dom hW hθ hD M hδ
  have := trueTransformFrequencyConstant_nonneg dom hθ hD M
  have := trueEndpointZeroFrequencyConstant_nonneg dom hW hθ hD
  have := truePairIntegralConstant_nonneg dom M
  have := (trueHalfZeroFrequencyBase_pos dom hW hθ hD).le
  unfold CepsCanonDomain.trueNormalFixedTaylorConstant
  positivity

include hW hθ hD in
theorem cepsScaledTrueNormalExpression_fixed_zero_window_taylor {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m) {b δ : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1) (hδ0 : 0 ≤ δ) (hδ : δ ≤ dom.trueDecayScaleBase M / 4)
    (hbs1 : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M 1 0))
    (hbband : 2 * b < dom.trueTransformFrequencyBase M) {z : ℂ} (hz : z.re = 0) (hz1 : ‖z‖ ≤ 1) :
    ‖cepsScaledTrueNormalExpression dom ρW b δ z - 1 - z * cepsScaledTrueNormalSlope dom ρW b δ‖ ≤
      dom.trueNormalFixedTaylorConstant M δ / b ^ 5 * ‖z‖ ^ 2 := by
  let A := 32 * dom.trueTransformFrequencyConstant M + 1 +
    2 * dom.trueEndpointZeroFrequencyConstant / dom.trueHalfZeroFrequencyBase + dom.truePairIntegralConstant M
  let R := dom.trueEndpointZeroFrequencyBase
  have hR : 0 < R := trueEndpointZeroFrequencyBase_pos dom hW hθ hD
  have hRh : 0 < dom.trueHalfZeroFrequencyBase := trueHalfZeroFrequencyBase_pos dom hW hθ hD
  have hT : 0 ≤ dom.trueTransformFrequencyConstant M := trueTransformFrequencyConstant_nonneg dom hθ hD M
  have hE : 0 ≤ dom.trueEndpointZeroFrequencyConstant := trueEndpointZeroFrequencyConstant_nonneg dom hW hθ hD
  have hI : 0 ≤ dom.truePairIntegralConstant M := truePairIntegralConstant_nonneg dom M
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hCb : 0 ≤ 4 * A / R ^ 2 := by positivity
  have hsmallscale : b * (1 + Real.sqrt ‖z‖) < dom.trueTransformFrequencyBase M := by
    have hs : Real.sqrt ‖z‖ ≤ 1 := by simpa using Real.sqrt_le_sqrt hz1
    nlinarith
  have hdecay : b * (1 + Real.sqrt ‖z‖) < dom.trueDecayScaleBase M / 4 :=
    hsmallscale.trans_le (min_le_left _ _)
  by_cases hsmall : z ∈ ball 0 (R * b / 2)
  · apply (cepsScaledTrueNormalExpression_zero_frequency_taylor dom hW hθ hD
      hf hη hM hm hb hb1 hδ0 hδ hbs1 hz hdecay hsmall).trans
    change dom.trueNormalZeroTaylorConstant M δ / b ^ 5 * ‖z‖ ^ 2 ≤
      (dom.trueNormalZeroTaylorConstant M δ + 4 * A / R ^ 2) / b ^ 5 * ‖z‖ ^ 2
    gcongr
    exact le_add_of_nonneg_right hCb
  · have hGn : ‖cepsScaledTrueNormalExpression dom ρW b δ z‖ ≤ 32 * dom.trueTransformFrequencyConstant M := by
      have ht := cepsScaledTrueNormalExpression_frequency_budget dom hW hθ hD hf hη hM hm hb hδ hz hsmallscale
      have hs : 1 + Real.sqrt ‖z‖ ≤ 2 := by
        have ht : Real.sqrt ‖z‖ ≤ 1 := by simpa using Real.sqrt_le_sqrt hz1
        linarith
      have he : Real.exp (-dom.entranceBridgeDecayRate * Real.sqrt ‖z‖) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (entranceBridgePolynomial_constants dom hW hθ hD 0 M).2.le)
          (Real.sqrt_nonneg _)
      calc
        _ ≤ dom.trueTransformFrequencyConstant M * (1 + Real.sqrt ‖z‖) ^ 5 *
            Real.exp (-dom.entranceBridgeDecayRate * Real.sqrt ‖z‖) := ht
        _ ≤ dom.trueTransformFrequencyConstant M * 2 ^ 5 * 1 := by gcongr
        _ = _ := by ring
    have hb0 : b * (1 + Real.sqrt ‖(0 : ℂ)‖) < dom.trueDecayScaleBase M / 4 := by
      simp only [norm_zero, Real.sqrt_zero, add_zero, mul_one]
      nlinarith [hdecay, Real.sqrt_nonneg ‖z‖]
    have hI0 : ‖∫ lam : ℝ, cepsScaledTrueCutoffPair dom ρW b δ 0 lam‖ ≤ dom.truePairIntegralConstant M := by
      simpa only [norm_zero, Real.sqrt_zero, add_zero, zero_mul, mul_zero, Real.exp_zero,
        one_pow, mul_one] using cepsScaledTrueCutoffPair_integral_budget dom hW hθ hD
          hf hη hM hm hb hδ (by simp) hb0
    have hDn : ‖cepsScaledTrueNormalSlope dom ρW b δ‖ ≤
        2 * dom.trueEndpointZeroFrequencyConstant / (dom.trueHalfZeroFrequencyBase * b) + dom.truePairIntegralConstant M := by
      unfold cepsScaledTrueNormalSlope
      exact (norm_sub_le _ _).trans ((add_le_add
        (by simpa only [norm_neg] using cepsScaledZeroEndpoint_zero_frequency_bound dom hW hθ hD M hb hb1 hbs1)
        hI0))
    have hcoarse : ‖cepsScaledTrueNormalExpression dom ρW b δ z - 1 - z * cepsScaledTrueNormalSlope dom ρW b δ‖ ≤ A / b := by
      have h1 := norm_sub_le (cepsScaledTrueNormalExpression dom ρW b δ z) 1
      have h2 := norm_sub_le (cepsScaledTrueNormalExpression dom ρW b δ z - 1) (z * cepsScaledTrueNormalSlope dom ρW b δ)
      rw [norm_one] at h1
      rw [norm_mul] at h2
      have hh := mul_le_mul hz1 hDn (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      have ht : ‖cepsScaledTrueNormalExpression dom ρW b δ z - 1 - z * cepsScaledTrueNormalSlope dom ρW b δ‖ ≤
          32 * dom.trueTransformFrequencyConstant M + 1 +
            2 * dom.trueEndpointZeroFrequencyConstant / (dom.trueHalfZeroFrequencyBase * b) + dom.truePairIntegralConstant M := by
        linarith
      apply ht.trans
      apply (le_div_iff₀ hb).mpr
      rw [add_mul, add_mul, add_mul,
        show (2 * dom.trueEndpointZeroFrequencyConstant / (dom.trueHalfZeroFrequencyBase * b)) * b =
          2 * dom.trueEndpointZeroFrequencyConstant / dom.trueHalfZeroFrequencyBase by field_simp]
      dsimp [A]
      nlinarith
    have hlarge : R * b / 2 ≤ ‖z‖ := le_of_not_gt (fun hz => hsmall (mem_ball_zero_iff.mpr hz))
    have hsq : R ^ 2 * b ^ 2 ≤ 4 * ‖z‖ ^ 2 := by nlinarith [mul_pos hR hb]
    have hp42 : b ^ 4 ≤ b ^ 2 := by
      rw [show b ^ 4 = b ^ 2 * b ^ 2 by ring]
      exact mul_le_of_le_one_right (sq_nonneg b) (pow_le_one₀ hb.le hb1)
    have hnum : R ^ 2 * b ^ 4 ≤ 4 * ‖z‖ ^ 2 := (mul_le_mul_of_nonneg_left hp42 (sq_nonneg R)).trans hsq
    have hratio : 1 / b ≤ (4 * ‖z‖ ^ 2) / (R ^ 2 * b ^ 5) := by
      apply (div_le_div_iff₀ hb (mul_pos (sq_pos_of_pos hR) (pow_pos hb 5))).mpr
      simpa only [one_mul, show R ^ 2 * b ^ 5 = R ^ 2 * b ^ 4 * b by ring] using mul_le_mul_of_nonneg_right hnum hb.le
    calc
      _ ≤ A / b := hcoarse
      _ ≤ A * ((4 * ‖z‖ ^ 2) / (R ^ 2 * b ^ 5)) := by
        simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hratio hA
      _ = (4 * A / R ^ 2) / b ^ 5 * ‖z‖ ^ 2 := by ring
      _ ≤ (dom.trueNormalZeroTaylorConstant M δ + 4 * A / R ^ 2) / b ^ 5 * ‖z‖ ^ 2 := by
        gcongr
        exact le_add_of_nonneg_left (trueNormalZeroTaylorConstant_nonneg dom hW hθ hD M hδ0)
      _ = _ := rfl

end PGM
