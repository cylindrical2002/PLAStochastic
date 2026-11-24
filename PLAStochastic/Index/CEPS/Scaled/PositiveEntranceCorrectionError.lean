import PLAStochastic.Index.CEPS.Scaled.PositiveHalfEntranceError
import PLAStochastic.Index.CEPS.Scaled.TruePositiveEntranceDecay

/-! # Positive-tail entrance cancellation errors preserve lower-root decay -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrueEntranceCorrection_error_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    (lam : ℝ) (hlam : 1 ≤ lam) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z))
    (hbN : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    ‖cepsScaledTrueEntranceCorrection dom ρW lam z b -
      cepsScaledSurrogateEntranceCorrection dom ρW N lam z b‖ ≤
      (7 * dom.positiveEntranceErrorConstant N M ^ 3) * (1 + |lam| + Real.sqrt ‖z‖) *
        (Real.exp (-(cepsScaledSignedRoot D θ ρW lam z 1 b * (1 + (b : ℂ) * lam)).re) +
          Real.exp (-(((b : ℂ) * z) * (1 + (b : ℂ) * lam)).re)) *
            Real.exp ((cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + (b : ℂ) * lam)).re) *
              |b * lam| ^ (N + 1) := by
  let p := cepsScaledSignedRoot D θ ρW lam z 1 (b : ℂ)
  let a := cepsScaledSignedRoot D θ ρW lam z (-1) (b : ℂ)
  let t := (b : ℂ) * z
  let w : ℂ := 1 + (b : ℂ) * lam
  let K := dom.positiveEntranceErrorConstant N M
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let Q := Real.exp (-(p * w).re) + Real.exp (-(t * w).re)
  let T := Real.exp ((a * w).re)
  let e := |b * lam| ^ (N + 1)
  let A := cepsScaledTrueHalfEntrance dom ρW lam z b
  let c := cepsScaledSurrogateHalfEntrance dom ρW N lam z b
  let B := dslope (cepsScaledTrueG dom ρW lam z b) p t
  let d := dslope (cepsScaledSurrogateG dom ρW N lam z b) p t
  let I := (cepsScaledTrueDenominator dom ρW lam z b)⁻¹
  let J := (cepsScaledSurrogateDenominator dom ρW N lam z b)⁻¹
  have hK : 0 ≤ K := (positiveEntranceErrorConstant_pos dom N M).le
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hbound : ∀ c ∈ dom.positiveEntranceErrorConstants N M, c ≤ K :=
    fun _ hc => positiveEntranceErrorConstant_le dom N M hc
  have hbD := ball_subset_ball (truePairScaleRadius_le dom M lam z)
    (ball_subset_ball (trueFrequencyScaleRadius_le dom M lam z) hbs)
  have hbP : (b : ℂ) ∈ ball (0 : ℂ) (dom.pairPolynomialScaleBase 0 M / X) :=
    ball_subset_ball (div_le_div_of_nonneg_right (min_le_left _ _) hX) hbD
  have ht := cepsScaledPositiveMarkerGap_ne_zero dom hW hθ hD 0 M lam hlam hz hbP
  have he1 : e ≤ 1 := pow_le_one₀ (abs_nonneg _)
    (cepsScaledTrueScale_drift_le_one dom hW hθ hD M lam hz hbD)
  obtain ⟨_, hc, hAc⟩ := cepsScaledHalfEntrance_positive_comparison_profile dom hW hθ hD hf hη hM N hN lam hlam hz hb hbs hbN
  have hB : ‖B‖ ≤ K * Q := (cepsScaledTrueG_first_dslope_weighted_budget dom hW hθ hD hf hη hM
    (by omega) lam hz hbD).trans (mul_le_mul_of_nonneg_right
      (hbound _ (by simp [CepsCanonDomain.positiveEntranceErrorConstants])) hQ)
  have hBd0 := cepsScaledTrueG_dslope_error_budget dom hW hθ hD hf hη hM N hN lam hz hbN
    (entranceScaleCurve_root_norm_le_half dom hW hθ hD N M lam hz hbN (by norm_num : ‖(1 : ℂ)‖ ≤ 1))
    (entranceScaleCurve_mark_norm_le_half dom hW hθ hD N M lam hz hbN)
  have hBd : ‖B - d‖ ≤ K * Q * e := by
    apply hBd0.trans
    calc
      _ = dom.trueSpatialErrorConstant N M 1 * Q * e := by ring
      _ ≤ K * Q * e := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (hbound _ (by simp [CepsCanonDomain.positiveEntranceErrorConstants])) hQ) (pow_nonneg (abs_nonneg _) _)
  have hd : ‖d‖ ≤ 2 * K * Q := by
    have hn := norm_sub_le B (B - d)
    rw [sub_sub_cancel] at hn
    exact hn.trans ((add_le_add hB (hBd.trans (mul_le_of_le_one_right (mul_nonneg hK hQ) he1))).trans_eq (by ring))
  have hI : ‖I‖ ≤ K * X * T := (cepsScaledTrueDenominator_inverse_weighted_budget dom hW hθ hD hf hη hM
    (by omega) lam hz hbD).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (hbound _ (by simp [CepsCanonDomain.positiveEntranceErrorConstants])) hX) (Real.exp_pos _).le)
  have hIJ0 : ‖I - J‖ ≤ (dom.trueDenominatorRelativeConstant N M *
      (2 * dom.surrogateSlopePolynomialConstant 0 M)) * X * T * e :=
    (cepsScaledTrueDenominator_inverse_error_budget dom hW hθ hD hf hη hM N hN lam hz hbD hbN).trans_eq (by ring)
  have hIJ : ‖I - J‖ ≤ K * X * T * e := hIJ0.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (hbound _ (by simp [CepsCanonDomain.positiveEntranceErrorConstants])) hX) (Real.exp_pos _).le)
        (pow_nonneg (abs_nonneg _) _))
  have h := cepsNorm_three_factor_error_entrance_profile hB hI hc hd hAc hBd hIJ
  rw [cepsScaledTrueEntranceCorrection_eq_firstSlope dom hW hθ hD hf hη hM (by omega) lam hz hbD ht,
    cepsScaledSurrogateEntranceCorrection_eq_firstSlope dom hW hθ hD hf hη hM N (by omega) lam hz hbN ht]
  simp only [div_eq_mul_inv, neg_mul]
  change ‖-(A * B * I) - -(c * d * J)‖ ≤ _
  rw [show -(A * B * I) - -(c * d * J) = -(A * B * I - c * d * J) by ring, norm_neg]
  exact h

include hW hθ hD in
theorem cepsScaledPositiveEntrance_weights_decay (M lam : ℝ) (hlam : 0 ≤ lam)
    {z : ℂ} (hz : z.re = 0) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z)) :
    (Real.exp (-(cepsScaledSignedRoot D θ ρW lam z 1 b * (1 + (b : ℂ) * lam)).re) +
      Real.exp (-(((b : ℂ) * z) * (1 + (b : ℂ) * lam)).re)) *
        Real.exp ((cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + (b : ℂ) * lam)).re) ≤
          2 * Real.exp (-dom.negativeBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) := by
  have hbD := ball_subset_ball (truePairScaleRadius_le dom M lam z)
    (ball_subset_ball (trueFrequencyScaleRadius_le dom M lam z) hbs)
  have hbP : (b : ℂ) ∈ ball (0 : ℂ) (dom.pairPolynomialScaleBase 0 M /
      (1 + |lam| + Real.sqrt ‖z‖)) :=
    ball_subset_ball (div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)) hbD
  have hbC := ball_subset_ball (min_le_left _ _)
    (ball_subset_ball (pairPolynomialScaleRadius_le dom hW hθ hD 0 M lam z).1 hbP)
  have he := cepsScaledRootMinus_positive_exp_polynomial dom hW hθ hD 0 M lam hlam hz.symm.le hbC
  obtain ⟨hp, _⟩ := cepsScaledTrueFrequency_root_re_signs dom hW hθ hD M lam hz.symm.le hb hbs
  obtain ⟨_, _, _, _, hwlo, _, _⟩ := cepsScaledTrueFrequency_curve_bounds dom hW hθ hD M lam hz.symm.le hb hbs
  have hwre : (1 + (b : ℂ) * (lam : ℂ)).re = 1 + b * lam := by simp
  have hwim : (1 + (b : ℂ) * (lam : ℂ)).im = 0 := by simp
  have hpw : 0 ≤ (cepsScaledSignedRoot D θ ρW lam z 1 b * (1 + (b : ℂ) * lam)).re := by
    rw [mul_re, hwre, hwim, mul_zero, sub_zero]
    exact mul_nonneg hp (by linarith)
  have htw : (((b : ℂ) * z) * (1 + (b : ℂ) * lam)).re = 0 := by simp [mul_re, mul_im, hz]
  have hQ : Real.exp (-(cepsScaledSignedRoot D θ ρW lam z 1 b * (1 + (b : ℂ) * lam)).re) +
      Real.exp (-(((b : ℂ) * z) * (1 + (b : ℂ) * lam)).re) ≤ 2 := by
    rw [htw, neg_zero, Real.exp_zero]
    have hh := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hpw)
    linarith
  exact mul_le_mul hQ he (Real.exp_pos _).le (by norm_num)

include hW hθ hD in
theorem cepsScaledTrueEntranceCorrection_imaginary_error_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    (lam : ℝ) (hlam : 1 ≤ lam) {z : ℂ} (hz : z.re = 0) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z))
    (hbN : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    ‖cepsScaledTrueEntranceCorrection dom ρW lam z b -
      cepsScaledSurrogateEntranceCorrection dom ρW N lam z b‖ ≤
      (14 * dom.positiveEntranceErrorConstant N M ^ 3) * (1 + |lam| + Real.sqrt ‖z‖) *
        Real.exp (-dom.negativeBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) * |b * lam| ^ (N + 1) := by
  have hK := (positiveEntranceErrorConstant_pos dom N M).le
  have h := cepsScaledTrueEntranceCorrection_error_budget dom hW hθ hD hf hη hM N hN lam hlam hz.symm.le hb hbs hbN
  have he := cepsScaledPositiveEntrance_weights_decay dom hW hθ hD M lam (by linarith) hz hb hbs
  apply h.trans
  calc
    _ = (7 * dom.positiveEntranceErrorConstant N M ^ 3 * (1 + |lam| + Real.sqrt ‖z‖)) *
      ((Real.exp (-(cepsScaledSignedRoot D θ ρW lam z 1 b * (1 + (b : ℂ) * lam)).re) +
        Real.exp (-(((b : ℂ) * z) * (1 + (b : ℂ) * lam)).re)) *
          Real.exp ((cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + (b : ℂ) * lam)).re)) * |b * lam| ^ (N + 1) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by positivity))
      (pow_nonneg (abs_nonneg _) _)).trans_eq (by ring)

end PGM
