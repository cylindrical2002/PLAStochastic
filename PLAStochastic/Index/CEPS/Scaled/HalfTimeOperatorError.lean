import PLAStochastic.Index.CEPS.Scaled.PositiveEntranceCorrectionError
import PLAStochastic.Index.CEPS.Scaled.TruePositivePair

/-! # Half-line time-operator errors recovered from full and corrected bridges -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSurrogate_timeOperator_sub {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    (lam : ℝ) (hl : lam ≠ 0) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z))
    (hbN : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    cepsScaledTimeOperator lam b (fun ζ => cepsScaledSurrogateBridge dom ρW N lam ζ b) z -
      cepsScaledTimeOperator lam b (fun ζ => cepsScaledSurrogateHalfBridge dom ρW N lam ζ b) z =
        cepsScaledTimeOperator lam b (fun ζ => cepsScaledSurrogateBridgeCorrection dom ρW N lam ζ b) z := by
  obtain ⟨_, hB, _, hC⟩ := cepsScaledBridges_frequency_differentiableAt dom hW hθ hD hf hη hM N hN lam hl hz hb hbs hbN
  have heq : (fun ζ => cepsScaledSurrogateHalfBridge dom ρW N lam ζ b) =
      (fun ζ => cepsScaledSurrogateBridge dom ρW N lam ζ b) -
        (fun ζ => cepsScaledSurrogateBridgeCorrection dom ρW N lam ζ b) := by
    funext ζ
    simp only [Pi.sub_apply, cepsScaledSurrogateBridgeCorrection]
    ring
  have hHalf : DifferentiableAt ℂ (fun ζ => cepsScaledSurrogateHalfBridge dom ρW N lam ζ b) z := by
    rw [heq]
    exact hB.sub hC
  have hd := deriv_sub hB hHalf
  simp only [Pi.sub_def] at hd
  unfold cepsScaledTimeOperator cepsScaledSurrogateBridgeCorrection
  rw [hd]
  ring

include hW hθ hD in
theorem cepsScaledBridge_error_weights_le (M lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z)) :
    Real.exp (-(cepsScaledSignedRoot D θ ρW lam z 1 b * (1 + (b : ℂ) * lam)).re) ≤ 1 ∧
    Real.exp (((cepsScaledSignedRoot D θ ρW lam z (-1) b -
      2 * cepsScaledSignedRoot D θ ρW lam z 1 b) * (1 + (b : ℂ) * lam)).re) ≤ 1 := by
  obtain ⟨hp, ha⟩ := cepsScaledTrueFrequency_root_re_signs dom hW hθ hD M lam hz hb hbs
  obtain ⟨_, _, _, _, hwlo, _, _⟩ := cepsScaledTrueFrequency_curve_bounds dom hW hθ hD M lam hz hb hbs
  have hw : 0 ≤ 1 + b * lam := by linarith
  have hwre : (1 + (b : ℂ) * (lam : ℂ)).re = 1 + b * lam := by simp
  have hwim : (1 + (b : ℂ) * (lam : ℂ)).im = 0 := by simp
  constructor
  · apply Real.exp_le_one_iff.mpr
    rw [mul_re, hwre, hwim, mul_zero, sub_zero]
    exact neg_nonpos.mpr (mul_nonneg hp hw)
  · apply Real.exp_le_one_iff.mpr
    simp only [mul_re, sub_re, hwre, hwim, mul_zero, sub_zero, re_ofNat, im_ofNat, zero_mul]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hw

include hW hθ hD in
theorem cepsScaledTrueHalfBridge_timeOperator_error_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 3 ≤ m)
    (lam : ℝ) (hlam : 1 ≤ lam) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z))
    (hbN : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius (N + 1) M lam z)) :
    ‖cepsScaledTimeOperator lam b (fun ζ => cepsScaledTrueHalfBridge dom ρW lam ζ b) z -
      cepsScaledTimeOperator lam b (fun ζ => cepsScaledSurrogateHalfBridge dom ρW (N + 1) lam ζ b) z‖ ≤
      (dom.bridgeTimeErrorConstant (N + 1) M + 21 * dom.kernelFrequencyConstant (N + 1) M ^ 3) *
        b ^ (N + 2) * (1 + |lam| + Real.sqrt ‖z‖) ^ (N + 3) := by
  have ht := cepsScaledTrue_timeOperator_sub dom hW hθ hD M lam hlam hz hb hbs
  have hs := cepsScaledSurrogate_timeOperator_sub dom hW hθ hD hf hη hM (N + 1) (by omega)
    lam (by linarith) hz hb hbs hbN
  have heq : cepsScaledTimeOperator lam b (fun ζ => cepsScaledTrueHalfBridge dom ρW lam ζ b) z -
      cepsScaledTimeOperator lam b (fun ζ => cepsScaledSurrogateHalfBridge dom ρW (N + 1) lam ζ b) z =
      (cepsScaledTimeOperator lam b (fun ζ => cepsScaledTrueBridge dom ρW lam ζ b) z -
        cepsScaledTimeOperator lam b (fun ζ => cepsScaledSurrogateBridge dom ρW (N + 1) lam ζ b) z) -
      (cepsScaledTimeOperator lam b (fun ζ => cepsScaledTrueBridgeCorrection dom ρW lam ζ b) z -
        cepsScaledTimeOperator lam b (fun ζ => cepsScaledSurrogateBridgeCorrection dom ρW (N + 1) lam ζ b) z) := by
    linear_combination -ht + hs
  have hK := (kernelFrequencyConstant_pos dom (N + 1) M).le
  have hB : 0 ≤ dom.bridgeTimeErrorConstant (N + 1) M := by
    unfold CepsCanonDomain.bridgeTimeErrorConstant; positivity
  obtain ⟨he, hc⟩ := cepsScaledBridge_error_weights_le dom hW hθ hD M lam hz hb hbs
  have hO := (cepsScaledTrueBridge_timeOperator_error_budget dom hW hθ hD hf hη hM N hN lam hz hb hbs hbN).trans
    ((mul_le_mul_of_nonneg_left he (by positivity)).trans_eq (mul_one _))
  have hC := (cepsScaledTrueBridgeCorrection_timeOperator_error_budget dom hW hθ hD hf hη hM N hN lam hz hb hbs hbN).trans
    ((mul_le_mul_of_nonneg_left hc (by positivity)).trans_eq (mul_one _))
  rw [heq]
  exact ((norm_sub_le _ _).trans (add_le_add hO hC)).trans_eq (by ring)

end PGM
