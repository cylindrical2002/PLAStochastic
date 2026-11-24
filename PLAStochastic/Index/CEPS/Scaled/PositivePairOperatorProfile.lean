import PLAStochastic.Index.CEPS.Scaled.PositivePairEntranceProfile

/-! # Complete time-operator profiles for positive-tail pair errors -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledBridgeCorrection_positive_error_weight (M lam : ℝ) (hlam : 0 ≤ lam)
    {z : ℂ} (hz : z.re = 0) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z)) :
    Real.exp (((cepsScaledSignedRoot D θ ρW lam z (-1) b -
      2 * cepsScaledSignedRoot D θ ρW lam z 1 b) * (1 + (b : ℂ) * lam)).re) ≤
        2 * Real.exp (-(dom.positiveBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) / 2) := by
  let p := cepsScaledSignedRoot D θ ρW lam z 1 (b : ℂ)
  let a := cepsScaledSignedRoot D θ ρW lam z (-1) (b : ℂ)
  let w : ℂ := 1 + (b : ℂ) * lam
  have ht : (((b : ℂ) * z) * w).re = 0 := by simp [w, mul_re, mul_im, hz]
  have he := cepsScaledPositiveEntrance_weights_decay dom hW hθ hD M lam hlam hz hb hbs
  change (Real.exp (-(p * w).re) + Real.exp (-(((b : ℂ) * z) * w).re)) * Real.exp ((a * w).re) ≤ _ at he
  rw [ht, neg_zero, Real.exp_zero] at he
  have ha : Real.exp ((a * w).re) ≤ 2 * Real.exp (-dom.negativeBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) :=
    (le_mul_of_one_le_left (Real.exp_pos _).le (by linarith [Real.exp_pos (-(p * w).re)])).trans he
  obtain ⟨hp, _⟩ := cepsScaledTrueFrequency_root_re_signs dom hW hθ hD M lam hz.symm.le hb hbs
  have hpw : 0 ≤ (p * w).re := by
    dsimp only [w]
    have hwre : (1 + (b : ℂ) * (lam : ℂ)).re = 1 + b * lam := by simp
    have hwim : (1 + (b : ℂ) * (lam : ℂ)).im = 0 := by simp
    rw [mul_re, hwre, hwim, mul_zero, sub_zero]
    exact mul_nonneg hp (by positivity)
  have hre : ((a - 2 * p) * w).re = (a * w).re - 2 * (p * w).re := by
    rw [sub_mul, mul_assoc, sub_re]
    simp
  have hc : Real.exp (((a - 2 * p) * w).re) ≤ Real.exp ((a * w).re) :=
    Real.exp_le_exp.mpr (by rw [hre]; linarith)
  exact (hc.trans ha).trans (mul_le_mul_of_nonneg_left
    (cepsScaledPositive_error_decay_le dom hW hθ hD M lam z) (by norm_num))

include hW hθ hD in
theorem cepsScaledPositivePair_operator_error_profile {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 3 ≤ m)
    (lam : ℝ) (hlam : 1 ≤ lam) {z : ℂ} (hz : z.re = 0) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDecayScaleRadius M lam z))
    (hbN : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius (N + 1) M lam z)) :
    let L := dom.positivePairComparisonConstant (N + 1) M
    let X := 1 + |lam| + Real.sqrt ‖z‖
    let beta := b ^ (N + 2)
    let E := Real.exp (-(dom.positiveBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) / 2)
    let Oc := cepsScaledTimeOperator lam b (fun ζ => cepsScaledTrueBridgeCorrection dom ρW lam ζ b) z
    let oc := cepsScaledTimeOperator lam b (fun ζ => cepsScaledSurrogateBridgeCorrection dom ρW (N + 1) lam ζ b) z
    let Oh := cepsScaledTimeOperator lam b (fun ζ => cepsScaledTrueHalfBridge dom ρW lam ζ b) z
    let oh := cepsScaledTimeOperator lam b (fun ζ => cepsScaledSurrogateHalfBridge dom ρW (N + 1) lam ζ b) z
    ‖Oc‖ ≤ L * X * E ∧ ‖Oh‖ ≤ L * X ∧
    ‖Oc - oc‖ ≤ L * beta * X ^ (N + 3) * E ∧ ‖Oh - oh‖ ≤ L * beta * X ^ (N + 3) := by
  let L := dom.positivePairComparisonConstant (N + 1) M
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let E := Real.exp (-(dom.positiveBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) / 2)
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hbound : ∀ c ∈ dom.positivePairErrorConstants (N + 1) M, c ≤ L :=
    fun _ hc => positivePairComparisonConstant_le dom (N + 1) M hc
  have hbf := ball_subset_ball (trueDecayScaleRadius_le_frequency dom M lam z) hbs
  have hO := (cepsScaledTrueBridgeCorrection_timeOperator_budget dom hW hθ hD hf hη hM
    (by omega) lam hlam hz.symm.le hb hbs).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hbound _ (by simp [CepsCanonDomain.positivePairErrorConstants])) hX) (Real.exp_pos _).le)
  have hOh := (cepsScaledTrueHalfBridge_timeOperator_budget dom hW hθ hD M lam hlam hz.symm.le hb hbf).trans
    (mul_le_mul_of_nonneg_right (hbound _ (by simp [CepsCanonDomain.positivePairErrorConstants])) hX)
  have hK := (kernelFrequencyConstant_pos dom (N + 1) M).le
  have he := cepsScaledBridgeCorrection_positive_error_weight dom hW hθ hD M lam (by linarith) hz hb hbf
  have hCE := (cepsScaledTrueBridgeCorrection_timeOperator_error_budget dom hW hθ hD hf hη hM
    N hN lam hz.symm.le hb hbf hbN).trans (mul_le_mul_of_nonneg_left he (by positivity))
  have hCE0 : ‖cepsScaledTimeOperator lam b (fun ζ => cepsScaledTrueBridgeCorrection dom ρW lam ζ b) z -
      cepsScaledTimeOperator lam b (fun ζ => cepsScaledSurrogateBridgeCorrection dom ρW (N + 1) lam ζ b) z‖ ≤
      (42 * dom.kernelFrequencyConstant (N + 1) M ^ 3) * b ^ (N + 2) * X ^ (N + 3) * E := hCE.trans_eq (by ring)
  have hCE' := hCE0.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hbound _ (by simp [CepsCanonDomain.positivePairErrorConstants])) (pow_nonneg hb.le _))
      (pow_nonneg hX _)) (Real.exp_pos _).le)
  have hOhE := (cepsScaledTrueHalfBridge_timeOperator_error_budget dom hW hθ hD hf hη hM
    N hN lam hlam hz.symm.le hb hbf hbN).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hbound _ (by simp [CepsCanonDomain.positivePairErrorConstants])) (pow_nonneg hb.le _))
        (pow_nonneg hX _))
  exact ⟨hO, hOh, hCE', hOhE⟩

end PGM
