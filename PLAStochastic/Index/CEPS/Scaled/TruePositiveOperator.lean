import PLAStochastic.Index.CEPS.Scaled.TruePositiveEntranceDecay

/-! # Both time-operator terms after actual half-line subtraction -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def cepsScaledTimeOperator (lam b : ℝ) (U : ℂ → ℂ) (z : ℂ) : ℂ :=
  -(1 / (1 + (b : ℂ) * lam)) * deriv U z - (b : ℂ) * U z

def CepsCanonDomain.truePositiveOperatorConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (M : ℝ) : ℝ :=
  2 * dom.truePositiveDerivativeConstant M + dom.trueBridgeWeightedConstant M

def CepsCanonDomain.trueHalfOperatorConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) : ℝ :=
  4 * dom.trueHalfFrequencyConstant / dom.positiveFrequencyRadius + dom.trueHalfFrequencyConstant

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrueBridgeCorrection_deriv_frequency (M lam : ℝ) (hlam : 1 ≤ lam)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z)) :
    deriv (fun ζ => cepsScaledTrueBridgeCorrection dom ρW lam ζ b) z =
      deriv (fun ζ => cepsScaledTrueBridge dom ρW lam ζ b) z -
        deriv (fun ζ => cepsScaledTrueHalfBridge dom ρW lam ζ b) z := by
  have ht := cepsScaledTrueBridge_differentiableOn_frequency_disc dom hW hθ hD M lam hz hb hbs
  have hh := cepsScaledTrueHalfBridge_positive_frequency_differentiableOn dom hW hθ hD M lam hlam hz hb hbs
  exact deriv_sub ((ht z (mem_ball_self (scaledFrequencyRadius_pos dom hD))).differentiableAt
    (ball_mem_nhds z (scaledFrequencyRadius_pos dom hD)))
    ((hh z (mem_ball_self (positiveFrequencyRadius_pos dom hW hθ hD))).differentiableAt
      (ball_mem_nhds z (positiveFrequencyRadius_pos dom hW hθ hD)))

include hW hθ hD in
theorem cepsScaledTrue_timeOperator_sub (M lam : ℝ) (hlam : 1 ≤ lam)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z)) :
    cepsScaledTimeOperator lam b (fun ζ => cepsScaledTrueBridge dom ρW lam ζ b) z -
      cepsScaledTimeOperator lam b (fun ζ => cepsScaledTrueHalfBridge dom ρW lam ζ b) z =
        cepsScaledTimeOperator lam b (fun ζ => cepsScaledTrueBridgeCorrection dom ρW lam ζ b) z := by
  unfold cepsScaledTimeOperator
  rw [cepsScaledTrueBridgeCorrection_deriv_frequency dom hW hθ hD M lam hlam hz hb hbs]
  unfold cepsScaledTrueBridgeCorrection
  ring

include hW hθ hD in
theorem cepsScaledTrueBridgeCorrection_timeOperator_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m) (lam : ℝ) (hlam : 1 ≤ lam)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDecayScaleRadius M lam z)) :
    ‖cepsScaledTimeOperator lam b (fun ζ => cepsScaledTrueBridgeCorrection dom ρW lam ζ b) z‖ ≤
      dom.truePositiveOperatorConstant M * (1 + |lam| + Real.sqrt ‖z‖) *
        Real.exp (-(dom.positiveBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) / 2) := by
  have hbf := ball_subset_ball (trueDecayScaleRadius_le_frequency dom M lam z) hbs
  have hbd := ball_subset_ball ((trueFrequencyScaleRadius_le dom M lam z).trans
    (truePairScaleRadius_le dom M lam z)) hbf
  obtain ⟨hb1, hw1⟩ := cepsScaledTrueFrequency_scale_width_budget dom hW hθ hD M lam hz hb hbf
  have hd := cepsScaledTrueBridgeCorrection_positive_frequency_derivative_budget dom hW hθ hD
    hf hη hM hm lam hlam hz hb hbs
  have hU := cepsScaledTrueBridgeCorrection_positive_polynomial_budget dom hW hθ hD
    hf hη hM hm lam (by linarith) hz hbd
  have hc := (positiveBridgePolynomial_constants dom hW hθ hD 0 M).2
  have hK : 0 ≤ dom.trueBridgeWeightedConstant M := by
    have := surrogateSlopePolynomialConstant_pos dom hW hθ hD 0 M
    unfold CepsCanonDomain.trueBridgeWeightedConstant
    positivity
  have hE : Real.exp (-dom.positiveBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) ≤
      Real.exp (-(dom.positiveBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) / 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.sqrt_nonneg ‖z‖, abs_nonneg lam]
  have hU' := hU.trans (mul_le_mul_of_nonneg_left hE (by positivity))
  unfold cepsScaledTimeOperator
  apply (norm_sub_le _ _).trans
  rw [norm_mul, norm_neg, norm_mul]
  exact (add_le_add (mul_le_mul hw1 hd (norm_nonneg _) (by norm_num))
    (mul_le_mul hb1 hU' (norm_nonneg _) (by norm_num))).trans_eq
      (by unfold CepsCanonDomain.truePositiveOperatorConstant; ring)

include hW hθ hD in
theorem cepsScaledTrueHalfBridge_timeOperator_budget (M lam : ℝ) (hlam : 1 ≤ lam)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z)) :
    ‖cepsScaledTimeOperator lam b (fun ζ => cepsScaledTrueHalfBridge dom ρW lam ζ b) z‖ ≤
      dom.trueHalfOperatorConstant * (1 + |lam| + Real.sqrt ‖z‖) := by
  obtain ⟨hb1, hw1⟩ := cepsScaledTrueFrequency_scale_width_budget dom hW hθ hD M lam hz hb hbs
  have hd := cepsScaledTrueHalfBridge_positive_frequency_derivative_budget dom hW hθ hD M lam hlam hz hb hbs
  have hU := cepsScaledTrueHalfBridge_frequency_budget dom hW hθ hD M lam hz hb hbs
    (mem_ball_self (scaledFrequencyRadius_pos dom hD))
  unfold cepsScaledTimeOperator
  apply (norm_sub_le _ _).trans
  rw [norm_mul, norm_neg, norm_mul]
  exact (add_le_add (mul_le_mul hw1 hd (norm_nonneg _) (by norm_num))
    (mul_le_mul hb1 hU (norm_nonneg _) (by norm_num))).trans_eq
      (by unfold CepsCanonDomain.trueHalfOperatorConstant; ring)

end PGM
