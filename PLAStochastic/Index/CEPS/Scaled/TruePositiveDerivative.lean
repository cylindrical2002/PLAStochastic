import PLAStochastic.Index.CEPS.Scaled.HalfFrequencyBudget

/-! # Actual positive-drift correction frequency derivative decay

Rightward differences preserve the closed right half-plane. A scale-uniform
complex-disc bound controls their Taylor remainder, retaining exponential
decay at imaginary-axis points on the positive drift tail.
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.truePositiveShiftConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (M : ℝ) : ℝ :=
  dom.trueBridgeWeightedConstant M * dom.frequencyShiftFactor *
    Real.exp (dom.positiveBridgeDecayRate * Real.sqrt dom.scaledFrequencyRadius)

def CepsCanonDomain.truePositiveDerivativeConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (M : ℝ) : ℝ :=
  8 * (dom.truePositiveShiftConstant M + dom.trueCorrectionFrequencyConstant) /
    dom.positiveFrequencyRadius

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem truePositiveDerivativeConstant_pos (M : ℝ) :
    0 < dom.truePositiveDerivativeConstant M := by
  have hK := surrogateSlopePolynomialConstant_pos dom hW hθ hD 0 M
  have hF := frequencyShiftFactor_pos dom
  have hC := trueFrequencyBridgeConstant_pos dom hW hθ hD
  have hH := trueHalfFrequencyConstant_pos dom hW hθ hD
  have hR := positiveFrequencyRadius_pos dom hW hθ hD
  unfold CepsCanonDomain.truePositiveDerivativeConstant CepsCanonDomain.truePositiveShiftConstant
    CepsCanonDomain.trueBridgeWeightedConstant CepsCanonDomain.trueCorrectionFrequencyConstant
  positivity

include hW hθ hD in
theorem cepsScaledTrueBridgeCorrection_positive_right_values {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m) (lam : ℝ) (hlam : 1 ≤ lam)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDecayScaleRadius M lam z))
    {s : ℝ} (hs : s ∈ Icc 0 (dom.positiveFrequencyRadius / 4)) :
    ‖cepsScaledTrueBridgeCorrection dom ρW lam (z + (s : ℂ)) b‖ ≤
      dom.truePositiveShiftConstant M * (1 + |lam| + Real.sqrt ‖z‖) *
        Real.exp (-dom.positiveBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) := by
  have hsδ : s ∈ Icc 0 (dom.scaledFrequencyRadius / 4) :=
    ⟨hs.1, hs.2.trans (div_le_div_of_nonneg_right (positiveFrequencyRadius_le dom) (by norm_num))⟩
  have hz' : 0 ≤ (z + (s : ℂ)).re := by simp only [add_re, ofReal_re]; linarith [hs.1]
  have hbs := cepsScaledTrueDecay_shift_mem_denominator dom hD M lam z hb hsδ
  have hn := cepsScaledTrueBridgeCorrection_positive_polynomial_budget dom hW hθ hD hf hη hM hm
    lam (by linarith) hz' hbs
  have hK : 0 ≤ dom.trueBridgeWeightedConstant M := by
    unfold CepsCanonDomain.trueBridgeWeightedConstant
    have := surrogateSlopePolynomialConstant_pos dom hW hθ hD 0 M
    positivity
  have hc := (positiveBridgePolynomial_constants dom hW hθ hD 0 M).2
  have hr := (cepsFrequency_sqrt_shift dom hD (z := z) hsδ).2
  have he : Real.exp (-dom.positiveBridgeDecayRate * (|lam| + Real.sqrt ‖z + (s : ℂ)‖)) ≤
      Real.exp (dom.positiveBridgeDecayRate * Real.sqrt dom.scaledFrequencyRadius) *
        Real.exp (-dom.positiveBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  apply hn.trans
  calc
    _ ≤ (dom.trueBridgeWeightedConstant M *
        (dom.frequencyShiftFactor * (1 + |lam| + Real.sqrt ‖z‖))) *
        (Real.exp (dom.positiveBridgeDecayRate * Real.sqrt dom.scaledFrequencyRadius) *
          Real.exp (-dom.positiveBridgeDecayRate * (|lam| + Real.sqrt ‖z‖))) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (cepsFrequency_polynomial_shift dom hD lam z hsδ) hK
      · exact he
      · exact (Real.exp_pos _).le
      · have := frequencyShiftFactor_pos dom
        positivity
    _ = _ := by unfold CepsCanonDomain.truePositiveShiftConstant; ring

include hW hθ hD in
theorem cepsScaledTrueBridgeCorrection_positive_frequency_derivative_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m) (lam : ℝ) (hlam : 1 ≤ lam)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDecayScaleRadius M lam z)) :
    ‖deriv (fun ζ => cepsScaledTrueBridgeCorrection dom ρW lam ζ b) z‖ ≤
      dom.truePositiveDerivativeConstant M * (1 + |lam| + Real.sqrt ‖z‖) *
        Real.exp (-(dom.positiveBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) / 2) := by
  have hbf := ball_subset_ball (trueDecayScaleRadius_le_frequency dom M lam z) hbs
  have hc := (positiveBridgePolynomial_constants dom hW hθ hD 0 M).2
  have hn := norm_deriv_le_decay_of_disc_and_right_values
    (A := dom.truePositiveShiftConstant M * (1 + |lam| + Real.sqrt ‖z‖))
    (positiveFrequencyRadius_pos dom hW hθ hD)
    (mul_nonneg hc.le (by positivity : 0 ≤ |lam| + Real.sqrt ‖z‖))
    (cepsScaledTrueBridgeCorrection_positive_frequency_differentiableOn dom hW hθ hD M lam hlam hz hb hbf)
    (fun ζ hζ => cepsScaledTrueBridgeCorrection_frequency_budget dom hW hθ hD M lam hz hb hbf
      (ball_subset_ball (positiveFrequencyRadius_le dom) hζ))
    (fun s hs => by simpa only [neg_mul] using
      cepsScaledTrueBridgeCorrection_positive_right_values dom hW hθ hD hf hη hM hm lam hlam hz hbs hs)
  exact hn.trans_eq (by unfold CepsCanonDomain.truePositiveDerivativeConstant; ring)

end PGM
