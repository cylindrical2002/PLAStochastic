import PLAStochastic.Index.CEPS.Scaled.FrequencyShift

/-! # Actual negative-drift frequency derivative decay

Rightward differences preserve the closed right half-plane. A scale-uniform
complex-disc bound controls their Taylor remainder, retaining exponential
decay at imaginary-axis points and at root mergers.
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.trueNegativeShiftConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (M : ℝ) : ℝ :=
  dom.trueBridgeWeightedConstant M * dom.frequencyShiftFactor *
    Real.exp (dom.negativeBridgeDecayRate * Real.sqrt dom.scaledFrequencyRadius)

def CepsCanonDomain.trueNegativeDerivativeConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (M : ℝ) : ℝ :=
  8 * (dom.trueNegativeShiftConstant M + dom.trueFrequencyBridgeConstant) /
    dom.scaledFrequencyRadius

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem trueNegativeDerivativeConstant_pos (M : ℝ) :
    0 < dom.trueNegativeDerivativeConstant M := by
  have hK := surrogateSlopePolynomialConstant_pos dom hW hθ hD 0 M
  have hF := frequencyShiftFactor_pos dom
  have hC := trueFrequencyBridgeConstant_pos dom hW hθ hD
  have hR := scaledFrequencyRadius_pos dom hD
  unfold CepsCanonDomain.trueNegativeDerivativeConstant CepsCanonDomain.trueNegativeShiftConstant
    CepsCanonDomain.trueBridgeWeightedConstant
  positivity

include hW hθ hD in
theorem cepsScaledTrueBridge_negative_right_values {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m) (lam : ℝ) (hlam : lam ≤ 0)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDecayScaleRadius M lam z))
    {s : ℝ} (hs : s ∈ Icc 0 (dom.scaledFrequencyRadius / 4)) :
    ‖cepsScaledTrueBridge dom ρW lam (z + (s : ℂ)) b‖ ≤
      dom.trueNegativeShiftConstant M * (1 + |lam| + Real.sqrt ‖z‖) *
        Real.exp (-dom.negativeBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) := by
  have hz' : 0 ≤ (z + (s : ℂ)).re := by simp only [add_re, ofReal_re]; linarith [hs.1]
  have hbs := cepsScaledTrueDecay_shift_mem_denominator dom hD M lam z hb hs
  have hn := cepsScaledTrueBridge_negative_polynomial_budget dom hW hθ hD hf hη hM hm
    lam hlam hz' hbs
  have hK : 0 ≤ dom.trueBridgeWeightedConstant M := by
    unfold CepsCanonDomain.trueBridgeWeightedConstant
    have := surrogateSlopePolynomialConstant_pos dom hW hθ hD 0 M
    positivity
  have hc := (negativeBridgePolynomial_constants dom hW hθ hD 0 M).2
  have hr := (cepsFrequency_sqrt_shift dom hD (z := z) hs).2
  have he : Real.exp (-dom.negativeBridgeDecayRate * (|lam| + Real.sqrt ‖z + (s : ℂ)‖)) ≤
      Real.exp (dom.negativeBridgeDecayRate * Real.sqrt dom.scaledFrequencyRadius) *
        Real.exp (-dom.negativeBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  apply hn.trans
  calc
    _ ≤ (dom.trueBridgeWeightedConstant M *
        (dom.frequencyShiftFactor * (1 + |lam| + Real.sqrt ‖z‖))) *
        (Real.exp (dom.negativeBridgeDecayRate * Real.sqrt dom.scaledFrequencyRadius) *
          Real.exp (-dom.negativeBridgeDecayRate * (|lam| + Real.sqrt ‖z‖))) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (cepsFrequency_polynomial_shift dom hD lam z hs) hK
      · exact he
      · exact (Real.exp_pos _).le
      · have := frequencyShiftFactor_pos dom
        positivity
    _ = _ := by unfold CepsCanonDomain.trueNegativeShiftConstant; ring

include hW hθ hD in
theorem cepsScaledTrueBridge_negative_frequency_derivative_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m) (lam : ℝ) (hlam : lam ≤ 0)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDecayScaleRadius M lam z)) :
    ‖deriv (fun ζ => cepsScaledTrueBridge dom ρW lam ζ b) z‖ ≤
      dom.trueNegativeDerivativeConstant M * (1 + |lam| + Real.sqrt ‖z‖) *
        Real.exp (-(dom.negativeBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) / 2) := by
  have hbf := ball_subset_ball (trueDecayScaleRadius_le_frequency dom M lam z) hbs
  have hc := (negativeBridgePolynomial_constants dom hW hθ hD 0 M).2
  have hn := norm_deriv_le_decay_of_disc_and_right_values
    (A := dom.trueNegativeShiftConstant M * (1 + |lam| + Real.sqrt ‖z‖))
    (scaledFrequencyRadius_pos dom hD)
    (mul_nonneg hc.le (by positivity : 0 ≤ |lam| + Real.sqrt ‖z‖))
    (cepsScaledTrueBridge_differentiableOn_frequency_disc dom hW hθ hD M lam hz hb hbf)
    (fun ζ hζ => cepsScaledTrueBridge_frequency_disc_budget dom hW hθ hD M lam hz hb hbf hζ)
    (fun s hs => by simpa only [neg_mul] using
      cepsScaledTrueBridge_negative_right_values dom hW hθ hD hf hη hM hm lam hlam hz hbs hs)
  exact hn.trans_eq (by unfold CepsCanonDomain.trueNegativeDerivativeConstant; ring)

end PGM
