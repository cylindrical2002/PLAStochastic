import PLAStochastic.Index.CEPS.Scaled.TrueImaginaryEntrance
import PLAStochastic.Index.CEPS.Scaled.TruePairScaling
import PLAStochastic.Index.CEPS.Scaled.BridgePolynomialTaylor

/-! # The complete actual negative-drift pair has an integrable envelope -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.trueNegativePairConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (M : ℝ) : ℝ :=
  (3 * dom.trueEntranceWeightedConstant M) ^ 2 *
    (2 * dom.trueNegativeDerivativeConstant M + dom.trueBridgeWeightedConstant M)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrueBridge_negative_timeOperator_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m) (lam : ℝ) (hlam : lam ≤ 0)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDecayScaleRadius M lam z)) :
    ‖-(1 / (1 + (b : ℂ) * lam)) * deriv (fun ζ => cepsScaledTrueBridge dom ρW lam ζ b) z -
        (b : ℂ) * cepsScaledTrueBridge dom ρW lam z b‖ ≤
      (2 * dom.trueNegativeDerivativeConstant M + dom.trueBridgeWeightedConstant M) *
        (1 + |lam| + Real.sqrt ‖z‖) *
          Real.exp (-(dom.negativeBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) / 2) := by
  have hbf := ball_subset_ball (trueDecayScaleRadius_le_frequency dom M lam z) hbs
  have hbd := ball_subset_ball ((trueFrequencyScaleRadius_le dom M lam z).trans
    (truePairScaleRadius_le dom M lam z)) hbf
  obtain ⟨hb1, hw1⟩ := cepsScaledTrueFrequency_scale_width_budget dom hW hθ hD M lam hz hb hbf
  have hd := cepsScaledTrueBridge_negative_frequency_derivative_budget dom hW hθ hD
    hf hη hM hm lam hlam hz hb hbs
  have hU := cepsScaledTrueBridge_negative_polynomial_budget dom hW hθ hD
    hf hη hM hm lam hlam hz hbd
  have hc := (negativeBridgePolynomial_constants dom hW hθ hD 0 M).2
  have hK : 0 ≤ dom.trueBridgeWeightedConstant M := by
    have := surrogateSlopePolynomialConstant_pos dom hW hθ hD 0 M
    unfold CepsCanonDomain.trueBridgeWeightedConstant
    positivity
  have hE : Real.exp (-dom.negativeBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) ≤
      Real.exp (-(dom.negativeBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) / 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.sqrt_nonneg ‖z‖, abs_nonneg lam]
  have hU' := hU.trans (mul_le_mul_of_nonneg_left hE (by positivity))
  calc
    _ ≤ ‖-(1 / (1 + (b : ℂ) * lam)) * deriv (fun ζ => cepsScaledTrueBridge dom ρW lam ζ b) z‖ +
        ‖(b : ℂ) * cepsScaledTrueBridge dom ρW lam z b‖ := norm_sub_le _ _
    _ = ‖(1 / (1 + (b : ℂ) * lam) : ℂ)‖ *
        ‖deriv (fun ζ => cepsScaledTrueBridge dom ρW lam ζ b) z‖ +
          ‖(b : ℂ)‖ * ‖cepsScaledTrueBridge dom ρW lam z b‖ := by rw [norm_mul, norm_neg, norm_mul]
    _ ≤ 2 * (dom.trueNegativeDerivativeConstant M * (1 + |lam| + Real.sqrt ‖z‖) *
        Real.exp (-(dom.negativeBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) / 2)) +
          1 * (dom.trueBridgeWeightedConstant M * (1 + |lam| + Real.sqrt ‖z‖) *
            Real.exp (-(dom.negativeBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) / 2)) :=
      add_le_add (mul_le_mul hw1 hd (norm_nonneg _) (by norm_num))
        (mul_le_mul hb1 hU' (norm_nonneg _) (by norm_num))
    _ = _ := by ring

include hW hθ hD in
theorem cepsScaledTruePair_negative_polynomial_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m) (lam : ℝ) (hlam : lam ≤ 0)
    {z : ℂ} (hz : z.re = 0) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDecayScaleRadius M lam z)) :
    ‖cepsScaledTruePair dom ρW lam z b‖ ≤ dom.trueNegativePairConstant M *
      (1 + |lam| + Real.sqrt ‖z‖) ^ 3 *
        Real.exp (-(dom.negativeBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) / 2) := by
  have hbf := ball_subset_ball (trueDecayScaleRadius_le_frequency dom M lam z) hbs
  have hH := cepsScaledTrueEntrance_imaginary_budget dom hW hθ hD hf hη hM hm lam hz hb hbf
  have hO := cepsScaledTrueBridge_negative_timeOperator_budget dom hW hθ hD
    hf hη hM hm lam hlam hz.symm.le hb hbs
  have hK := trueNegativeDerivativeConstant_pos dom hW hθ hD M
  have hU : 0 ≤ dom.trueBridgeWeightedConstant M := by
    have := surrogateSlopePolynomialConstant_pos dom hW hθ hD 0 M
    unfold CepsCanonDomain.trueBridgeWeightedConstant
    positivity
  have hH0 : 0 ≤ (3 * dom.trueEntranceWeightedConstant M) * (1 + |lam| + Real.sqrt ‖z‖) :=
    (norm_nonneg _).trans hH
  unfold cepsScaledTruePair
  rw [norm_mul, norm_mul, norm_pow, cepsScaledMarker_exp_norm_imaginary lam b hz, one_mul]
  exact (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hH 2) hO (norm_nonneg _)
    (by positivity)).trans_eq (by unfold CepsCanonDomain.trueNegativePairConstant; ring)

include hW hθ hD in
theorem cepsScaledTruePair_negative_envelope_integrable (M : ℝ) (z : ℂ) :
    Integrable (fun lam : ℝ => dom.trueNegativePairConstant M *
      (1 + |lam| + Real.sqrt ‖z‖) ^ 3 *
        Real.exp (-(dom.negativeBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) / 2)) := by
  have hc := (negativeBridgePolynomial_constants dom hW hθ hD 0 M).2
  simpa only [neg_mul, neg_div, div_mul_eq_mul_div] using
    cepsBridge_polynomialEnvelope_integrable 3 (half_pos hc) (dom.trueNegativePairConstant M) z

end PGM
