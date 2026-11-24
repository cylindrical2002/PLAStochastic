import PLAStochastic.Index.CEPS.Scaled.TruePositivePair
import PLAStochastic.Index.CEPS.Scaled.TrueCentralPair

/-! # A single integrable envelope for the actual subtracted pair

The physical scale disc is fixed before the Taylor order. Half-line
subtraction is used on the positive tail, where its lower-root pole is
uniformly separated from the marker. The complete time operator is retained.
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def cepsScaledTrueSubtractedPair {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (lam : ℝ) (z : ℂ) (b : ℝ) : ℂ :=
  if 1 ≤ lam then cepsScaledTruePair dom ρW lam z b - cepsScaledTrueHalfPair dom ρW lam z b
  else cepsScaledTruePair dom ρW lam z b

def CepsCanonDomain.trueSubtractedPairConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (M : ℝ) : ℝ :=
  |dom.trueNegativePairConstant M| + |dom.trueCentralPairConstant M| + |dom.truePositivePairConstant M|

private theorem envelope_weaken {u : ℂ} {K K' X F c d : ℝ}
    (hX : 0 ≤ X) (hF : 0 ≤ F) (hc : c ≤ d) (hK : |K| ≤ K')
    (hu : ‖u‖ ≤ K * X ^ 3 * Real.exp (-d * F)) :
    ‖u‖ ≤ K' * X ^ 3 * Real.exp (-c * F) := by
  have hE : Real.exp (-d * F) ≤ Real.exp (-c * F) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hc hF]
  calc
    _ ≤ |K| * X ^ 3 * Real.exp (-d * F) := hu.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity))
        (Real.exp_pos _).le)
    _ ≤ |K| * X ^ 3 * Real.exp (-c * F) := mul_le_mul_of_nonneg_left hE (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK (by positivity))
      (Real.exp_pos _).le

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrueSubtractedPair_polynomial_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m) (lam : ℝ)
    {z : ℂ} (hz : z.re = 0) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDecayScaleRadius M lam z)) :
    ‖cepsScaledTrueSubtractedPair dom ρW lam z b‖ ≤ dom.trueSubtractedPairConstant M *
      (1 + |lam| + Real.sqrt ‖z‖) ^ 3 *
        Real.exp (-(dom.positiveBridgeDecayRate / 2) * (|lam| + Real.sqrt ‖z‖)) := by
  have hc := (positiveBridgePolynomial_constants dom hW hθ hD 0 M).2
  have hr : dom.negativeBridgeDecayRate = 2 * dom.positiveBridgeDecayRate := by
    unfold CepsCanonDomain.negativeBridgeDecayRate CepsCanonDomain.positiveBridgeDecayRate
    ring
  have hrate : dom.positiveBridgeDecayRate / 2 ≤ dom.negativeBridgeDecayRate / 2 := by
    rw [hr]; linarith
  have hKn : |dom.trueNegativePairConstant M| ≤ dom.trueSubtractedPairConstant M := by
    unfold CepsCanonDomain.trueSubtractedPairConstant
    linarith [abs_nonneg (dom.trueCentralPairConstant M), abs_nonneg (dom.truePositivePairConstant M)]
  have hKc : |dom.trueCentralPairConstant M| ≤ dom.trueSubtractedPairConstant M := by
    unfold CepsCanonDomain.trueSubtractedPairConstant
    linarith [abs_nonneg (dom.trueNegativePairConstant M), abs_nonneg (dom.truePositivePairConstant M)]
  have hKp : |dom.truePositivePairConstant M| ≤ dom.trueSubtractedPairConstant M := by
    unfold CepsCanonDomain.trueSubtractedPairConstant
    linarith [abs_nonneg (dom.trueNegativePairConstant M), abs_nonneg (dom.trueCentralPairConstant M)]
  unfold cepsScaledTrueSubtractedPair
  split_ifs with hlam
  · have hu := cepsScaledTruePair_positive_polynomial_budget dom hW hθ hD hf hη hM hm lam hlam hz hb hbs
    apply envelope_weaken (by positivity) (by positivity) le_rfl hKp
    simpa only [neg_mul, neg_div, div_mul_eq_mul_div] using hu
  · by_cases hneg : lam ≤ 0
    · have hu := cepsScaledTruePair_negative_polynomial_budget dom hW hθ hD hf hη hM hm lam hneg hz hb hbs
      apply envelope_weaken (by positivity) (by positivity) hrate hKn
      simpa only [neg_mul, neg_div, div_mul_eq_mul_div] using hu
    · have habs : |lam| ≤ 1 := by rw [abs_of_pos (lt_of_not_ge hneg)]; exact (lt_of_not_ge hlam).le
      have hu := cepsScaledTruePair_central_polynomial_budget dom hW hθ hD hf hη hM hm lam habs hz hb hbs
      apply envelope_weaken (by positivity) (by positivity) hrate hKc
      simpa only [neg_mul, neg_div, div_mul_eq_mul_div] using hu

include hW hθ hD in
theorem cepsScaledTrueSubtractedPair_envelope_integrable (M : ℝ) (z : ℂ) :
    Integrable (fun lam : ℝ => dom.trueSubtractedPairConstant M *
      (1 + |lam| + Real.sqrt ‖z‖) ^ 3 *
        Real.exp (-(dom.positiveBridgeDecayRate / 2) * (|lam| + Real.sqrt ‖z‖))) :=
  cepsBridge_polynomialEnvelope_integrable 3
    (half_pos (positiveBridgePolynomial_constants dom hW hθ hD 0 M).2)
    (dom.trueSubtractedPairConstant M) z

end PGM
