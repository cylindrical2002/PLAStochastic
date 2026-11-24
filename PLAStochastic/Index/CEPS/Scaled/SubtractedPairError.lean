import PLAStochastic.Index.CEPS.Scaled.LeftPairError
import PLAStochastic.Index.CEPS.Scaled.PositivePairError
import PLAStochastic.Index.CEPS.Scaled.TrueSubtractedPair

/-! # All-real-drift complete-pair errors with an integrable Taylor envelope -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def cepsScaledSurrogateSubtractedPair {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (N : ℕ) (lam : ℝ) (z b : ℂ) : ℂ :=
  if 1 ≤ lam then cepsScaledSurrogatePair dom ρW N lam z b - cepsScaledSurrogateHalfPair dom ρW N lam z b
  else cepsScaledSurrogatePair dom ρW N lam z b

def CepsCanonDomain.subtractedPairErrorConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  |dom.leftPairErrorConstant N M| + 6 * dom.positivePairComparisonConstant N M ^ 3

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

theorem subtractedPairErrorConstant_pos (N : ℕ) (M : ℝ) : 0 < dom.subtractedPairErrorConstant N M := by
  have := positivePairComparisonConstant_pos dom N M
  unfold CepsCanonDomain.subtractedPairErrorConstant
  positivity

include hW hθ hD in
theorem cepsScaledTrueSubtractedPair_error_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 3 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : z.re = 0) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDecayScaleRadius M lam z))
    (hbN : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius (N + 1) M lam z)) :
    ‖cepsScaledTrueSubtractedPair dom ρW lam z b - cepsScaledSurrogateSubtractedPair dom ρW (N + 1) lam z b‖ ≤
      dom.subtractedPairErrorConstant (N + 1) M * b ^ (N + 2) *
        (1 + |lam| + Real.sqrt ‖z‖) ^ (N + 5) *
          Real.exp (-(dom.positiveBridgeDecayRate / 2) * (|lam| + Real.sqrt ‖z‖)) := by
  have hK := (subtractedPairErrorConstant_pos dom (N + 1) M).le
  have hL := (positivePairComparisonConstant_pos dom (N + 1) M).le
  have hp : 6 * dom.positivePairComparisonConstant (N + 1) M ^ 3 ≤ dom.subtractedPairErrorConstant (N + 1) M :=
    le_add_of_nonneg_left (abs_nonneg _)
  have hl : dom.leftPairErrorConstant (N + 1) M ≤ dom.subtractedPairErrorConstant (N + 1) M :=
    (le_abs_self _).trans (le_add_of_nonneg_right (by positivity))
  unfold cepsScaledTrueSubtractedPair cepsScaledSurrogateSubtractedPair
  split_ifs with hlam
  · have hu := cepsScaledTruePair_positive_error_budget dom hW hθ hD hf hη hM N hN lam hlam hz hb hbs hbN
    apply hu.trans
    have hh : (6 * dom.positivePairComparisonConstant (N + 1) M ^ 3) * b ^ (N + 2) *
        (1 + |lam| + Real.sqrt ‖z‖) ^ (N + 5) *
          Real.exp (-(dom.positiveBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) / 2) ≤
        dom.subtractedPairErrorConstant (N + 1) M * b ^ (N + 2) *
          (1 + |lam| + Real.sqrt ‖z‖) ^ (N + 5) *
            Real.exp (-(dom.positiveBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) / 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hp (pow_nonneg hb.le _)) (by positivity)) (Real.exp_pos _).le
    simpa only [neg_mul, neg_div, div_mul_eq_mul_div] using hh
  · have hu := cepsScaledTruePair_left_error_budget dom hW hθ hD hf hη hM N hN lam
      (lt_of_not_ge hlam).le hz hb hbs hbN
    have hrate : dom.positiveBridgeDecayRate ≤ dom.negativeBridgeDecayRate := by
      have hc := (positiveBridgePolynomial_constants dom hW hθ hD 0 M).2
      have hr : dom.negativeBridgeDecayRate = 2 * dom.positiveBridgeDecayRate := by
        unfold CepsCanonDomain.negativeBridgeDecayRate CepsCanonDomain.positiveBridgeDecayRate
        ring
      rw [hr]
      linarith
    have he : Real.exp (-(dom.negativeBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) / 2) ≤
        Real.exp (-(dom.positiveBridgeDecayRate / 2) * (|lam| + Real.sqrt ‖z‖)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hrate (by positivity : 0 ≤ |lam| + Real.sqrt ‖z‖)]
    exact hu.trans (mul_le_mul
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hl (pow_nonneg hb.le _)) (by positivity))
        he (Real.exp_pos _).le (by positivity))

include hW hθ hD in
theorem cepsScaledTrueSubtractedPair_error_envelope_integrable (N : ℕ) (M b : ℝ) (z : ℂ) :
    Integrable (fun lam : ℝ => dom.subtractedPairErrorConstant (N + 1) M * b ^ (N + 2) *
      (1 + |lam| + Real.sqrt ‖z‖) ^ (N + 5) *
        Real.exp (-(dom.positiveBridgeDecayRate / 2) * (|lam| + Real.sqrt ‖z‖))) :=
  cepsBridge_polynomialEnvelope_integrable (N + 5)
    (half_pos (positiveBridgePolynomial_constants dom hW hθ hD 0 M).2)
    (dom.subtractedPairErrorConstant (N + 1) M * b ^ (N + 2)) z

end PGM
