import PLAStochastic.Index.CEPS.Scaled.PositivePairOperatorProfile

/-! # Complete positive-tail actual-minus-surrogate pair error -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def cepsScaledSurrogateHalfPair {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (N : ℕ) (lam : ℝ) (z b : ℂ) : ℂ :=
  exp ((b * z) * (1 + b * lam)) * (cepsScaledSurrogateHalfEntrance dom ρW N lam z b) ^ 2 *
    (-(1 / (1 + b * lam)) * deriv (fun ζ => cepsScaledSurrogateHalfBridge dom ρW N lam ζ b) z -
      b * cepsScaledSurrogateHalfBridge dom ρW N lam z b)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTruePair_positive_error_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 3 ≤ m)
    (lam : ℝ) (hlam : 1 ≤ lam) {z : ℂ} (hz : z.re = 0) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDecayScaleRadius M lam z))
    (hbN : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius (N + 1) M lam z)) :
    ‖(cepsScaledTruePair dom ρW lam z b - cepsScaledTrueHalfPair dom ρW lam z b) -
      (cepsScaledSurrogatePair dom ρW (N + 1) lam z b - cepsScaledSurrogateHalfPair dom ρW (N + 1) lam z b)‖ ≤
        (6 * dom.positivePairComparisonConstant (N + 1) M ^ 3) * b ^ (N + 2) *
          (1 + |lam| + Real.sqrt ‖z‖) ^ (N + 5) *
            Real.exp (-(dom.positiveBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) / 2) := by
  let L := dom.positivePairComparisonConstant (N + 1) M
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let beta := b ^ (N + 2)
  let E := Real.exp (-(dom.positiveBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) / 2)
  let H := cepsScaledTrueEntrance dom ρW lam z b
  let h := cepsScaledSurrogateEntrance dom ρW (N + 1) lam z b
  let Hh := cepsScaledTrueHalfEntrance dom ρW lam z b
  let hh := cepsScaledSurrogateHalfEntrance dom ρW (N + 1) lam z b
  let O := cepsScaledTimeOperator lam b (fun ζ => cepsScaledTrueBridge dom ρW lam ζ b) z
  let o := cepsScaledTimeOperator lam b (fun ζ => cepsScaledSurrogateBridge dom ρW (N + 1) lam ζ b) z
  let Oc := cepsScaledTimeOperator lam b (fun ζ => cepsScaledTrueBridgeCorrection dom ρW lam ζ b) z
  let oc := cepsScaledTimeOperator lam b (fun ζ => cepsScaledSurrogateBridgeCorrection dom ρW (N + 1) lam ζ b) z
  let Oh := cepsScaledTimeOperator lam b (fun ζ => cepsScaledTrueHalfBridge dom ρW lam ζ b) z
  let oh := cepsScaledTimeOperator lam b (fun ζ => cepsScaledSurrogateHalfBridge dom ρW (N + 1) lam ζ b) z
  let Em := exp (((b : ℂ) * z) * (1 + (b : ℂ) * lam))
  have hbf := ball_subset_ball (trueDecayScaleRadius_le_frequency dom M lam z) hbs
  obtain ⟨hH, hh0, hPlus, hplus, hcorr, hHE, hPlusE, hCorrE⟩ :=
    cepsScaledPositivePair_entrance_error_profile dom hW hθ hD hf hη hM N hN lam hlam hz hb hbf hbN
  obtain ⟨hOc, hOh, hOcE, hOhE⟩ := cepsScaledPositivePair_operator_error_profile dom hW hθ hD hf hη hM N hN lam hlam hz hb hbs hbN
  have h1 : ‖H ^ 2 * Oc - h ^ 2 * oc‖ ≤ 3 * L ^ 3 * beta * X ^ (N + 5) * E :=
    (cepsNorm_square_product_taylor_error_le N hH hh0 hHE hOc hOcE).trans_eq (by ring)
  have h2 : ‖(H - Hh) * (H + Hh) * Oh - (h - hh) * (h + hh) * oh‖ ≤
      3 * L ^ 3 * beta * X ^ (N + 5) * E :=
    cepsNorm_three_factor_taylor_error_le N hPlus hOh hcorr hplus hCorrE hPlusE hOhE
  have ht : O - Oh = Oc := cepsScaledTrue_timeOperator_sub dom hW hθ hD M lam hlam hz.symm.le hb hbf
  have hs : o - oh = oc := cepsScaledSurrogate_timeOperator_sub dom hW hθ hD hf hη hM (N + 1)
    (by omega) lam (by linarith) hz.symm.le hb hbf hbN
  have heq : (cepsScaledTruePair dom ρW lam z b - cepsScaledTrueHalfPair dom ρW lam z b) -
      (cepsScaledSurrogatePair dom ρW (N + 1) lam z b - cepsScaledSurrogateHalfPair dom ρW (N + 1) lam z b) =
      Em * ((H ^ 2 * Oc - h ^ 2 * oc) +
        ((H - Hh) * (H + Hh) * Oh - (h - hh) * (h + hh) * oh)) := by
    unfold cepsScaledTruePair cepsScaledTrueHalfPair cepsScaledSurrogatePair cepsScaledSurrogateHalfPair
    change (Em * H ^ 2 * O - Em * Hh ^ 2 * Oh) - (Em * h ^ 2 * o - Em * hh ^ 2 * oh) = _
    linear_combination Em * H ^ 2 * ht - Em * h ^ 2 * hs
  rw [heq, norm_mul]
  have hEm : ‖Em‖ = 1 := cepsScaledMarker_exp_norm_imaginary lam b hz
  rw [hEm, one_mul]
  exact ((norm_add_le _ _).trans (add_le_add h1 h2)).trans_eq (by ring)

include hW hθ hD in
theorem cepsScaledTruePair_positive_error_envelope_integrable (N : ℕ) (M b : ℝ) (z : ℂ) :
    Integrable (fun lam : ℝ => (6 * dom.positivePairComparisonConstant (N + 1) M ^ 3) * b ^ (N + 2) *
      (1 + |lam| + Real.sqrt ‖z‖) ^ (N + 5) *
        Real.exp (-(dom.positiveBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) / 2)) := by
  have hc := (positiveBridgePolynomial_constants dom hW hθ hD 0 M).2
  simpa only [neg_mul, neg_div, div_mul_eq_mul_div] using
    cepsBridge_polynomialEnvelope_integrable (N + 5) (half_pos hc)
      ((6 * dom.positivePairComparisonConstant (N + 1) M ^ 3) * b ^ (N + 2)) z

end PGM
