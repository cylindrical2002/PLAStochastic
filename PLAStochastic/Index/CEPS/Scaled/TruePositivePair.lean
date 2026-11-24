import PLAStochastic.Index.CEPS.Scaled.TruePositiveOperator

/-! # Complete actual positive-tail pair subtraction and integrable decay -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def cepsScaledTrueHalfPair {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (lam : ℝ) (z : ℂ) (b : ℝ) : ℂ :=
  exp (((b : ℂ) * z) * (1 + (b : ℂ) * lam)) * (cepsScaledTrueHalfEntrance dom ρW lam z b) ^ 2 *
    cepsScaledTimeOperator lam b (fun ζ => cepsScaledTrueHalfBridge dom ρW lam ζ b) z

def CepsCanonDomain.truePositivePairConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (M : ℝ) : ℝ :=
  (3 * dom.trueEntranceWeightedConstant M) ^ 2 * dom.truePositiveOperatorConstant M +
    (2 * dom.trueEntranceCorrectionConstant M) *
      (3 * dom.trueEntranceWeightedConstant M + dom.trueHalfEntranceConstant) * dom.trueHalfOperatorConstant

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTruePair_positive_polynomial_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m) (lam : ℝ) (hlam : 1 ≤ lam)
    {z : ℂ} (hz : z.re = 0) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDecayScaleRadius M lam z)) :
    ‖cepsScaledTruePair dom ρW lam z b - cepsScaledTrueHalfPair dom ρW lam z b‖ ≤
      dom.truePositivePairConstant M * (1 + |lam| + Real.sqrt ‖z‖) ^ 3 *
        Real.exp (-(dom.positiveBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) / 2) := by
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let F := |lam| + Real.sqrt ‖z‖
  let H := cepsScaledTrueEntrance dom ρW lam z b
  let Hh := cepsScaledTrueHalfEntrance dom ρW lam z b
  let O := cepsScaledTimeOperator lam b (fun ζ => cepsScaledTrueBridge dom ρW lam ζ b) z
  let Oh := cepsScaledTimeOperator lam b (fun ζ => cepsScaledTrueHalfBridge dom ρW lam ζ b) z
  let E := exp (((b : ℂ) * z) * (1 + (b : ℂ) * lam))
  let A := 3 * dom.trueEntranceWeightedConstant M
  let Ah := dom.trueHalfEntranceConstant
  let Ac := 2 * dom.trueEntranceCorrectionConstant M
  let Ao := dom.truePositiveOperatorConstant M
  let Aoh := dom.trueHalfOperatorConstant
  let e := Real.exp (-(dom.positiveBridgeDecayRate * F) / 2)
  have hz0 : 0 ≤ z.re := hz.symm.le
  have hbf := ball_subset_ball (trueDecayScaleRadius_le_frequency dom M lam z) hbs
  have hbd := ball_subset_ball ((trueFrequencyScaleRadius_le dom M lam z).trans
    (truePairScaleRadius_le dom M lam z)) hbf
  have hH : ‖H‖ ≤ A * X := cepsScaledTrueEntrance_imaginary_budget dom hW hθ hD
    hf hη hM hm lam hz hb hbf
  have hHalf : ‖Hh‖ ≤ Ah := cepsScaledTrueHalfEntrance_positive_budget dom hW hθ hD M lam hlam hz0 hbd
  have hCorr := cepsScaledTrueEntranceCorrection_positive_imaginary_budget dom hW hθ hD
    hf hη hM hm lam hlam hz hb hbf
  have hOc : ‖O - Oh‖ ≤ Ao * X * e := by
    dsimp only [O, Oh]
    rw [cepsScaledTrue_timeOperator_sub dom hW hθ hD M lam hlam hz0 hb hbf]
    exact cepsScaledTrueBridgeCorrection_timeOperator_budget dom hW hθ hD hf hη hM hm lam hlam hz0 hb hbs
  have hOh : ‖Oh‖ ≤ Aoh * X := cepsScaledTrueHalfBridge_timeOperator_budget dom hW hθ hD M lam hlam hz0 hb hbf
  have hX : 1 ≤ X := by dsimp [X]; linarith [abs_nonneg lam, Real.sqrt_nonneg ‖z‖]
  have hAh := (trueHalfEntranceConstant_pos dom hW hθ hD).le
  have hAc := trueEntranceCorrectionConstant_nonneg dom hW hθ hD ((cepsSobolev_nonneg m η fW).trans hM)
  have hAo : 0 ≤ Ao := by
    have := truePositiveDerivativeConstant_pos dom hW hθ hD M
    have := surrogateSlopePolynomialConstant_pos dom hW hθ hD 0 M
    dsimp [Ao, CepsCanonDomain.truePositiveOperatorConstant, CepsCanonDomain.trueBridgeWeightedConstant]
    positivity
  have hAoh : 0 ≤ Aoh := by
    have := trueHalfFrequencyConstant_pos dom hW hθ hD
    have := positiveFrequencyRadius_pos dom hW hθ hD
    dsimp [Aoh, CepsCanonDomain.trueHalfOperatorConstant]
    positivity
  have he : Real.exp (-dom.negativeBridgeDecayRate * F) ≤ e := by
    have hc := (positiveBridgePolynomial_constants dom hW hθ hD 0 M).2
    have hr : dom.negativeBridgeDecayRate = 2 * dom.positiveBridgeDecayRate := by
      unfold CepsCanonDomain.negativeBridgeDecayRate CepsCanonDomain.positiveBridgeDecayRate
      ring
    apply Real.exp_le_exp.mpr
    rw [hr]
    nlinarith [show 0 ≤ F by dsimp [F]; positivity]
  have hC : ‖H - Hh‖ ≤ Ac * X * e := hCorr.trans
    (mul_le_mul_of_nonneg_left he (by positivity))
  have hs : ‖H + Hh‖ ≤ (A + Ah) * X :=
    (norm_add_le _ _).trans ((add_le_add hH hHalf).trans (by
      have ht := mul_le_mul_of_nonneg_left hX hAh
      change A * X + Ah ≤ (A + Ah) * X
      nlinarith))
  have hAX : 0 ≤ A * X := (norm_nonneg _).trans hH
  have hsX : 0 ≤ (A + Ah) * X := (norm_nonneg _).trans hs
  have h₁ : ‖H ^ 2 * (O - Oh)‖ ≤ (A * X) ^ 2 * (Ao * X * e) := by
    rw [norm_mul, norm_pow]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hH 2) hOc (norm_nonneg _) (sq_nonneg _)
  have h₂ : ‖(H - Hh) * (H + Hh) * Oh‖ ≤ (Ac * X * e) * ((A + Ah) * X) * (Aoh * X) := by
    rw [norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul hC hs (norm_nonneg _) (by dsimp [Ac, X, e]; positivity)) hOh
      (norm_nonneg _) (mul_nonneg (by dsimp [Ac, X, e]; positivity) hsX)
  have heq : H ^ 2 * O - Hh ^ 2 * Oh = H ^ 2 * (O - Oh) + (H - Hh) * (H + Hh) * Oh := by ring
  change ‖E * H ^ 2 * O - E * Hh ^ 2 * Oh‖ ≤ _
  rw [mul_assoc E (H ^ 2) O, mul_assoc E (Hh ^ 2) Oh, ← mul_sub, norm_mul]
  have hEn : ‖E‖ = 1 := cepsScaledMarker_exp_norm_imaginary lam b hz
  rw [hEn, one_mul, heq]
  exact ((norm_add_le _ _).trans (add_le_add h₁ h₂)).trans_eq (by
    unfold CepsCanonDomain.truePositivePairConstant
    dsimp [A, Ac, Ah, Ao, Aoh, X, F, e]
    ring)

include hW hθ hD in
theorem cepsScaledTruePair_positive_envelope_integrable (M : ℝ) (z : ℂ) :
    Integrable (fun lam : ℝ => dom.truePositivePairConstant M *
      (1 + |lam| + Real.sqrt ‖z‖) ^ 3 *
        Real.exp (-(dom.positiveBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) / 2)) := by
  have hc := (positiveBridgePolynomial_constants dom hW hθ hD 0 M).2
  simpa only [neg_mul, neg_div, div_mul_eq_mul_div] using
    cepsBridge_polynomialEnvelope_integrable 3 (half_pos hc) (dom.truePositivePairConstant M) z

end PGM
