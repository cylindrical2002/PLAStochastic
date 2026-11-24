import PLAStochastic.Index.CEPS.Scaled.EntranceImaginaryError
import PLAStochastic.Index.CEPS.Scaled.PairValueErrorBudget
import PLAStochastic.Index.CEPS.Scaled.TrueCentralPair

/-! # Complete actual-minus-surrogate pair errors on the left and central drift ranges -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.leftOperatorConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (M : ℝ) : ℝ :=
  |2 * dom.trueNegativeDerivativeConstant M + dom.trueBridgeWeightedConstant M| +
    |2 * dom.trueCentralDerivativeConstant M + dom.trueCentralBridgeConstant M|

def CepsCanonDomain.leftPairErrorConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  dom.entranceComparisonConstant N M ^ 2 *
    (2 * dom.leftOperatorConstant M + dom.bridgeTimeErrorConstant N M * Real.exp (2 / cepsVarLo D))

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrueBridge_left_timeOperator_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m) (lam : ℝ) (hlam : lam ≤ 1)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDecayScaleRadius M lam z)) :
    ‖cepsScaledTimeOperator lam b (fun ζ => cepsScaledTrueBridge dom ρW lam ζ b) z‖ ≤
      dom.leftOperatorConstant M * (1 + |lam| + Real.sqrt ‖z‖) *
        Real.exp (-(dom.negativeBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) / 2) := by
  by_cases hl : lam ≤ 0
  · have hC : 2 * dom.trueNegativeDerivativeConstant M + dom.trueBridgeWeightedConstant M ≤
        dom.leftOperatorConstant M := (le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))
    exact (cepsScaledTrueBridge_negative_timeOperator_budget dom hW hθ hD hf hη hM hm lam hl hz hb hbs).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (by positivity)) (Real.exp_pos _).le)
  · have hla : |lam| ≤ 1 := by rw [abs_of_pos (lt_of_not_ge hl)]; exact hlam
    have hC : 2 * dom.trueCentralDerivativeConstant M + dom.trueCentralBridgeConstant M ≤
        dom.leftOperatorConstant M := (le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))
    exact (cepsScaledTrueBridge_central_timeOperator_budget dom hW hθ hD hf hη hM hm lam hla hz hb hbs).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (by positivity)) (Real.exp_pos _).le)

include hW hθ hD in
theorem cepsScaledRootPlus_left_exp_polynomial (M lam : ℝ) (hlam : lam ≤ 1)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z)) :
    Real.exp (-(cepsScaledSignedRoot D θ ρW lam z 1 b * (1 + (b : ℂ) * lam)).re) ≤
      Real.exp (2 / cepsVarLo D) *
        Real.exp (-(dom.negativeBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) / 2) := by
  have hbD := ball_subset_ball (truePairScaleRadius_le dom M lam z)
    (ball_subset_ball (trueFrequencyScaleRadius_le dom M lam z) hbs)
  have hbP : (b : ℂ) ∈ ball (0 : ℂ) (dom.pairPolynomialScaleBase 0 M /
      (1 + |lam| + Real.sqrt ‖z‖)) :=
    ball_subset_ball (div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)) hbD
  have hbC := ball_subset_ball (min_le_left _ _)
    (ball_subset_ball (pairPolynomialScaleRadius_le dom hW hθ hD 0 M lam z).1 hbP)
  have hc := (negativeBridgePolynomial_constants dom hW hθ hD 0 M).2
  have he : Real.exp (-dom.negativeBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) ≤
      Real.exp (-(dom.negativeBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) / 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [abs_nonneg lam, Real.sqrt_nonneg ‖z‖]
  by_cases hl : lam ≤ 0
  · have h := cepsScaledRootPlus_negative_exp_polynomial dom hW hθ hD 0 M lam hl hz hbC
    have hL : 1 ≤ Real.exp (2 / cepsVarLo D) := Real.one_le_exp_iff.mpr (by have := cepsVarLo_pos hD; positivity)
    exact (h.trans he).trans (le_mul_of_one_le_left (Real.exp_pos _).le hL)
  · have hla : |lam| ≤ 1 := by rw [abs_of_pos (lt_of_not_ge hl)]; exact hlam
    exact (cepsScaledRootPlus_central_exp_polynomial dom hW hθ hD 0 M lam hla hz hbC).trans
      (mul_le_mul_of_nonneg_left he (Real.exp_pos _).le)

include hW hθ hD in
theorem cepsScaledTruePair_left_error_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 3 ≤ m)
    (lam : ℝ) (hlam : lam ≤ 1) {z : ℂ} (hz : z.re = 0) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDecayScaleRadius M lam z))
    (hbN : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius (N + 1) M lam z)) :
    ‖cepsScaledTruePair dom ρW lam z b - cepsScaledSurrogatePair dom ρW (N + 1) lam z b‖ ≤
      dom.leftPairErrorConstant (N + 1) M * b ^ (N + 2) * (1 + |lam| + Real.sqrt ‖z‖) ^ (N + 5) *
        Real.exp (-(dom.negativeBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) / 2) := by
  have hbf := ball_subset_ball (trueDecayScaleRadius_le_frequency dom M lam z) hbs
  obtain ⟨hH, hh, hE⟩ := cepsScaledEntrance_imaginary_comparison_profile dom hW hθ hD hf hη hM
    (N + 1) (by omega) lam hz hb hbf hbN
  have hK : 0 ≤ dom.entranceComparisonConstant (N + 1) M := by
    unfold CepsCanonDomain.entranceComparisonConstant; positivity
  have hEB := cepsDrift_taylor_value_budget (lam := lam) (X := 1 + |lam| + Real.sqrt ‖z‖)
    (N + 2) hb.le hK (by norm_num : (0 : ℝ) ≤ 1)
    (by linarith [Real.sqrt_nonneg ‖z‖]) (by simpa only [mul_one] using hE)
  simp only [mul_one] at hEB
  have hO := cepsScaledTrueBridge_left_timeOperator_budget dom hW hθ hD hf hη hM (by omega) lam hlam hz.symm.le hb hbs
  have hOE := cepsScaledTrueBridge_timeOperator_error_budget dom hW hθ hD hf hη hM N hN lam hz.symm.le hb hbf hbN
  have hExp := cepsScaledRootPlus_left_exp_polynomial dom hW hθ hD M lam hlam hz.symm.le hbf
  have hCE : 0 ≤ dom.bridgeTimeErrorConstant (N + 1) M := by
    have := kernelFrequencyConstant_pos dom (N + 1) M
    unfold CepsCanonDomain.bridgeTimeErrorConstant; positivity
  have hOE' := hOE.trans (mul_le_mul_of_nonneg_left hExp (by positivity))
  have hOE'' : ‖cepsScaledTimeOperator lam b (fun ζ => cepsScaledTrueBridge dom ρW lam ζ b) z -
      cepsScaledTimeOperator lam b (fun ζ => cepsScaledSurrogateBridge dom ρW (N + 1) lam ζ b) z‖ ≤
      (dom.bridgeTimeErrorConstant (N + 1) M * Real.exp (2 / cepsVarLo D)) * b ^ (N + 2) *
        (1 + |lam| + Real.sqrt ‖z‖) ^ (N + 3) *
          Real.exp (-(dom.negativeBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) / 2) := hOE'.trans_eq (by ring)
  have h := cepsNorm_square_product_taylor_error_le N hH hh hEB hO hOE''
  unfold cepsScaledTruePair cepsScaledSurrogatePair
  rw [mul_assoc (exp _) _ _, mul_assoc (exp _) _ _, ← mul_sub, norm_mul,
    cepsScaledMarker_exp_norm_imaginary lam b hz, one_mul]
  exact h.trans_eq (by unfold CepsCanonDomain.leftPairErrorConstant; ring)

include hW hθ hD in
theorem cepsScaledTruePair_left_error_envelope_integrable (N : ℕ) (M b : ℝ) (z : ℂ) :
    Integrable (fun lam : ℝ => dom.leftPairErrorConstant (N + 1) M * b ^ (N + 2) *
      (1 + |lam| + Real.sqrt ‖z‖) ^ (N + 5) *
        Real.exp (-(dom.negativeBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) / 2)) := by
  have hc := (negativeBridgePolynomial_constants dom hW hθ hD 0 M).2
  simpa only [neg_mul, neg_div, div_mul_eq_mul_div] using
    cepsBridge_polynomialEnvelope_integrable (N + 5) (half_pos hc)
      (dom.leftPairErrorConstant (N + 1) M * b ^ (N + 2)) z

end PGM
