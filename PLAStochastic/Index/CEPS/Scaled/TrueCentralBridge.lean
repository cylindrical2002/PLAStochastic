import PLAStochastic.Index.CEPS.Scaled.TrueFrequencyBudget
import PLAStochastic.Index.CEPS.Scaled.RootDriftDirection
import PLAStochastic.Index.CEPS.Scaled.NegativeBridgePolynomial

/-! # Actual bridge decay on the bounded central drift interval -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.trueCentralBridgeConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (M : ℝ) : ℝ :=
  dom.trueBridgeWeightedConstant M * Real.exp (2 / cepsVarLo D)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledRootPlus_central_exp_polynomial (N : ℕ) (M lam : ℝ)
    (hlam : |lam| ≤ 1) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.complexDirectionScaleRadius N M lam z)) :
    Real.exp (-(cepsScaledSignedRoot D θ ρW lam z 1 b * (1 + b * lam)).re) ≤
      Real.exp (2 / cepsVarLo D) *
        Real.exp (-dom.negativeBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) := by
  have hpre := cepsScaledRootPlus_width_drift_loss dom hW hθ hD N M lam hz hb
  have hbReg := ball_subset_ball (min_le_left _ _) (ball_subset_ball (min_le_left _ _) hb)
  have hRc := (scaledCoordinateLower_drift_frequency_le dom hW hθ hD lam z).trans
    (cepsScaledRootCoordinate_lower dom hW hθ hD N M lam hz hbReg)
  have hv := CepsCanonDomain.v_pos hW hθ hD
  have hvl := cepsVarLo_pos hD
  have hlo := div_le_div_of_nonneg_right hRc
    (by positivity : 0 ≤ 8 * Real.sqrt v)
  have hloss := mul_le_of_le_one_right (by positivity : 0 ≤ 2 / cepsVarLo D) hlam
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hr : ((|lam| + Real.sqrt ‖z‖) / Real.sqrt (8 * v + 8)) / (8 * Real.sqrt v) =
      dom.negativeBridgeDecayRate * (|lam| + Real.sqrt ‖z‖) := by
    unfold CepsCanonDomain.negativeBridgeDecayRate
    ring
  rw [hr] at hlo
  linarith

include hW hθ hD in
theorem cepsScaledTrueBridge_central_polynomial_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m) (lam : ℝ) (hlam : |lam| ≤ 1)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDenominatorScaleRadius M lam z)) :
    ‖cepsScaledTrueBridge dom ρW lam z b‖ ≤ dom.trueCentralBridgeConstant M *
      (1 + |lam| + Real.sqrt ‖z‖) *
        Real.exp (-dom.negativeBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) := by
  have hbP : (b : ℂ) ∈ ball (0 : ℂ) (dom.pairPolynomialScaleBase 0 M /
      (1 + |lam| + Real.sqrt ‖z‖)) :=
    ball_subset_ball (div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)) hb
  have hbD := ball_subset_ball (min_le_left _ _)
    (ball_subset_ball (pairPolynomialScaleRadius_le dom hW hθ hD 0 M lam z).1 hbP)
  have he := cepsScaledRootPlus_central_exp_polynomial dom hW hθ hD 0 M lam hlam hz hbD
  have hK : 0 ≤ dom.trueBridgeWeightedConstant M := by
    unfold CepsCanonDomain.trueBridgeWeightedConstant
    have := (surrogateSlopePolynomialConstant_pos dom hW hθ hD 0 M).le
    positivity
  exact ((cepsScaledTrueBridge_weighted_budget dom hW hθ hD hf hη hM hm lam hz hb).trans
    (mul_le_mul_of_nonneg_left he (by positivity))).trans_eq (by
      unfold CepsCanonDomain.trueCentralBridgeConstant
      ring)

end PGM
