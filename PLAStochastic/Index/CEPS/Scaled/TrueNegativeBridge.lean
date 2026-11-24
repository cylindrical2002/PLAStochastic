import PLAStochastic.Index.CEPS.Scaled.TrueFrequencyBudget
import PLAStochastic.Index.CEPS.Scaled.NegativeBridgePolynomial

/-! # Actual negative-drift bridge decay on the order-independent disc -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledRootPlus_negative_exp_polynomial (N : ℕ) (M lam : ℝ) (hlam : lam ≤ 0)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.complexDirectionScaleRadius N M lam z)) :
    Real.exp (-(cepsScaledSignedRoot D θ ρW lam z 1 b * (1 + b * lam)).re) ≤
      Real.exp (-dom.negativeBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) := by
  have he := cepsScaledRootPlus_complex_exp_decay dom hW hθ hD N M lam hlam hz hb
  simp only [norm_exp, neg_mul, neg_re] at he
  have hv : 0 < 8 * Real.sqrt v := by have := CepsCanonDomain.v_pos hW hθ hD; positivity
  have hlo := div_le_div_of_nonneg_right
    (scaledCoordinateLower_drift_frequency_le dom hW hθ hD lam z) hv.le
  have hdir : -dom.scaledCoordinateLower lam z / (8 * Real.sqrt v) ≤
      -dom.negativeBridgeDecayRate * (|lam| + Real.sqrt ‖z‖) := by
    unfold CepsCanonDomain.negativeBridgeDecayRate
    have hr : ((|lam| + Real.sqrt ‖z‖) / Real.sqrt (8 * v + 8)) / (8 * Real.sqrt v) =
        (1 / (Real.sqrt (8 * v + 8) * (8 * Real.sqrt v))) * (|lam| + Real.sqrt ‖z‖) := by ring
    rw [hr] at hlo
    simpa only [neg_div, neg_mul] using neg_le_neg hlo
  exact he.trans (Real.exp_le_exp.mpr hdir)

include hW hθ hD in
theorem cepsScaledTrueBridge_negative_polynomial_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m) (lam : ℝ) (hlam : lam ≤ 0)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDenominatorScaleRadius M lam z)) :
    ‖cepsScaledTrueBridge dom ρW lam z b‖ ≤ dom.trueBridgeWeightedConstant M *
      (1 + |lam| + Real.sqrt ‖z‖) *
        Real.exp (-dom.negativeBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) := by
  have hbP : (b : ℂ) ∈ ball (0 : ℂ) (dom.pairPolynomialScaleBase 0 M /
      (1 + |lam| + Real.sqrt ‖z‖)) :=
    ball_subset_ball (div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)) hb
  have hbD := ball_subset_ball (min_le_left _ _)
    (ball_subset_ball (pairPolynomialScaleRadius_le dom hW hθ hD 0 M lam z).1 hbP)
  have he := cepsScaledRootPlus_negative_exp_polynomial dom hW hθ hD 0 M lam hlam hz hbD
  exact (cepsScaledTrueBridge_weighted_budget dom hW hθ hD hf hη hM hm lam hz hb).trans
    (mul_le_mul_of_nonneg_left he (by
      unfold CepsCanonDomain.trueBridgeWeightedConstant
      have := (surrogateSlopePolynomialConstant_pos dom hW hθ hD 0 M).le
      positivity))

end PGM
