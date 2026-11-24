import PLAStochastic.Index.CEPS.Scaled.EndpointWeights

/-! # The endpoint carrier absorbs the positive-root exponential weight -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledEndpointCarrier_weighted_budget (N : ℕ) (M : ℝ)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.pairPolynomialScaleBase N M / (2 + Real.sqrt ‖z‖))) :
    Real.exp (-(cepsScaledSignedRoot D θ ρW 1 z 1 b * (1 + b)).re) *
      ‖cepsScaledEndpointCarrier D θ ρW z b‖ ≤
        (dom.endpointCarrierConstant * Real.exp (2 / cepsVarLo D)) *
          (2 + Real.sqrt ‖z‖) * Real.exp (-dom.entranceBridgeDecayRate * Real.sqrt ‖z‖) := by
  let p := (cepsScaledSignedRoot D θ ρW 1 z 1 b * (1 + b)).re
  let t := ((b * z) * (1 + b)).re
  have hb' : b ∈ ball (0 : ℂ) (dom.pairPolynomialScaleBase N M /
      (1 + |(1 : ℝ)| + Real.sqrt ‖z‖)) := by
    simpa only [abs_one, one_add_one_eq_two] using hb
  have hdir := cepsScaledRootPlus_marker_drift_loss dom hW hθ hD N M 1 hz hb'
  simp only [abs_one, ofReal_one, mul_one, sub_mul, sub_re] at hdir
  have hc := (entranceBridgePolynomial_constants dom hW hθ hD N M).2
  have he : t - p ≤ 2 / cepsVarLo D - dom.entranceBridgeDecayRate * Real.sqrt ‖z‖ := by
    dsimp only [t, p]
    linarith [hc.le]
  have hK := endpointCarrierConstant_nonneg dom hW hθ hD
  calc
    _ ≤ Real.exp (-p) * (dom.endpointCarrierConstant * (2 + Real.sqrt ‖z‖) * Real.exp t) :=
      mul_le_mul_of_nonneg_left (cepsScaledEndpointCarrier_budget dom hW hθ hD N M hz hb)
        (Real.exp_pos _).le
    _ = (dom.endpointCarrierConstant * (2 + Real.sqrt ‖z‖)) * Real.exp (t - p) := by
      rw [show t - p = -p + t by ring, Real.exp_add]
      ring
    _ ≤ (dom.endpointCarrierConstant * (2 + Real.sqrt ‖z‖)) *
        Real.exp (2 / cepsVarLo D - dom.entranceBridgeDecayRate * Real.sqrt ‖z‖) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity)
    _ = _ := by
      rw [show 2 / cepsVarLo D - dom.entranceBridgeDecayRate * Real.sqrt ‖z‖ =
        2 / cepsVarLo D + -dom.entranceBridgeDecayRate * Real.sqrt ‖z‖ by ring, Real.exp_add]
      ring

end PGM
