import PLAStochastic.Index.CEPS.Scaled.BridgePolynomialTaylor

/-! # Integration of square-root-frequency polynomial exponential envelopes -/

noncomputable section
open Complex Set Metric MeasureTheory
namespace PGM

theorem cepsScaled_integral_norm_le_of_envelope {F : ℝ → ℂ} {C c : ℝ}
    (d : ℕ) (hc : 0 < c) (hC : 0 ≤ C) (z : ℂ) (hm : AEStronglyMeasurable F)
    (hb : ∀ x, ‖F x‖ ≤ C * (1 + |x| + Real.sqrt ‖z‖) ^ d *
      Real.exp (-c * (|x| + Real.sqrt ‖z‖))) :
    Integrable F ∧ ‖∫ x, F x‖ ≤
      (C * ∫ x : ℝ, (1 + |x|) ^ d * Real.exp (-c * |x|)) *
        (1 + Real.sqrt ‖z‖) ^ d * Real.exp (-c * Real.sqrt ‖z‖) := by
  have he := cepsBridge_polynomialEnvelope_integrable d hc C z
  have hi : Integrable F := he.mono' hm (ae_of_all _ hb)
  have hmajor (x : ℝ) : C * (1 + |x| + Real.sqrt ‖z‖) ^ d *
      Real.exp (-c * (|x| + Real.sqrt ‖z‖)) ≤
      (C * (1 + Real.sqrt ‖z‖) ^ d * Real.exp (-c * Real.sqrt ‖z‖)) *
        ((1 + |x|) ^ d * Real.exp (-c * |x|)) := by
    have hp : 1 + |x| + Real.sqrt ‖z‖ ≤ (1 + |x|) * (1 + Real.sqrt ‖z‖) := by
      nlinarith [mul_nonneg (abs_nonneg x) (Real.sqrt_nonneg ‖z‖)]
    calc
      _ ≤ C * ((1 + |x|) * (1 + Real.sqrt ‖z‖)) ^ d * Real.exp (-c * (|x| + Real.sqrt ‖z‖)) := by gcongr
      _ = _ := by
        rw [mul_pow, show -c * (|x| + Real.sqrt ‖z‖) = -c * |x| + -c * Real.sqrt ‖z‖ by ring, Real.exp_add]
        ring
  have hmi := (cepsBrownian_driftEnvelope_integrable d hc).const_mul
    (C * (1 + Real.sqrt ‖z‖) ^ d * Real.exp (-c * Real.sqrt ‖z‖))
  refine ⟨hi, (norm_integral_le_integral_norm F).trans ?_⟩
  calc
    _ ≤ ∫ x : ℝ, (C * (1 + Real.sqrt ‖z‖) ^ d * Real.exp (-c * Real.sqrt ‖z‖)) *
        ((1 + |x|) ^ d * Real.exp (-c * |x|)) := integral_mono hi.norm hmi (fun x => (hb x).trans (hmajor x))
    _ = _ := by rw [integral_const_mul]; ring

end PGM
