import PLAStochastic.Index.CEPS.Scaled.TrueCutoffPairMeasurability

/-! # Integrability of the actual subtracted complete pair at fixed physical cutoff -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrueCutoffPair_integrable {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m) {b δ : ℝ}
    (hb : 0 < b) (hδ : δ ≤ dom.trueDecayScaleBase M / 4) {z : ℂ} (hz : z.re = 0)
    (hbz : b * (1 + Real.sqrt ‖z‖) < dom.trueDecayScaleBase M / 4) :
    Integrable (cepsScaledTrueCutoffPair dom ρW b δ z) := by
  have hc := half_pos (positiveBridgePolynomial_constants dom hW hθ hD 0 M).2
  have hi := (cepsBrownian_driftEnvelope_integrable 3 hc).const_mul
    (dom.trueSubtractedPairConstant M * (1 + Real.sqrt ‖z‖) ^ 3 *
      Real.exp (-(dom.positiveBridgeDecayRate / 2) * Real.sqrt ‖z‖))
  exact hi.mono' (cepsScaledTrueCutoffPair_aestronglyMeasurable dom hW hθ hD hf hm hη hM
    hb hδ (by rw [hz]) hbz) (ae_of_all _ fun a =>
      cepsScaledTrueCutoffPair_factored_budget dom hW hθ hD hf hη hM hm hb hδ hz hbz a)

include hW hθ hD in
theorem cepsScaledTrueCutoffPair_integrable_and_integral_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m) {b δ : ℝ}
    (hb : 0 < b) (hδ : δ ≤ dom.trueDecayScaleBase M / 4) {z : ℂ} (hz : z.re = 0)
    (hbz : b * (1 + Real.sqrt ‖z‖) < dom.trueDecayScaleBase M / 4) :
    Integrable (cepsScaledTrueCutoffPair dom ρW b δ z) ∧
      ‖∫ a : ℝ, cepsScaledTrueCutoffPair dom ρW b δ z a‖ ≤
        dom.truePairIntegralConstant M * (1 + Real.sqrt ‖z‖) ^ 3 *
          Real.exp (-(dom.positiveBridgeDecayRate / 2) * Real.sqrt ‖z‖) :=
  ⟨cepsScaledTrueCutoffPair_integrable dom hW hθ hD hf hη hM hm hb hδ hz hbz,
    cepsScaledTrueCutoffPair_integral_budget dom hW hθ hD hf hη hM hm hb hδ hz hbz⟩

end PGM
