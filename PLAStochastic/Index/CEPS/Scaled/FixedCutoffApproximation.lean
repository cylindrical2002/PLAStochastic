import PLAStochastic.Index.CEPS.Scaled.CutoffPairIntegralError

/-! # An order-dependent approximation inside an order-independent actual cutoff -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.pairApproximationCutoff {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M δ : ℝ) : ℝ :=
  min δ (dom.pairComparisonScaleBase (N + 1) M / 8)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem pairApproximationCutoff_properties (N : ℕ) {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 < δ) :
    0 < dom.pairApproximationCutoff N M δ ∧
      dom.pairApproximationCutoff N M δ ≤ δ ∧
      dom.pairApproximationCutoff N M δ ≤ dom.pairComparisonScaleBase (N + 1) M / 4 := by
  have hbase := pairComparisonScaleBase_pos dom hW hθ hD (N + 1) hM
  refine ⟨lt_min hδ (by positivity), min_le_left _ _, ?_⟩
  exact (min_le_right _ _).trans (by linarith)

include hW hθ hD in
theorem cepsScaledCutoffPair_fixed_integral_error {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 3 ≤ m)
    {δ : ℝ} (hδ : 0 < δ) (hδactual : δ ≤ dom.trueDecayScaleBase M / 4)
    {b : ℝ} (hb : 0 < b) {z : ℂ} (hz : z.re = 0)
    (hbz : b * (1 + Real.sqrt ‖z‖) < dom.pairComparisonScaleBase (N + 1) M / 4) :
    let δN := dom.pairApproximationCutoff N M δ
    Integrable (cepsScaledTrueCutoffPair dom ρW b δ z) ∧
      Integrable (cepsScaledSurrogateCutoffPair dom ρW (N + 1) b δN z) ∧
      ‖(∫ lam : ℝ, cepsScaledTrueCutoffPair dom ρW b δ z lam) -
        (∫ lam : ℝ, cepsScaledSurrogateCutoffPair dom ρW (N + 1) b δN z lam)‖ ≤
        dom.cutoffPairErrorIntegralConstant N M δN * b ^ (N + 2) *
          (1 + Real.sqrt ‖z‖) ^ (N + 5) * Real.exp (-(dom.positiveBridgeDecayRate / 2) * Real.sqrt ‖z‖) := by
  obtain ⟨hδN, hle, hsmall⟩ := pairApproximationCutoff_properties dom hW hθ hD N
    ((cepsSobolev_nonneg m η fW).trans hM) hδ
  exact cepsScaledCutoffPair_integral_error dom hW hθ hD hf hη hM N hN hb hδN hle hδactual hsmall hz hbz

end PGM
