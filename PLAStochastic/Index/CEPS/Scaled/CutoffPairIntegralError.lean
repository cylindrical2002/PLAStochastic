import PLAStochastic.Index.CEPS.Scaled.SurrogateCutoffPairMeasurability
import PLAStochastic.Index.CEPS.Scaled.TrueCutoffIntegrability
import PLAStochastic.Index.CEPS.Scaled.PolynomialEnvelopeIntegral

/-! # Genuine integral comparison at a fixed actual physical drift cutoff -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.cutoffPairErrorIntegralConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M δ : ℝ) : ℝ :=
  dom.cutoffPairErrorConstant N M δ *
    ∫ lam : ℝ, (1 + |lam|) ^ (N + 5) * Real.exp (-(dom.positiveBridgeDecayRate / 2) * |lam|)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

theorem cutoffPairErrorIntegralConstant_nonneg (N : ℕ) (M : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    0 ≤ dom.cutoffPairErrorIntegralConstant N M δ :=
  mul_nonneg (cutoffPairErrorConstant_nonneg dom N M hδ) (integral_nonneg (fun _ => by positivity))

include hW hθ hD in
theorem cepsScaledCutoffPair_integral_error {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 3 ≤ m)
    {b δ δN : ℝ} (hb : 0 < b) (hδN : 0 < δN) (hδle : δN ≤ δ)
    (hδ : δ ≤ dom.trueDecayScaleBase M / 4)
    (hδsmall : δN ≤ dom.pairComparisonScaleBase (N + 1) M / 4)
    {z : ℂ} (hz : z.re = 0)
    (hbz : b * (1 + Real.sqrt ‖z‖) < dom.pairComparisonScaleBase (N + 1) M / 4) :
    Integrable (cepsScaledTrueCutoffPair dom ρW b δ z) ∧
      Integrable (cepsScaledSurrogateCutoffPair dom ρW (N + 1) b δN z) ∧
      ‖(∫ lam : ℝ, cepsScaledTrueCutoffPair dom ρW b δ z lam) -
        (∫ lam : ℝ, cepsScaledSurrogateCutoffPair dom ρW (N + 1) b δN z lam)‖ ≤
        dom.cutoffPairErrorIntegralConstant N M δN * b ^ (N + 2) *
          (1 + Real.sqrt ‖z‖) ^ (N + 5) * Real.exp (-(dom.positiveBridgeDecayRate / 2) * Real.sqrt ‖z‖) := by
  have hbase : dom.pairComparisonScaleBase (N + 1) M ≤ dom.trueDecayScaleBase M := min_le_left _ _
  have hbzT := hbz.trans_le (div_le_div_of_nonneg_right hbase (by norm_num))
  have hA := cepsScaledTrueCutoffPair_integrable dom hW hθ hD hf hη hM (by omega) hb hδ hz hbzT
  have hmS := cepsScaledSurrogateCutoffPair_aestronglyMeasurable dom hW hθ hD hf hη hM (N + 1)
    (by omega) hb hδsmall (by rw [hz]) hbz
  have hc := half_pos (positiveBridgePolynomial_constants dom hW hθ hD 0 M).2
  have hC := mul_nonneg (cutoffPairErrorConstant_nonneg dom N M hδN) (pow_nonneg hb.le (N + 2))
  obtain ⟨hErr, hbound⟩ := cepsScaled_integral_norm_le_of_envelope (N + 5) hc hC z
    (hA.aestronglyMeasurable.sub hmS) (fun lam =>
      cepsScaledCutoffPair_error_budget dom hW hθ hD hf hη hM N hN hb hδN hδle hδ hδsmall hz hbz lam)
  have hS : Integrable (cepsScaledSurrogateCutoffPair dom ρW (N + 1) b δN z) :=
    (hA.sub hErr).congr (ae_of_all _ fun lam => by
      change cepsScaledTrueCutoffPair dom ρW b δ z lam -
        (cepsScaledTrueCutoffPair dom ρW b δ z lam - cepsScaledSurrogateCutoffPair dom ρW (N + 1) b δN z lam) =
          cepsScaledSurrogateCutoffPair dom ρW (N + 1) b δN z lam
      ring)
  refine ⟨hA, hS, ?_⟩
  simp only [Pi.sub_apply] at hbound
  rw [integral_sub hA hS] at hbound
  exact hbound.trans_eq (by unfold CepsCanonDomain.cutoffPairErrorIntegralConstant; ring)

end PGM
