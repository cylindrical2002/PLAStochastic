import PLAStochastic.Index.CEPS.Scaled.TrueCutoffRadius

/-! # Actual drift-cutoff pair integral frequency decay

This is a norm budget for the Bochner integral. It does not assert
measurability or integrability of the actual cutoff kernel.
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def cepsScaledTrueCutoffPair {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (b δ : ℝ) (z : ℂ) (lam : ℝ) : ℂ :=
  if |lam| ≤ δ / b then cepsScaledTrueSubtractedPair dom ρW lam z b else 0

def CepsCanonDomain.truePairIntegralConstant {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (M : ℝ) : ℝ := dom.trueSubtractedPairConstant M *
      ∫ lam : ℝ, (1 + |lam|) ^ 3 * Real.exp (-(dom.positiveBridgeDecayRate / 2) * |lam|)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

theorem trueSubtractedPairConstant_nonneg (M : ℝ) : 0 ≤ dom.trueSubtractedPairConstant M := by
  unfold CepsCanonDomain.trueSubtractedPairConstant
  positivity

theorem truePairIntegralConstant_nonneg (M : ℝ) : 0 ≤ dom.truePairIntegralConstant M :=
  mul_nonneg (trueSubtractedPairConstant_nonneg dom M) (integral_nonneg (fun _ => by positivity))

include hW hθ hD in
theorem cepsScaledTrueCutoffPair_factored_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m) {b δ : ℝ}
    (hb : 0 < b) (hδ : δ ≤ dom.trueDecayScaleBase M / 4) {z : ℂ} (hz : z.re = 0)
    (hbz : b * (1 + Real.sqrt ‖z‖) < dom.trueDecayScaleBase M / 4) (lam : ℝ) :
    ‖cepsScaledTrueCutoffPair dom ρW b δ z lam‖ ≤
      (dom.trueSubtractedPairConstant M * (1 + Real.sqrt ‖z‖) ^ 3 *
        Real.exp (-(dom.positiveBridgeDecayRate / 2) * Real.sqrt ‖z‖)) *
          ((1 + |lam|) ^ 3 * Real.exp (-(dom.positiveBridgeDecayRate / 2) * |lam|)) := by
  have hK := trueSubtractedPairConstant_nonneg dom M
  unfold cepsScaledTrueCutoffPair
  split_ifs with hlam
  · have hbs := cepsScaledTrueDecay_mem_of_cutoff dom hW hθ hD
      ((cepsSobolev_nonneg m η fW).trans hM) hb hδ hbz hlam
    have hn := cepsScaledTrueSubtractedPair_polynomial_budget dom hW hθ hD hf hη hM hm lam hz hb hbs
    have hp : 1 + |lam| + Real.sqrt ‖z‖ ≤ (1 + |lam|) * (1 + Real.sqrt ‖z‖) := by
      nlinarith [mul_nonneg (abs_nonneg lam) (Real.sqrt_nonneg ‖z‖)]
    apply hn.trans
    calc
      _ ≤ dom.trueSubtractedPairConstant M * ((1 + |lam|) * (1 + Real.sqrt ‖z‖)) ^ 3 *
          Real.exp (-(dom.positiveBridgeDecayRate / 2) * (|lam| + Real.sqrt ‖z‖)) := by
        gcongr
      _ = _ := by
        rw [mul_pow, show -(dom.positiveBridgeDecayRate / 2) * (|lam| + Real.sqrt ‖z‖) =
          -(dom.positiveBridgeDecayRate / 2) * |lam| + -(dom.positiveBridgeDecayRate / 2) * Real.sqrt ‖z‖ by ring,
          Real.exp_add]
        ring
  · rw [norm_zero]
    positivity

include hW hθ hD in
theorem cepsScaledTrueCutoffPair_integral_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m) {b δ : ℝ}
    (hb : 0 < b) (hδ : δ ≤ dom.trueDecayScaleBase M / 4) {z : ℂ} (hz : z.re = 0)
    (hbz : b * (1 + Real.sqrt ‖z‖) < dom.trueDecayScaleBase M / 4) :
    ‖∫ lam : ℝ, cepsScaledTrueCutoffPair dom ρW b δ z lam‖ ≤
      dom.truePairIntegralConstant M * (1 + Real.sqrt ‖z‖) ^ 3 *
        Real.exp (-(dom.positiveBridgeDecayRate / 2) * Real.sqrt ‖z‖) := by
  have hc := half_pos (positiveBridgePolynomial_constants dom hW hθ hD 0 M).2
  have hi := (cepsBrownian_driftEnvelope_integrable 3 hc).const_mul
    (dom.trueSubtractedPairConstant M * (1 + Real.sqrt ‖z‖) ^ 3 *
      Real.exp (-(dom.positiveBridgeDecayRate / 2) * Real.sqrt ‖z‖))
  have h := norm_integral_le_of_norm_le hi (ae_of_all _ fun lam =>
    cepsScaledTrueCutoffPair_factored_budget dom hW hθ hD hf hη hM hm hb hδ hz hbz lam)
  rw [integral_const_mul] at h
  exact h.trans_eq (by unfold CepsCanonDomain.truePairIntegralConstant; ring)

end PGM
