import PLAStochastic.Index.CEPS.Scaled.TrueCutoffIntegrability
import PLAStochastic.Index.CEPS.Scaled.CutoffTaylorTail

/-! # Arbitrary-order tails when reducing a fixed actual drift cutoff -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.trueCutoffTailIntegralConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (M δ : ℝ) (n : ℕ) : ℝ :=
  (dom.trueSubtractedPairConstant M / δ ^ n) *
    ∫ lam : ℝ, (1 + |lam|) ^ (n + 3) *
      Real.exp (-(dom.positiveBridgeDecayRate / 2) * |lam|)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

theorem trueCutoffTailIntegralConstant_nonneg (M : ℝ) {δ : ℝ}
    (hδ : 0 < δ) (n : ℕ) : 0 ≤ dom.trueCutoffTailIntegralConstant M δ n := by
  have hK := trueSubtractedPairConstant_nonneg dom M
  unfold CepsCanonDomain.trueCutoffTailIntegralConstant
  exact mul_nonneg (by positivity) (integral_nonneg fun _ => by positivity)

include hW hθ hD in
theorem cepsScaledTrueCutoffPair_change_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m) {b δ δ' : ℝ}
    (hb : 0 < b) (hδ' : 0 < δ') (hδle : δ' ≤ δ)
    (hδ : δ ≤ dom.trueDecayScaleBase M / 4) {z : ℂ} (hz : z.re = 0)
    (hbz : b * (1 + Real.sqrt ‖z‖) < dom.trueDecayScaleBase M / 4)
    (n : ℕ) (lam : ℝ) :
    ‖cepsScaledTrueCutoffPair dom ρW b δ z lam -
      cepsScaledTrueCutoffPair dom ρW b δ' z lam‖ ≤
      (dom.trueSubtractedPairConstant M / δ' ^ n) * b ^ n *
        (1 + |lam| + Real.sqrt ‖z‖) ^ (n + 3) *
          Real.exp (-(dom.positiveBridgeDecayRate / 2) * (|lam| + Real.sqrt ‖z‖)) := by
  have hK := trueSubtractedPairConstant_nonneg dom M
  by_cases hs : |lam| ≤ δ' / b
  · have hl : |lam| ≤ δ / b := hs.trans (div_le_div_of_nonneg_right hδle hb.le)
    simp only [cepsScaledTrueCutoffPair, if_pos hs, if_pos hl, sub_self, norm_zero]
    positivity
  · have ht : δ' ≤ b * (1 + |lam| + Real.sqrt ‖z‖) := by
      have := (div_lt_iff₀ hb).mp (lt_of_not_ge hs)
      nlinarith [Real.sqrt_nonneg ‖z‖]
    simp only [cepsScaledTrueCutoffPair, if_neg hs, sub_zero]
    split_ifs with hl
    · have hbs := cepsScaledTrueDecay_mem_of_cutoff dom hW hθ hD
        ((cepsSobolev_nonneg m η fW).trans hM) hb hδ hbz hl
      exact cepsNorm_cutoff_tail_power_le_degree hK (by positivity) (Real.exp_nonneg _)
        hδ' ht 3 (cepsScaledTrueSubtractedPair_polynomial_budget dom hW hθ hD
          hf hη hM hm lam hz hb hbs) n
    · simp only [norm_zero]
      positivity

include hW hθ hD in
theorem cepsScaledTrueCutoffPair_change_integral_le {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m) {b δ δ' : ℝ}
    (hb : 0 < b) (hδ' : 0 < δ') (hδle : δ' ≤ δ)
    (hδ : δ ≤ dom.trueDecayScaleBase M / 4) {z : ℂ} (hz : z.re = 0)
    (hbz : b * (1 + Real.sqrt ‖z‖) < dom.trueDecayScaleBase M / 4) (n : ℕ) :
    ‖(∫ lam : ℝ, cepsScaledTrueCutoffPair dom ρW b δ z lam) -
      (∫ lam : ℝ, cepsScaledTrueCutoffPair dom ρW b δ' z lam)‖ ≤
      dom.trueCutoffTailIntegralConstant M δ' n * b ^ n *
        (1 + Real.sqrt ‖z‖) ^ (n + 3) *
          Real.exp (-(dom.positiveBridgeDecayRate / 2) * Real.sqrt ‖z‖) := by
  have hK := trueSubtractedPairConstant_nonneg dom M
  have hA := cepsScaledTrueCutoffPair_integrable dom hW hθ hD hf hη hM hm hb hδ hz hbz
  have hB := cepsScaledTrueCutoffPair_integrable dom hW hθ hD hf hη hM hm hb
    (hδle.trans hδ) hz hbz
  have hc := half_pos (positiveBridgePolynomial_constants dom hW hθ hD 0 M).2
  have hi := (cepsBrownian_driftEnvelope_integrable (n + 3) hc).const_mul
    ((dom.trueSubtractedPairConstant M / δ' ^ n) * b ^ n *
      (1 + Real.sqrt ‖z‖) ^ (n + 3) *
        Real.exp (-(dom.positiveBridgeDecayRate / 2) * Real.sqrt ‖z‖))
  rw [← integral_sub hA hB]
  have h := norm_integral_le_of_norm_le
    (f := fun lam : ℝ => cepsScaledTrueCutoffPair dom ρW b δ z lam -
      cepsScaledTrueCutoffPair dom ρW b δ' z lam) hi (ae_of_all _ fun lam => ?_)
  · rw [integral_const_mul] at h
    exact h.trans_eq (by unfold CepsCanonDomain.trueCutoffTailIntegralConstant; ring)
  · have hp : 1 + |lam| + Real.sqrt ‖z‖ ≤ (1 + |lam|) * (1 + Real.sqrt ‖z‖) := by
      nlinarith [mul_nonneg (abs_nonneg lam) (Real.sqrt_nonneg ‖z‖)]
    apply (cepsScaledTrueCutoffPair_change_budget dom hW hθ hD hf hη hM hm
      hb hδ' hδle hδ hz hbz n lam).trans
    calc
      _ ≤ (dom.trueSubtractedPairConstant M / δ' ^ n) * b ^ n *
          ((1 + |lam|) * (1 + Real.sqrt ‖z‖)) ^ (n + 3) *
            Real.exp (-(dom.positiveBridgeDecayRate / 2) * (|lam| + Real.sqrt ‖z‖)) := by
        gcongr
      _ = _ := by
        rw [mul_pow, show -(dom.positiveBridgeDecayRate / 2) * (|lam| + Real.sqrt ‖z‖) =
          -(dom.positiveBridgeDecayRate / 2) * |lam| +
            -(dom.positiveBridgeDecayRate / 2) * Real.sqrt ‖z‖ by ring, Real.exp_add]
        ring

end PGM
