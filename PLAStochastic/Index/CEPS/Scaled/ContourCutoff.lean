import PLAStochastic.Index.CEPS.Scaled.ContourPair
import PLAStochastic.Index.CEPS.Scaled.TrueCutoffChange

/-! # Transfer of the actual cutoff integral to a smaller contour -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)
variable {σ : ℝ} (hσ : 0 < σ) (hσc : σ ≤ dom.c₀)

include hW hθ hD in
theorem cepsScaledTrueCutoffPair_shrink_eq {M M' b δ : ℝ} (hM : 0 ≤ M) (hM' : 0 ≤ M')
    (hb : 0 < b) (hδ : δ ≤ dom.trueDecayScaleBase M / 4)
    (hδ' : δ ≤ (dom.shrink σ hσ hσc).trueDecayScaleBase M' / 4)
    {z : ℂ} (hz : z.re = 0)
    (hbz : b * (1 + Real.sqrt ‖z‖) < dom.trueDecayScaleBase M / 4)
    (hbz' : b * (1 + Real.sqrt ‖z‖) < (dom.shrink σ hσ hσc).trueDecayScaleBase M' / 4)
    (lam : ℝ) :
    cepsScaledTrueCutoffPair (dom.shrink σ hσ hσc) ρW b δ z lam =
      cepsScaledTrueCutoffPair dom ρW b δ z lam := by
  unfold cepsScaledTrueCutoffPair
  split_ifs with hl
  · have hbs := cepsScaledTrueDecay_mem_of_cutoff dom hW hθ hD hM hb hδ hbz hl
    have hbs' := cepsScaledTrueDecay_mem_of_cutoff (dom.shrink σ hσ hσc)
      hW hθ hD hM' hb hδ' hbz' hl
    exact cepsScaledTrueSubtractedPair_shrink_eq dom hW hθ hD hσ hσc M M' lam hz hb
      (ball_subset_ball (trueDecayScaleRadius_le_frequency dom M lam z) hbs)
      (ball_subset_ball (trueDecayScaleRadius_le_frequency (dom.shrink σ hσ hσc) M' lam z) hbs')
  · rfl

include hW hθ hD in
theorem cepsScaledTrueCutoffPair_shrink_integral_eq {M M' b δ : ℝ}
    (hM : 0 ≤ M) (hM' : 0 ≤ M') (hb : 0 < b)
    (hδ : δ ≤ dom.trueDecayScaleBase M / 4)
    (hδ' : δ ≤ (dom.shrink σ hσ hσc).trueDecayScaleBase M' / 4)
    {z : ℂ} (hz : z.re = 0)
    (hbz : b * (1 + Real.sqrt ‖z‖) < dom.trueDecayScaleBase M / 4)
    (hbz' : b * (1 + Real.sqrt ‖z‖) < (dom.shrink σ hσ hσc).trueDecayScaleBase M' / 4) :
    (∫ lam : ℝ, cepsScaledTrueCutoffPair (dom.shrink σ hσ hσc) ρW b δ z lam) =
      ∫ lam : ℝ, cepsScaledTrueCutoffPair dom ρW b δ z lam := by
  exact integral_congr_ae (ae_of_all _ fun lam =>
    cepsScaledTrueCutoffPair_shrink_eq dom hW hθ hD hσ hσc hM hM' hb hδ hδ' hz hbz hbz' lam)

include hW hθ hD in
theorem cepsScaledTrueCutoffPair_shrink_integral_le {m : ℕ} {η M M' : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m) (hM' : 0 ≤ M')
    {b δ δ' : ℝ} (hb : 0 < b) (hδ' : 0 < δ') (hδle : δ' ≤ δ)
    (hδ : δ ≤ dom.trueDecayScaleBase M / 4)
    (hsmall : δ' ≤ (dom.shrink σ hσ hσc).trueDecayScaleBase M' / 4)
    {z : ℂ} (hz : z.re = 0)
    (hbz : b * (1 + Real.sqrt ‖z‖) < dom.trueDecayScaleBase M / 4)
    (hbz' : b * (1 + Real.sqrt ‖z‖) < (dom.shrink σ hσ hσc).trueDecayScaleBase M' / 4)
    (n : ℕ) :
    ‖(∫ lam : ℝ, cepsScaledTrueCutoffPair dom ρW b δ z lam) -
      (∫ lam : ℝ, cepsScaledTrueCutoffPair (dom.shrink σ hσ hσc) ρW b δ' z lam)‖ ≤
      dom.trueCutoffTailIntegralConstant M δ' n * b ^ n *
        (1 + Real.sqrt ‖z‖) ^ (n + 3) *
          Real.exp (-(dom.positiveBridgeDecayRate / 2) * Real.sqrt ‖z‖) := by
  rw [cepsScaledTrueCutoffPair_shrink_integral_eq dom hW hθ hD hσ hσc
    ((cepsSobolev_nonneg m η fW).trans hM) hM' hb (hδle.trans hδ) hsmall hz hbz hbz']
  exact cepsScaledTrueCutoffPair_change_integral_le dom hW hθ hD hf hη hM hm
    hb hδ' hδle hδ hz hbz n

end PGM
