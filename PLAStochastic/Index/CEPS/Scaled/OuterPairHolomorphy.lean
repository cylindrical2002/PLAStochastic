import PLAStochastic.Index.CEPS.Scaled.HalfBridgeJoint
import PLAStochastic.Index.CEPS.Scaled.SurrogatePairJoint
import PLAStochastic.Index.CEPS.Scaled.SurrogateHalfEntranceHolomorphy
import PLAStochastic.Index.CEPS.Scaled.SubtractedPairError
import PLAStochastic.Index.CEPS.Scaled.OuterTimeOperator

/-! # Scale holomorphy of the complete subtracted pair outside the central rectangle -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

attribute [local irreducible] cepsScaledSurrogatePair cepsScaledSurrogateHalfPair

def CepsCanonDomain.outerPairScaleRadius {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (N : ℕ) (M lam : ℝ) (z : ℂ) : ℝ :=
  min (dom.pairPolynomialScaleBase N M / (1 + |lam| + Real.sqrt ‖z‖))
    (min (dom.jointRootScaleRadius lam z) (1 / (2 * (1 + |lam|))))

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem outerPairScaleRadius_pos (N : ℕ) (M lam : ℝ) (z : ℂ) :
    0 < dom.outerPairScaleRadius N M lam z := by
  unfold CepsCanonDomain.outerPairScaleRadius
  exact lt_min (div_pos (pairPolynomialScaleBase_pos dom hW hθ hD N M) (by positivity))
    (lt_min (jointRootScaleRadius_pos dom hW hθ hD lam z) (by positivity))

include hW hθ hD in
theorem cepsScaledSurrogatePairs_outer_differentiableOn {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) (hne : lam ≠ 0 ∨ z ≠ 0) :
    DifferentiableOn ℂ (cepsScaledSurrogatePair dom ρW N lam z)
      (ball 0 (dom.outerPairScaleRadius N M lam z)) ∧
      (1 ≤ lam → DifferentiableOn ℂ (cepsScaledSurrogateHalfPair dom ρW N lam z)
        (ball 0 (dom.outerPairScaleRadius N M lam z))) := by
  let U := ball (0 : ℂ) (dom.outerPairScaleRadius N M lam z)
  have hP : U ⊆ ball (0 : ℂ) (dom.pairPolynomialScaleBase N M / (1 + |lam| + Real.sqrt ‖z‖)) :=
    ball_subset_ball (min_le_left _ _)
  have hE : U ⊆ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z) :=
    fun b hb => ball_subset_ball (pairPolynomialScaleRadius_le dom hW hθ hD N M lam z).2 (hP hb)
  have hJ : U ⊆ ball (0 : ℂ) (dom.jointRootScaleRadius lam z) :=
    ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _))
  have hWidth : U ⊆ ball (0 : ℂ) (1 / (2 * (1 + |lam|))) :=
    ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _))
  have hjoint : ∀ b ∈ U, b ∈ ball (0 : ℂ)
      (min (dom.jointRootScaleRadius lam z) (dom.entranceScaleRadius N M lam z)) :=
    fun b hb => mem_ball_zero_iff.mpr (lt_min (mem_ball_zero_iff.mp (hJ hb)) (mem_ball_zero_iff.mp (hE hb)))
  have hcurve : ∀ b : ℂ, DifferentiableAt ℂ (fun c : ℂ => (c, z)) b :=
    fun _ => differentiableAt_id.prodMk (differentiableAt_const z)
  have hFull : DifferentiableOn ℂ (cepsScaledSurrogatePair dom ρW N lam z) U := by
    intro b hb
    obtain ⟨δ, hδ, hd⟩ := cepsScaledSurrogatePair_holomorphic_near_joint_of_nonzero
      dom hW hθ hD hf hη hM N hN lam hz hne (hjoint b hb) (hWidth hb)
    have hdat := hd.differentiableAt ((isOpen_ball.prod isOpen_ball).mem_nhds
      (show (b, z) ∈ ball b δ ×ˢ ball z δ from ⟨mem_ball_self hδ, mem_ball_self hδ⟩))
    exact (hdat.comp b (hcurve b)).differentiableWithinAt
  refine ⟨hFull, fun hlam => ?_⟩
  have hH := (cepsScaledSurrogateHalfEntrance_differentiableOn dom hW hθ hD
    (M := M) hf hη N hN lam hlam hz).mono hP
  intro b hb
  obtain ⟨δ, hδ, hB, hDB⟩ := cepsScaledSurrogateHalfBridge_holomorphic_near_joint
    dom hW hθ hD hf hη N hN lam hz hne (hjoint b hb)
  have hmem := (isOpen_ball.prod isOpen_ball).mem_nhds
    (show (b, z) ∈ ball b δ ×ˢ ball z δ from ⟨mem_ball_self hδ, mem_ball_self hδ⟩)
  have hB' := (hB.differentiableAt hmem).comp b (hcurve b)
  have hDB' := (hDB.differentiableAt hmem).comp b (hcurve b)
  have hH' := hH.differentiableAt (isOpen_ball.mem_nhds hb)
  have hw : DifferentiableAt ℂ (fun c : ℂ => 1 + c * (lam : ℂ)) b := by fun_prop
  have hwne := (cepsComplexScaled_width_bounds lam (hWidth hb)).2.1
  have hO := ((hw.inv hwne).neg.mul hDB').sub (differentiableAt_id.mul hB')
  have hExp : DifferentiableAt ℂ (fun c : ℂ => exp ((c * z) * (1 + c * lam))) b := by fun_prop
  have hd := (hExp.mul (hH'.pow 2)).mul hO
  unfold cepsScaledSurrogateHalfPair
  simpa only [Function.comp_apply, Pi.mul_apply, Pi.sub_apply,
    Pi.neg_apply, Pi.inv_apply, Pi.pow_apply, id_eq, one_div] using!
      (hd.differentiableWithinAt (s := U))

include hW hθ hD in
theorem cepsScaledSurrogateSubtractedPair_outer_differentiableOn {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) (hne : lam ≠ 0 ∨ z ≠ 0) :
    DifferentiableOn ℂ (cepsScaledSurrogateSubtractedPair dom ρW N lam z)
      (ball 0 (dom.outerPairScaleRadius N M lam z)) := by
  obtain ⟨hF, hH⟩ := cepsScaledSurrogatePairs_outer_differentiableOn dom hW hθ hD hf hη hM N hN lam hz hne
  unfold cepsScaledSurrogateSubtractedPair
  split_ifs with h
  · exact hF.sub (hH h)
  · exact hF

end PGM
