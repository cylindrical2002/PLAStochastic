import PLAStochastic.Affine.Extrema.OrderedVector

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

theorem slopeUpper_neg_zero (g : Path 1) : slopeUpper (-g) 0 = -slopeLower g 0 := by
  obtain ⟨t,ht⟩ := slopeUpper_attained (-g) 0
  obtain ⟨u,hu⟩ := slopeLower_attained g 0
  have hlow := slopeLower_le_residual g 0 t
  have hupp := slopeResidual_le_upper (-g) 0 u
  simp only [slopeResidual,zero_mul,sub_zero,ContinuousMap.neg_apply] at *
  linarith

theorem slopeLower_neg_zero (g : Path 1) : slopeLower (-g) 0 = -slopeUpper g 0 := by
  have h := slopeUpper_neg_zero (-g)
  simp only [neg_neg] at h
  linarith

theorem lowerTime_neg_zero_of_differentiable (g : Path 1)
    (hu : DifferentiableAt ℝ (slopeUpper g) 0) : lowerTime (-g) 0=upperTime g 0 := by
  apply upperTime_unique_of_differentiable g hu
  have h := lowerTime_attains (-g) 0
  rw [slopeLower_neg_zero] at h
  simp only [slopeResidual,zero_mul,sub_zero,ContinuousMap.neg_apply] at *
  linarith

theorem upperTime_neg_zero_of_differentiable (g : Path 1)
    (hl : DifferentiableAt ℝ (slopeLower g) 0) : upperTime (-g) 0=lowerTime g 0 := by
  apply lowerTime_unique_of_differentiable g hl
  have h := upperTime_attains (-g) 0
  rw [slopeUpper_neg_zero] at h
  simp only [slopeResidual,zero_mul,sub_zero,ContinuousMap.neg_apply] at *
  linarith

/-- Spatial reflection swaps both extremal values and both extremum times. -/
def extremaReflection (p : ExtremaVector) : ExtremaVector :=
  (-p.2.1,-p.1,p.2.2.2.1,p.2.2.1,-p.2.2.2.2)

theorem continuous_extremaReflection : Continuous extremaReflection := by
  unfold extremaReflection
  fun_prop

theorem extremaReflection_involutive : Function.Involutive extremaReflection := by
  intro p
  simp only [extremaReflection,neg_neg]

theorem extremaReflection_preimage_ordered : extremaReflection ⁻¹' orderedExtremaDomain =
    reverseOrderedExtremaDomain := by
  ext p
  simp only [mem_preimage,orderedExtremaDomain,reverseOrderedExtremaDomain,extremaReflection,
    mem_ofPred_eq,neg_lt_zero,neg_lt_neg_iff,neg_pos]
  tauto

theorem extremaReflection_preimage_reverse : extremaReflection ⁻¹' reverseOrderedExtremaDomain =
    orderedExtremaDomain := by
  rw [←extremaReflection_preimage_ordered,←preimage_comp]
  rw [show extremaReflection ∘ extremaReflection=id from funext extremaReflection_involutive]
  rfl

theorem unitPath_processPath_neg {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (B · ω)) (T : ℝ≥0) :
    unitPath (processPath (-B) ω) T = -unitPath (processPath B ω) T := by
  have hn : Continuous ((-B) · ω) := hc.neg
  apply DFunLike.ext
  intro u
  rw [ContinuousMap.neg_apply,unitPath_processPath_apply hn,unitPath_processPath_apply hc]
  rfl

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- Reflection of the actual five-variable Brownian vector holds on one full-measure event. -/
theorem brownianExtremaVector_neg_ae (hB : IsBrownianReal B μ) :
    brownianExtremaVector (-B) =ᵐ[μ] extremaReflection ∘ brownianExtremaVector B := by
  filter_upwards [hB.cont,brownian_upper_lower_differentiable_ae hB 0] with ω hc hd
  have hg : unitPath (processPath (-B) ω) 1 = -unitPath (processPath B ω) 1 := by
    simpa only [NNReal.coe_one] using unitPath_processPath_neg hc 1
  simp only [brownianExtremaVector,hg,slopeLower_neg_zero,slopeUpper_neg_zero,
    lowerTime_neg_zero_of_differentiable _ hd.1,upperTime_neg_zero_of_differentiable _ hd.2,
    Function.comp_def,extremaReflection,Pi.neg_apply]

end BrownianAffine
