import PLAStochastic.Affine.Moments.Optimal.Survival.Spatial.CoefficientCollection
import PLAStochastic.Affine.Moments.Optimal.Survival.Image.Convergence
import PLAStochastic.Affine.Moments.Optimal.Survival.Spatial.SignedIntegral
import PLAStochastic.Affine.Moments.Optimal.Survival.Spatial.BoundaryLimit

/-! # Exact finite reindexing of the genuine image integrals -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def optimalImageSpatialClosed (n : ℕ) (T : ℝ) : ℝ :=
  let m := (n:ℝ)+1
  let c := optimalQImageCoefficientC n
  let b := optimalQImageCoefficientB n
  imageEqualClosed m T c b+imageEqualClosed (m+1) T c b+imageMixedClosed m T c b

theorem optimalImageSpatialClosed_collection (n : ℕ) {T : ℝ} (hT : 0<T) :
    optimalImageSpatialClosed n T=optimalImageMode n (4*T)+
      optimalImageSpatialBoundary (n+1) T-optimalImageSpatialBoundary n T := by
  have hA := optimalImageCoefficientA_collection n T
  have hB := optimalImageCoefficientB_collection n T
  have hC : 4*optimalQImageCoefficientB n+4*optimalQImagePreviousB n=4*((n:ℝ)+1)^2 := by
    unfold optimalQImageCoefficientB optimalQImagePreviousB
    ring
  have hD : -8*optimalQImageCoefficientB n= -4*((n:ℝ)+1)*(((n:ℝ)+1)+1) := by
    unfold optimalQImageCoefficientB
    ring
  rw [optimalImageMode_of_pos n (by positivity : 0<4*T)]
  simp only [optimalImageSpatialClosed,optimalImageSpatialBoundary,imageEqualClosed,imageMixedClosed,
    optimalQImagePreviousC_succ,optimalQImagePreviousB_succ,Nat.cast_add,Nat.cast_one]
  linear_combination (norm := ring_nf)
    Real.exp (-2*((n:ℝ)+1)^2/T)*hA+
    Real.exp (-2*((n:ℝ)+1)*(((n:ℝ)+1)+1)/T)*hB+
    exponentialIntegralE1 (2*((n:ℝ)+1)^2/T)*hC+
    exponentialIntegralE1 (2*((n:ℝ)+1)*(((n:ℝ)+1)+1)/T)*hD

/-- Each actual spatial image equals its final Ψ term plus two explicit adjacent boundaries. -/
theorem optimalImageSpatialMode_collection (n : ℕ) {T : ℝ} (hT : 0<T) :
    optimalImageSpatialMode n T=optimalImageMode n (4*T)+
      optimalImageSpatialBoundary (n+1) T-optimalImageSpatialBoundary n T := by
  rw [optimalImageSpatialMode_closed n hT]
  exact optimalImageSpatialClosed_collection n hT

/-- Exact finite reindexing, including the source of the constant one. -/
theorem sum_range_optimalImageSpatialMode {T : ℝ} (hT : 0<T) (N : ℕ) :
    (∑ n ∈ Finset.range N, optimalImageSpatialMode n T)=
      1+(∑ n ∈ Finset.range N, optimalImageMode n (4*T))+optimalImageSpatialBoundary N T := by
  induction N with
  | zero => simp [optimalImageSpatialBoundary_zero]
  | succ N ih =>
    rw [Finset.sum_range_succ,Finset.sum_range_succ,ih,optimalImageSpatialMode_collection N hT]
    ring

/-- The finite sums of the actual spatial images converge to the explicit image series. -/
theorem tendsto_sum_range_optimalImageSpatialMode {T : ℝ} (hT : 0<T) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, optimalImageSpatialMode n T) atTop
      (𝓝 (optimalImageSeries (4*T))) := by
  simp_rw [sum_range_optimalImageSpatialMode hT]
  have hs := (summable_optimalImageMode (4*T)).hasSum.tendsto_sum_nat
  convert! (tendsto_const_nhds.add hs).add (tendsto_optimalImageSpatialBoundary hT) using 1
  simp [optimalImageSeries]

end BrownianAffine
