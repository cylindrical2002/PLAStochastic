import PLAStochastic.Affine.Moments.Optimal.Survival.Spatial.Coefficients

/-! # The actual boundary terms produced by collecting spatial images -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- The coefficients with manuscript index m=n, including the absent m=0 image. -/
def optimalQImagePreviousB (n : ℕ) : ℝ := (n:ℝ)*((n:ℝ)+1)/2

def optimalQImagePreviousC (n : ℕ) : ℝ := (n:ℝ)*((n:ℝ)+1)*(2*(n:ℝ)+1)/6

/-- The complete spatial reindexing boundary; index zero is exactly -1. -/
def optimalImageSpatialBoundary (n : ℕ) (T : ℝ) : ℝ :=
  let m := (n:ℝ)+1
  let c := optimalQImagePreviousC n
  let b := optimalQImagePreviousB n
  (imageEqualMiddleCoefficient m T c b-4*c/m)*Real.exp (-2*m^2/T)+
  4*b*exponentialIntegralE1 (2*m^2/T)+
  imageEqualUpperCoefficient m T c b*Real.exp (-2*m*(m+1)/T)-
  imageEqualLowerCoefficient m T (optimalQImageCoefficientC n) (optimalQImageCoefficientB n)*
    Real.exp (-2*m*(m-1)/T)

theorem optimalQImagePreviousB_succ (n : ℕ) :
    optimalQImagePreviousB (n+1)=optimalQImageCoefficientB n := by
  unfold optimalQImagePreviousB optimalQImageCoefficientB
  push_cast
  ring

theorem optimalQImagePreviousC_succ (n : ℕ) :
    optimalQImagePreviousC (n+1)=optimalQImageCoefficientC n := by
  unfold optimalQImagePreviousC optimalQImageCoefficientC
  push_cast
  ring

theorem optimalImageSpatialBoundary_zero (T : ℝ) : optimalImageSpatialBoundary 0 T= -1 := by
  simp [optimalImageSpatialBoundary,optimalQImagePreviousC,optimalQImagePreviousB,
    optimalQImageCoefficientC,optimalQImageCoefficientB,imageEqualLowerCoefficient,
    imageEqualMiddleCoefficient,imageEqualUpperCoefficient]
  ring

end BrownianAffine
