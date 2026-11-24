import PLAStochastic.ForMathlib.Analysis.SpecialFunctions.ExponentialUnitMoments
import PLAStochastic.Affine.Moments.Optimal.Integrals.RemainingClosedForms

/-! # Regular derivatives of the spatial exponential factors -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- All derivatives in the first parameter, with the second parameter fixed. -/
def spatialDifferenceMoment (n : ℕ) (k h : ℝ) : ℝ :=
  exponentialUnitMoment n (k+h)-(-1 : ℝ)^n*exponentialUnitMoment n (h-k)

theorem hasDerivAt_spatialDifferenceMoment (n : ℕ) (k h : ℝ) :
    HasDerivAt (spatialDifferenceMoment n · h) (spatialDifferenceMoment (n+1) k h) k := by
  have h1 := (hasDerivAt_exponentialUnitMoment n (k+h)).comp k ((hasDerivAt_id k).add_const h)
  have h2 := (hasDerivAt_exponentialUnitMoment n (h-k)).comp k ((hasDerivAt_id k).const_sub h)
  have hd := h1.sub (h2.const_mul ((-1 : ℝ)^n))
  convert! hd using 1
  simp only [spatialDifferenceMoment,mul_one,pow_succ]
  ring

theorem continuous_spatialDifferenceMoment (n : ℕ) (h : ℝ) :
    Continuous (spatialDifferenceMoment n · h) :=
  continuous_iff_continuousAt.mpr fun k => (hasDerivAt_spatialDifferenceMoment n k h).continuousAt

end BrownianAffine
