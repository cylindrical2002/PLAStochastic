import PLAStochastic.ForMathlib.Analysis.SpecialFunctions.ExponentialUnitMoments
import PLAStochastic.Affine.Moments.Optimal.Integrals.RemainingClosedForms

/-! # The actual spatial generating integral in the optimal-moment calculation -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- The separate second parameter is held fixed during all moment derivatives. -/
def optimalSpatialGenerating (k h : ℝ) : ℝ :=
  ∫ b : ℝ in (0)..1, ∫ a : ℝ in (0)..1,
    Real.cosh (h*(b-a))*Real.sinh (k*(1-a))*Real.sinh (k*b)

def spatialExponentialDifference (k h u : ℝ) : ℝ :=
  Real.exp ((k+h)*u)-Real.exp ((h-k)*u)

theorem continuous_spatialExponentialDifference (k h : ℝ) :
    Continuous (spatialExponentialDifference k h) := by
  unfold spatialExponentialDifference
  fun_prop

theorem integral_spatialExponentialDifference (k h : ℝ) :
    (∫ u : ℝ in (0)..1, spatialExponentialDifference k h u)=
      exponentialUnitMoment 0 (k+h)-exponentialUnitMoment 0 (h-k) := by
  unfold spatialExponentialDifference
  rw [intervalIntegral.integral_sub
    ((by fun_prop : Continuous (fun u : ℝ => Real.exp ((k+h)*u))).intervalIntegrable 0 1)
    ((by fun_prop : Continuous (fun u : ℝ => Real.exp ((h-k)*u))).intervalIntegrable 0 1),
    exponentialUnitMoment_eq_intervalIntegral,exponentialUnitMoment_eq_intervalIntegral]
  simp only [pow_zero,one_mul]

theorem optimalSpatial_kernel_expansion (k h a b : ℝ) :
    Real.cosh (h*(b+a-1))*Real.sinh (k*a)*Real.sinh (k*b)=
      (Real.exp (-h)*spatialExponentialDifference k h a*spatialExponentialDifference k h b+
        Real.exp h*spatialExponentialDifference k (-h) a*spatialExponentialDifference k (-h) b)/8 := by
  simp only [spatialExponentialDifference,Real.cosh_eq,Real.sinh_eq,
    mul_sub,mul_add,add_mul,sub_mul,neg_mul,Real.exp_sub,Real.exp_add,Real.exp_neg,mul_one]
  field_simp
  ring

theorem intervalDoubleIntegral_separated {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (c d : ℝ) :
    (∫ b : ℝ in (0)..1, ∫ a : ℝ in (0)..1, c*f a*f b+d*g a*g b)=
      c*(∫ a : ℝ in (0)..1, f a)^2+d*(∫ a : ℝ in (0)..1, g a)^2 := by
  have hinner (b : ℝ) : (∫ a : ℝ in (0)..1, c*f a*f b+d*g a*g b)=
      c*(∫ a : ℝ in (0)..1, f a)*f b+d*(∫ a : ℝ in (0)..1, g a)*g b := by
    rw [intervalIntegral.integral_add
      (((hf.intervalIntegrable 0 1).const_mul c).mul_const (f b))
      (((hg.intervalIntegrable 0 1).const_mul d).mul_const (g b))]
    simp only [intervalIntegral.integral_mul_const,intervalIntegral.integral_const_mul]
  simp_rw [hinner]
  rw [intervalIntegral.integral_add
    ((hf.intervalIntegrable 0 1).const_mul (c*∫ a : ℝ in (0)..1, f a))
    ((hg.intervalIntegrable 0 1).const_mul (d*∫ a : ℝ in (0)..1, g a))]
  simp only [intervalIntegral.integral_const_mul]
  ring

/-- An everywhere regular exponential representation of the spatial integral. -/
theorem optimalSpatialGenerating_eq_exponentialMoments (k h : ℝ) :
    optimalSpatialGenerating k h=
      (Real.exp (-h)*(exponentialUnitMoment 0 (k+h)-exponentialUnitMoment 0 (h-k))^2+
        Real.exp h*(exponentialUnitMoment 0 (k-h)-exponentialUnitMoment 0 (-h-k))^2)/8 := by
  have hchange (b : ℝ) :
      (∫ a : ℝ in (0)..1, Real.cosh (h*(b-a))*Real.sinh (k*(1-a))*Real.sinh (k*b))=
      ∫ a : ℝ in (0)..1, Real.cosh (h*(b+a-1))*Real.sinh (k*a)*Real.sinh (k*b) := by
    have he : (fun a : ℝ => Real.cosh (h*(b-a))*Real.sinh (k*(1-a))*Real.sinh (k*b))=
        fun a : ℝ => (fun u : ℝ => Real.cosh (h*(b+u-1))*Real.sinh (k*u)*Real.sinh (k*b)) (1-a) := by
      funext a
      congr 3
      ring
    rw [he]
    simpa only [sub_self,sub_zero] using! intervalIntegral.integral_comp_sub_left
      (fun u : ℝ => Real.cosh (h*(b+u-1))*Real.sinh (k*u)*Real.sinh (k*b)) (a := 0) (b := 1) 1
  unfold optimalSpatialGenerating
  simp_rw [hchange,optimalSpatial_kernel_expansion]
  simp_rw [intervalIntegral.integral_div]
  rw [intervalDoubleIntegral_separated
    (continuous_spatialExponentialDifference k h) (continuous_spatialExponentialDifference k (-h))]
  rw [integral_spatialExponentialDifference,integral_spatialExponentialDifference]
  simp only [←sub_eq_add_neg]

/-- The integral uses the same open spatial square as the probability formula. -/
theorem optimalSpatialGenerating_eq_open (k h : ℝ) :
    optimalSpatialGenerating k h=
      ∫ b : ℝ in Ioo 0 1, ∫ a : ℝ in Ioo 0 1,
        Real.cosh (h*(b-a))*Real.sinh (k*(1-a))*Real.sinh (k*b) := by
  unfold optimalSpatialGenerating
  simp_rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),integral_Ioc_eq_integral_Ioo]

/-- The manuscript's closed expression, away from its removable diagonals. -/
theorem optimalSpatialGenerating_eq_quotient {k h : ℝ} (hplus : k+h ≠ 0) (hminus : k-h ≠ 0) :
    optimalSpatialGenerating k h=
      (((k^2+h^2)*Real.sinh k^2+2*k^2)*Real.cosh h-2*k^2*Real.cosh k-
        2*k*h*Real.sinh k*Real.cosh k*Real.sinh h)/(k^2-h^2)^2 := by
  have hminus' : h-k ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp hminus).symm
  have hplus' : -h-k ≠ 0 := by intro he; apply hplus; linarith
  have hsquare : k^2-h^2 ≠ 0 := by rw [sq_sub_sq]; exact mul_ne_zero hplus hminus
  rw [optimalSpatialGenerating_eq_exponentialMoments,
    exponentialUnitMoment_zero_index hplus,exponentialUnitMoment_zero_index hminus',
    exponentialUnitMoment_zero_index hminus,exponentialUnitMoment_zero_index hplus']
  simp only [Real.cosh_eq,Real.sinh_eq,Real.exp_add,Real.exp_sub,Real.exp_neg]
  field_simp
  ring

end BrownianAffine
