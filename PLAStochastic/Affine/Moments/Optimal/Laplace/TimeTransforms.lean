import PLAStochastic.ForMathlib.MeasureTheory.Measure.PositiveLaplaceMoments
import PLAStochastic.Affine.Error.Measurable
import PLAStochastic.Affine.Error.BrownianScaling
import PLAStochastic.Affine.Lifetime.GaussianBlocks
import PLAStochastic.Affine.Moments.Optimal.Laplace.LaplaceReal

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- Time-moment transforms of the actual real unit-width convolution. -/
def optimalMomentTimeTransform (n : ℕ) (a b k : ℝ) : ℝ :=
  positiveLaplaceMoment (optimalMomentConvolution a b) n (k^2/2)

private theorem integrableOn_laplace_optimalMomentConvolution_lambda {a b : ℝ}
    (ha : a∈Ioo 0 1) (hb : b∈Ioo 0 1) (lam : ℝ) (hlam : 0<lam) :
    IntegrableOn (fun t => Real.exp (-lam*t)*optimalMomentConvolution a b t) (Ioi 0) := by
  have hk : 0<Real.sqrt (2*lam) := Real.sqrt_pos.mpr (by positivity)
  have h := integrableOn_laplace_optimalMomentConvolution ha hb hk
  rwa [Real.sq_sqrt (by positivity),mul_div_cancel_left₀ _ (by norm_num : (2:ℝ)≠0)] at h

theorem integrableOn_optimalMomentTimeTransform {a b k : ℝ}
    (ha : a∈Ioo 0 1) (hb : b∈Ioo 0 1) (hk : 0<k) (n : ℕ) :
    IntegrableOn (fun t => t^n*Real.exp (-(k^2/2)*t)*optimalMomentConvolution a b t) (Ioi 0) :=
  integrableOn_positiveLaplaceMoment (G := optimalMomentConvolution a b)
    (measurable_optimalMomentConvolution.comp (f := fun t : ℝ => (a,b,t)) (by fun_prop))
    (fun t _ => optimalMomentConvolution_nonneg ha hb t)
    (integrableOn_laplace_optimalMomentConvolution_lambda ha hb) (by positivity) n

theorem optimalMomentTimeTransform_nonneg {a b : ℝ}
    (ha : a∈Ioo 0 1) (hb : b∈Ioo 0 1) (n : ℕ) (k : ℝ) :
    0≤optimalMomentTimeTransform n a b k := by
  apply setIntegral_nonneg measurableSet_Ioi
  intro t ht
  exact mul_nonneg (mul_nonneg (pow_nonneg ht.le n) (Real.exp_nonneg _))
    (optimalMomentConvolution_nonneg ha hb t)

theorem optimalMomentTimeTransform_zero {a b k : ℝ}
    (ha : a∈Ioo 0 1) (hb : b∈Ioo 0 1) (hk : 0<k) :
    optimalMomentTimeTransform 0 a b k=optimalMomentLaplaceKernel k a b := by
  simpa only [optimalMomentTimeTransform,positiveLaplaceMoment,pow_zero,one_mul] using
    integral_laplace_optimalMomentConvolution ha hb hk

/-- The operator -(1/k)d/dk on the proved Q transform inserts one genuine time factor. -/
theorem hasDerivAt_optimalMomentTimeTransform {a b k : ℝ}
    (ha : a∈Ioo 0 1) (hb : b∈Ioo 0 1) (hk : 0<k) (n : ℕ) :
    HasDerivAt (optimalMomentTimeTransform n a b) (-k*optimalMomentTimeTransform (n+1) a b k) k := by
  have hd := hasDerivAt_positiveLaplaceMoment (G := optimalMomentConvolution a b)
    (measurable_optimalMomentConvolution.comp (f := fun t : ℝ => (a,b,t)) (by fun_prop))
    (fun t _ => optimalMomentConvolution_nonneg ha hb t)
    (integrableOn_laplace_optimalMomentConvolution_lambda ha hb) (by positivity : 0<k^2/2) n
  have hk' : HasDerivAt (fun x : ℝ => x^2/2) k k := by
    convert! ((hasDerivAt_id k).pow 2).div_const 2 using 1
    simp
  have h := hd.comp k hk'
  change HasDerivAt (fun x => positiveLaplaceMoment (optimalMomentConvolution a b) n (x^2/2)) _ k
  convert! h using 1
  unfold optimalMomentTimeTransform
  ring

theorem optimalMomentTimeTransform_succ {a b k : ℝ}
    (ha : a∈Ioo 0 1) (hb : b∈Ioo 0 1) (hk : 0<k) (n : ℕ) :
    optimalMomentTimeTransform (n+1) a b k=
      -(1/k)*deriv (optimalMomentTimeTransform n a b) k := by
  rw [(hasDerivAt_optimalMomentTimeTransform ha hb hk n).deriv]
  field_simp

end BrownianAffine
