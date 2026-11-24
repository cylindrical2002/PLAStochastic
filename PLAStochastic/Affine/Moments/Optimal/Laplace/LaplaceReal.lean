import PLAStochastic.Affine.Moments.Optimal.Laplace.ConvolutionReal

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

theorem optimalMomentLaplaceKernel_nonneg {a b k : ℝ}
    (ha : a∈Ioo 0 1) (hb : b∈Ioo 0 1) (hk : 0<k) : 0≤optimalMomentLaplaceKernel k a b := by
  have hf : 0≤centeredCoth k := by
    rw [←(hasSum_centeredCoth hk).tsum_eq]
    exact tsum_nonneg (fun n => by positivity)
  have hs : 0≤Real.sinh k := (Real.sinh_pos_iff.mpr hk).le
  have ha' : 0≤Real.sinh (k*(1-a)) := (Real.sinh_pos_iff.mpr (mul_pos hk (by linarith [ha.2]))).le
  have hb' : 0≤Real.sinh (k*b) := (Real.sinh_pos_iff.mpr (mul_pos hk hb.1)).le
  unfold optimalMomentLaplaceKernel
  positivity

theorem lintegral_ofReal_laplace_optimalMomentConvolution {a b k : ℝ}
    (ha : a∈Ioo 0 1) (hb : b∈Ioo 0 1) (hk : 0<k) :
    (∫⁻ T in Ioi (0:ℝ), ENNReal.ofReal (Real.exp (-(k^2/2)*T)*optimalMomentConvolution a b T))=
      ENNReal.ofReal (optimalMomentLaplaceKernel k a b) := by
  rw [←lintegral_laplace_optimalMomentConvolutionENN ha hb hk]
  apply lintegral_congr_ae
  filter_upwards [ofReal_optimalMomentConvolution_eq_ae ha hb] with T hT
  rw [ENNReal.ofReal_mul (Real.exp_nonneg _),hT]

/-- Actual real Q is exponentially integrable for every positive Laplace parameter. -/
theorem integrableOn_laplace_optimalMomentConvolution {a b k : ℝ}
    (ha : a∈Ioo 0 1) (hb : b∈Ioo 0 1) (hk : 0<k) :
    IntegrableOn (fun T => Real.exp (-(k^2/2)*T)*optimalMomentConvolution a b T) (Ioi 0) := by
  have hm : Measurable (fun T => Real.exp (-(k^2/2)*T)*optimalMomentConvolution a b T) :=
    (by fun_prop : Measurable (fun T : ℝ => Real.exp (-(k^2/2)*T))).mul
      (measurable_optimalMomentConvolution.comp (f := fun T : ℝ => (a,b,T)) (by fun_prop))
  apply (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
    (Eventually.of_forall fun T => mul_nonneg (Real.exp_nonneg _) (optimalMomentConvolution_nonneg ha hb T))).mp
  rw [lintegral_ofReal_laplace_optimalMomentConvolution ha hb hk]
  exact ENNReal.ofReal_ne_top

/-- The manuscript's explicit Q transform is the integral of the real convolution. -/
theorem integral_laplace_optimalMomentConvolution {a b k : ℝ}
    (ha : a∈Ioo 0 1) (hb : b∈Ioo 0 1) (hk : 0<k) :
    (∫ T in Ioi (0:ℝ), Real.exp (-(k^2/2)*T)*optimalMomentConvolution a b T)=
      optimalMomentLaplaceKernel k a b := by
  have hi := integrableOn_laplace_optimalMomentConvolution ha hb hk
  have hn : 0≤ᵐ[volume.restrict (Ioi (0:ℝ))]
      (fun T => Real.exp (-(k^2/2)*T)*optimalMomentConvolution a b T) :=
    Eventually.of_forall fun T => mul_nonneg (Real.exp_nonneg _) (optimalMomentConvolution_nonneg ha hb T)
  rw [integral_eq_lintegral_of_nonneg_ae hn hi.aestronglyMeasurable,
    lintegral_ofReal_laplace_optimalMomentConvolution ha hb hk,
    ENNReal.toReal_ofReal (optimalMomentLaplaceKernel_nonneg ha hb hk)]

end BrownianAffine
