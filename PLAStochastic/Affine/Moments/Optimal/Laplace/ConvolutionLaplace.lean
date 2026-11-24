import PLAStochastic.Affine.Moments.Optimal.Laplace.Convolution
import PLAStochastic.ForMathlib.MeasureTheory.Integral.TimeSimplex
import PLAStochastic.ForMathlib.Analysis.SpecialFunctions.CenteredCoth.PartialFractions

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

def optimalMomentLaplaceKernel (k a b : ℝ) : ℝ :=
  8*centeredCoth k/Real.sinh k^3*Real.sinh (k*(1-a))*Real.sinh (k*b)

private theorem laplace_convolution_point {a b k T v w : ℝ}
    (ha : a∈Ioo 0 1) (_hb : b∈Ioo 0 1) (hv : 0<v) (hw : w∈Ioo 0 (T-v)) :
    ENNReal.ofReal (Real.exp (-(k^2/2)*T))*
      ENNReal.ofReal (optimalMomentConvolutionIntegrand a b T v w)=
      ENNReal.ofReal (Real.exp (-(k^2/2)*v)*heatBoundaryLeft 1 v a)*
      ENNReal.ofReal (w*Real.exp (-(k^2/2)*w)*heatCrossBoundary 1 w)*
      ENNReal.ofReal (Real.exp (-(k^2/2)*(T-v-w))*heatBoundaryRight 1 (T-v-w) b) := by
  have hnA : 0≤Real.exp (-(k^2/2)*v)*heatBoundaryLeft 1 v a :=
    mul_nonneg (Real.exp_nonneg _) (heatBoundaryLeft_strictlyPositive (by norm_num) hv ha).le
  have hnC : 0≤w*Real.exp (-(k^2/2)*w)*heatCrossBoundary 1 w :=
    mul_nonneg (mul_nonneg hw.1.le (Real.exp_nonneg _)) (heatCrossBoundary_strictlyPositive (by norm_num) hw.1).le
  rw [←ENNReal.ofReal_mul (Real.exp_nonneg _),←ENNReal.ofReal_mul hnA,
    ←ENNReal.ofReal_mul (mul_nonneg hnA hnC)]
  congr 1
  unfold optimalMomentConvolutionIntegrand
  rw [show -(k^2/2)*T=-(k^2/2)*v+(-(k^2/2)*w+(-(k^2/2)*(T-v-w))) by ring,
    Real.exp_add,Real.exp_add]
  ring

/-- The real three-piece time convolution has the product of the three proved
boundary Laplace transforms, with no convergence assumption on Q. -/
theorem lintegral_laplace_optimalMomentConvolutionENN {a b k : ℝ}
    (ha : a∈Ioo 0 1) (hb : b∈Ioo 0 1) (hk : 0<k) :
    (∫⁻ T in Ioi (0:ℝ), ENNReal.ofReal (Real.exp (-(k^2/2)*T))*optimalMomentConvolutionENN a b T)=
      ENNReal.ofReal (optimalMomentLaplaceKernel k a b) := by
  let A : ℝ→ℝ := fun t => Real.exp (-(k^2/2)*t)*heatBoundaryLeft 1 t a
  let C : ℝ→ℝ := fun t => t*Real.exp (-(k^2/2)*t)*heatCrossBoundary 1 t
  let R : ℝ→ℝ := fun t => Real.exp (-(k^2/2)*t)*heatBoundaryRight 1 t b
  have hA : Measurable A := by
    exact (by fun_prop : Measurable (fun t : ℝ => Real.exp (-(k^2/2)*t))).mul
      ((measurable_heatBoundaryLeft 1).comp (f := fun t : ℝ => (a,t)) (by fun_prop))
  have hC : Measurable C := by
    exact ((by fun_prop : Measurable (fun t : ℝ => t*Real.exp (-(k^2/2)*t))).mul
      (measurable_heatCrossBoundary 1))
  have hR : Measurable R := by
    exact (by fun_prop : Measurable (fun t : ℝ => Real.exp (-(k^2/2)*t))).mul
      ((measurable_heatBoundaryRight 1).comp (f := fun t : ℝ => (b,t)) (by fun_prop))
  have hm : Measurable (fun p : ℝ×ℝ×ℝ => ENNReal.ofReal (A p.1)*ENNReal.ofReal (C p.2.1)*ENNReal.ofReal (R p.2.2)) :=
    ((hA.ennreal_ofReal.comp measurable_fst).mul (hC.ennreal_ofReal.comp (by fun_prop))).mul
      (hR.ennreal_ofReal.comp (by fun_prop))
  have htri := lintegral_positive_time_simplex hm
  have hstart : (∫⁻ T in Ioi (0:ℝ), ENNReal.ofReal (Real.exp (-(k^2/2)*T))*optimalMomentConvolutionENN a b T)=
      ∫⁻ T in Ioi (0:ℝ), ∫⁻ v in Ioi (0:ℝ), ∫⁻ w in Ioo (0:ℝ) (T-v),
        ENNReal.ofReal (A v)*ENNReal.ofReal (C w)*ENNReal.ofReal (R (T-v-w)) := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro T hT
    dsimp only
    unfold optimalMomentConvolutionENN
    rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro v hv
    dsimp only
    rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro w hw
    exact laplace_convolution_point ha hb hv hw
  rw [hstart,htri]
  have hint : (∫⁻ v in Ioi (0:ℝ), ∫⁻ w in Ioi (0:ℝ), ∫⁻ t in Ioi (0:ℝ),
      ENNReal.ofReal (A v)*ENNReal.ofReal (C w)*ENNReal.ofReal (R t))=
      (∫⁻ v in Ioi (0:ℝ), ENNReal.ofReal (A v))*
      (∫⁻ w in Ioi (0:ℝ), ENNReal.ofReal (C w))*
      (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (R t)) := by
    simp_rw [lintegral_const_mul _ hR.ennreal_ofReal,mul_assoc,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rw [lintegral_mul_const _ hC.ennreal_ofReal,lintegral_mul_const _ hA.ennreal_ofReal]
  rw [hint]
  have hAn : 0≤ᵐ[volume.restrict (Ioi (0:ℝ))] A := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.exp_nonneg _) (heatBoundaryLeft_strictlyPositive (by norm_num) ht ha).le
  have hCn : 0≤ᵐ[volume.restrict (Ioi (0:ℝ))] C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (mul_nonneg ht.le (Real.exp_nonneg _)) (heatCrossBoundary_strictlyPositive (by norm_num) ht).le
  have hRn : 0≤ᵐ[volume.restrict (Ioi (0:ℝ))] R := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.exp_nonneg _) (heatBoundaryRight_strictlyPositive (by norm_num) ht hb).le
  have hCi : IntegrableOn C (Ioi 0) :=
    (hasDerivAt_crossBoundaryTransform isBrownianReal_canonicalBrownian (by norm_num) (by positivity : 0<k^2/2)).1
  rw [←ofReal_integral_eq_lintegral_ofReal (integrableOn_laplace_heatBoundaryLeft (by norm_num) hk ha) hAn,
    ←ofReal_integral_eq_lintegral_ofReal hCi hCn,
    ←ofReal_integral_eq_lintegral_ofReal (integrableOn_laplace_heatBoundaryRight (by norm_num) hk hb) hRn]
  rw [←ENNReal.ofReal_mul (integral_nonneg_of_ae hAn),
    ←ENNReal.ofReal_mul (mul_nonneg (integral_nonneg_of_ae hAn) (integral_nonneg_of_ae hCn))]
  congr 1
  dsimp only [A,C,R]
  rw [integral_laplace_heatBoundaryLeft_eq_sinh (by norm_num) hk ha,
    integral_laplace_heatCrossBoundary_moment isBrownianReal_canonicalBrownian (by norm_num) hk,
    integral_laplace_heatBoundaryRight_eq_sinh (by norm_num) hk hb,boundaryPairTransform_eq (by norm_num) hk]
  unfold optimalMomentLaplaceKernel centeredCoth
  simp only [mul_one]
  field_simp
  ring

end BrownianAffine
