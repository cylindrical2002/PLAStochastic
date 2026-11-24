import PLAStochastic.Affine.Moments.Optimal.Survival.Kernel.TimeContinuity
import PLAStochastic.ForMathlib.MeasureTheory.Integral.RectangleAverage
import PLAStochastic.Affine.Moments.Optimal.Laplace.ConvolutionReal

/-! # Identification of the continuous representation with the genuine Q convolution -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

theorem measurable_optimalSurvivalEdgeWeight (a : ℝ) :
    Measurable (fun t : ℝ => ENNReal.ofReal (Real.exp (-t/2)*heatBoundaryLeft 1 t a)) := by
  exact ((by fun_prop : Measurable (fun t : ℝ => Real.exp (-t/2))).mul
    ((measurable_heatBoundaryLeft 1).comp (f := fun t : ℝ => (a,t)) (by fun_prop))).ennreal_ofReal

theorem lintegral_optimalSurvivalEdgeMeasure (a : ℝ) {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ t, F t ∂optimalSurvivalEdgeMeasure a) = ∫⁻ t in Ioi (0 : ℝ),
      ENNReal.ofReal (Real.exp (-t/2)*heatBoundaryLeft 1 t a) * F t := by
  exact lintegral_withDensity_eq_lintegral_mul _ (measurable_optimalSurvivalEdgeWeight a) hF

theorem optimalSurvivalWeightedKernel_eq {a b v u : ℝ} (T : ℝ)
    (ha : a ∈ Ioo 0 1) (hb : b ∈ Ioo 0 1) (hv : 0 < v) (hu : 0 < u) :
    ENNReal.ofReal (Real.exp (-v/2)*heatBoundaryLeft 1 v a) *
      (ENNReal.ofReal (Real.exp (-u/2)*heatBoundaryLeft 1 u (1-b)) *
        ENNReal.ofReal (optimalSurvivalMiddleKernel (T-v-u))) =
      ENNReal.ofReal (Real.exp (-T/2)) * (Iio (T-v)).indicator
        (fun u => ENNReal.ofReal (optimalMomentConvolutionIntegrand a b T v (T-v-u))) u := by
  have hb' : 1-b ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hb.2], by linarith [hb.1]⟩
  by_cases hw : 0 < T-v-u
  · have hu' : u ∈ Iio (T-v) := by change u < T-v; linarith
    rw [indicator_of_mem hu']
    have hA : 0 ≤ Real.exp (-v/2)*heatBoundaryLeft 1 v a :=
      mul_nonneg (Real.exp_nonneg _) (heatBoundaryLeft_strictlyPositive (by norm_num) hv ha).le
    have hR : 0 ≤ Real.exp (-u/2)*heatBoundaryLeft 1 u (1-b) :=
      mul_nonneg (Real.exp_nonneg _) (heatBoundaryLeft_strictlyPositive (by norm_num) hu hb').le
    rw [← ENNReal.ofReal_mul hR, ← ENNReal.ofReal_mul hA,
      ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
    congr 1
    unfold optimalSurvivalMiddleKernel heatCrossZeroExtension optimalMomentConvolutionIntegrand
    rw [if_pos hw, show T-v-(T-v-u)=u by ring, heatBoundaryRight_reflection (by norm_num)]
    have he : Real.exp (-v/2)*Real.exp (-u/2)*Real.exp (-(T-v-u)/2) = Real.exp (-T/2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    calc
      _ = (Real.exp (-v/2)*Real.exp (-u/2)*Real.exp (-(T-v-u)/2))*
          (heatBoundaryLeft 1 v a*((T-v-u)*heatCrossBoundary 1 (T-v-u))*heatBoundaryLeft 1 u (1-b)) := by ring
      _ = _ := by rw [he]
  · have hu' : u ∉ Iio (T-v) := by simp only [mem_Iio]; linarith
    simp only [optimalSurvivalMiddleKernel,
      heatCrossZeroExtension_of_nonpos (le_of_not_gt hw), mul_zero, ENNReal.ofReal_zero,
      indicator_of_notMem hu']

theorem lintegral_reflect_positive_interval (F : ℝ → ℝ≥0∞) (c : ℝ) :
    (∫⁻ u in Ioo (0 : ℝ) c, F (c-u)) = ∫⁻ w in Ioo (0 : ℝ) c, F w := by
  have hh := setLIntegral_affine_preimage_eq_div F (S := Ioo 0 c) measurableSet_Ioo c
    (by norm_num : (-1 : ℝ) ≠ 0)
  have he : (fun u : ℝ => c+(-1)*u) ⁻¹' Ioo 0 c = Ioo 0 c := by
    ext u
    simp only [mem_preimage, mem_Ioo]
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  rw [he] at hh
  simpa only [neg_one_mul, ← sub_eq_add_neg, abs_neg, abs_one, ENNReal.ofReal_one, div_one] using hh

theorem lintegral_optimalSurvivalEdgeProduct {a b : ℝ}
    (ha : a ∈ Ioo 0 1) (hb : b ∈ Ioo 0 1) {F : ℝ × ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ p, F p ∂optimalSurvivalEdgeProduct a b) = ∫⁻ v in Ioi (0 : ℝ), ∫⁻ u in Ioi (0 : ℝ),
      ENNReal.ofReal (Real.exp (-v/2)*heatBoundaryLeft 1 v a) *
        (ENNReal.ofReal (Real.exp (-u/2)*heatBoundaryLeft 1 u (1-b)) * F (v,u)) := by
  have hb' : 1-b ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hb.2], by linarith [hb.1]⟩
  have := isFiniteMeasure_optimalSurvivalEdgeMeasure ha
  have := isFiniteMeasure_optimalSurvivalEdgeMeasure hb'
  rw [optimalSurvivalEdgeProduct, lintegral_prod _ hF.aemeasurable,
    lintegral_optimalSurvivalEdgeMeasure a hF.lintegral_prod_right']
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro v hv
  dsimp only
  have hm : Measurable (fun u => F (v,u)) := hF.comp (by fun_prop)
  rw [lintegral_optimalSurvivalEdgeMeasure (1-b) hm,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

theorem ofReal_optimalSurvivalTimeIntegral {a b : ℝ}
    (ha : a ∈ Ioo 0 1) (hb : b ∈ Ioo 0 1) (T : ℝ) :
    ENNReal.ofReal (optimalSurvivalTimeIntegral a b T) =
      ENNReal.ofReal (Real.exp (-T/2))*optimalMomentConvolutionENN a b T := by
  unfold optimalSurvivalTimeIntegral
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_optimalSurvivalTimeIntegrand ha hb T)
    (Eventually.of_forall fun p => optimalSurvivalMiddleKernel_nonneg (T-p.1-p.2))]
  have hm : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (optimalSurvivalMiddleKernel (T-p.1-p.2))) :=
    (continuous_optimalSurvivalMiddleKernel.comp (by fun_prop)).measurable.ennreal_ofReal
  rw [lintegral_optimalSurvivalEdgeProduct ha hb hm]
  unfold optimalMomentConvolutionENN
  rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro v hv
  dsimp only
  have he : (∫⁻ u in Ioi (0 : ℝ),
      ENNReal.ofReal (Real.exp (-v/2)*heatBoundaryLeft 1 v a) *
        (ENNReal.ofReal (Real.exp (-u/2)*heatBoundaryLeft 1 u (1-b)) *
          ENNReal.ofReal (optimalSurvivalMiddleKernel (T-v-u)))) =
      ENNReal.ofReal (Real.exp (-T/2))*∫⁻ u in Ioo (0 : ℝ) (T-v),
        ENNReal.ofReal (optimalMomentConvolutionIntegrand a b T v (T-v-u)) := by
    calc
      _ = ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-T/2)) * (Iio (T-v)).indicator
          (fun u => ENNReal.ofReal (optimalMomentConvolutionIntegrand a b T v (T-v-u))) u := by
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro u hu
        exact optimalSurvivalWeightedKernel_eq T ha hb hv hu
      _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
        rw [show Iio (T-v) ∩ Ioi (0 : ℝ) = Ioo 0 (T-v) by
          ext u
          simp only [mem_inter_iff,mem_Iio,mem_Ioi,mem_Ioo,and_comm]]
  rw [he]
  congr 1
  exact lintegral_reflect_positive_interval
    (fun w => ENNReal.ofReal (optimalMomentConvolutionIntegrand a b T v w)) (T-v)

theorem optimalMomentConvolutionENN_ne_top {a b : ℝ}
    (ha : a ∈ Ioo 0 1) (hb : b ∈ Ioo 0 1) (T : ℝ) :
    optimalMomentConvolutionENN a b T ≠ ∞ := by
  have hh : ENNReal.ofReal (Real.exp (-T/2))*optimalMomentConvolutionENN a b T ≠ ∞ := by
    rw [←ofReal_optimalSurvivalTimeIntegral ha hb T]
    exact ENNReal.ofReal_ne_top
  exact (ENNReal.lt_top_of_mul_ne_top_right hh
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne').ne

theorem ofReal_optimalMomentConvolution_eq {a b : ℝ}
    (ha : a ∈ Ioo 0 1) (hb : b ∈ Ioo 0 1) (T : ℝ) :
    ENNReal.ofReal (optimalMomentConvolution a b T)=optimalMomentConvolutionENN a b T :=
  ofReal_optimalMomentConvolution_eq_of_finite ha hb (optimalMomentConvolutionENN_ne_top ha hb T)

theorem optimalMomentConvolution_eq_timeIntegral {a b : ℝ}
    (ha : a ∈ Ioo 0 1) (hb : b ∈ Ioo 0 1) (T : ℝ) :
    optimalMomentConvolution a b T=Real.exp (T/2)*optimalSurvivalTimeIntegral a b T := by
  have hh := ofReal_optimalSurvivalTimeIntegral ha hb T
  rw [←ofReal_optimalMomentConvolution_eq ha hb T,←ENNReal.ofReal_mul (Real.exp_nonneg _)] at hh
  have hn : 0 ≤ optimalSurvivalTimeIntegral a b T :=
    integral_nonneg (fun p => optimalSurvivalMiddleKernel_nonneg (T-p.1-p.2))
  have he := (ENNReal.ofReal_eq_ofReal_iff hn (mul_nonneg (Real.exp_nonneg _)
    (optimalMomentConvolution_nonneg ha hb T))).mp hh
  rw [he,←mul_assoc,←Real.exp_add,show T/2 + -T/2=0 by ring,Real.exp_zero,one_mul]

theorem continuous_optimalMomentConvolution_time {a b : ℝ}
    (ha : a ∈ Ioo 0 1) (hb : b ∈ Ioo 0 1) :
    Continuous (optimalMomentConvolution a b) := by
  have he : optimalMomentConvolution a b = fun T => Real.exp (T/2)*optimalSurvivalTimeIntegral a b T :=
    funext (optimalMomentConvolution_eq_timeIntegral ha hb)
  rw [he]
  exact (by fun_prop : Continuous (fun T : ℝ => Real.exp (T/2))).mul
    (continuous_optimalSurvivalTimeIntegral ha hb)

theorem exists_bound_optimalMomentConvolution_time (U : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a ∈ Ioo (0 : ℝ) 1, ∀ b ∈ Ioo (0 : ℝ) 1, ∀ T ≤ U,
      ‖optimalMomentConvolution a b T‖ ≤ M := by
  obtain ⟨M,hM0,hM⟩ := exists_bound_optimalSurvivalTimeIntegral
  refine ⟨Real.exp (U/2)*M,by positivity,?_⟩
  intro a ha b hb T hT
  rw [optimalMomentConvolution_eq_timeIntegral ha hb, norm_mul,
    Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul (Real.exp_le_exp.mpr (by linarith)) (hM a ha b hb T)
    (norm_nonneg _) (Real.exp_nonneg _)

end BrownianAffine
