import PLAStochastic.ForMathlib.Probability.Gaussian.HyperbolaSubstitution

/-! # Exact Gaussian integrals after hyperbola and reciprocal substitutions -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

def gaussianHyperbolaKernel (a b x : ℝ) : ℝ :=
  Real.exp (-(gaussianHyperbola a b x)^2/2)

theorem measurable_gaussianHyperbolaKernel (a b : ℝ) :
    Measurable (gaussianHyperbolaKernel a b) := by
  unfold gaussianHyperbolaKernel gaussianHyperbola
  fun_prop

theorem gaussianHyperbolaKernel_pos (a b x : ℝ) : 0 < gaussianHyperbolaKernel a b x :=
  Real.exp_pos _

private theorem integrable_standardGaussian :
    Integrable (fun y : ℝ => Real.exp (-y^2/2)) volume := by
  convert! integrable_exp_neg_mul_sq (by norm_num : 0 < (1/2 : ℝ)) using 1
  funext y
  congr 1
  ring

private theorem integral_standardGaussian :
    (∫ y : ℝ, Real.exp (-y^2/2))=Real.sqrt (2*Real.pi) := by
  have he : (fun y : ℝ => Real.exp (-y^2/2))=fun y => Real.exp (-(1/2:ℝ)*y^2) := by
    funext y; congr 1; ring
  rw [he, integral_gaussian]
  congr 1
  ring

theorem integrable_gaussianHyperbola_weighted {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun x => (a+b/x^2)*gaussianHyperbolaKernel a b x) (Ioi 0) := by
  have hi := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun x (hx : x ∈ Ioi (0:ℝ)) => (hasDerivAt_gaussianHyperbola a b hx.ne').hasDerivWithinAt)
    (strictMonoOn_gaussianHyperbola ha hb).injOn (fun y : ℝ => Real.exp (-y^2/2))
  rw [image_gaussianHyperbola ha hb] at hi
  have hg := hi.mp (by simpa only [integrableOn_univ] using integrable_standardGaussian)
  apply hg.congr_fun _ measurableSet_Ioi
  intro x hx
  simp only [smul_eq_mul, gaussianHyperbolaKernel,
    abs_of_nonneg (by positivity : 0 ≤ a+b/x^2)]

theorem integral_gaussianHyperbola_weighted {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x in Ioi (0:ℝ), (a+b/x^2)*gaussianHyperbolaKernel a b x)=Real.sqrt (2*Real.pi) := by
  have hi := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun x (hx : x ∈ Ioi (0:ℝ)) => (hasDerivAt_gaussianHyperbola a b hx.ne').hasDerivWithinAt)
    (strictMonoOn_gaussianHyperbola ha hb).injOn (fun y : ℝ => Real.exp (-y^2/2))
  rw [image_gaussianHyperbola ha hb, setIntegral_univ, integral_standardGaussian] at hi
  rw [hi]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  simp only [smul_eq_mul, gaussianHyperbolaKernel,
    abs_of_nonneg (by positivity : 0 ≤ a+b/x^2)]

theorem integrable_gaussianHyperbolaKernel {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (gaussianHyperbolaKernel a b) (Ioi 0) := by
  apply ((integrable_gaussianHyperbola_weighted ha hb).div_const a).mono'
    (measurable_gaussianHyperbolaKernel a b).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (gaussianHyperbolaKernel_pos a b x)]
  apply (le_div_iff₀ ha).mpr
  have hp := gaussianHyperbolaKernel_pos a b x
  have hn : 0 ≤ b/x^2 := by positivity
  nlinarith

theorem integrable_gaussianHyperbola_reciprocal_weight {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun x => (b/x^2)*gaussianHyperbolaKernel a b x) (Ioi 0) := by
  apply (integrable_gaussianHyperbola_weighted ha hb).mono'
    ((measurable_const.div (measurable_id.pow_const 2)).mul
      (measurable_gaussianHyperbolaKernel a b)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hp := gaussianHyperbolaKernel_pos a b x
  dsimp only [Pi.mul_apply, Pi.div_apply, id_eq]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith

theorem integral_gaussianHyperbola_reciprocal {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x in Ioi (0:ℝ), (b/x^2)*gaussianHyperbolaKernel a b x)=
      a*(∫ x in Ioi (0:ℝ), gaussianHyperbolaKernel a b x) := by
  have hinj : Set.InjOn (gaussianReciprocal a b) (Ioi 0) :=
    (show Function.Involutive (gaussianReciprocal a b) from
      fun _ => gaussianReciprocal_involutive ha.ne' hb.ne').injective.injOn
  have hi := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun x (hx : x ∈ Ioi (0:ℝ)) => (hasDerivAt_gaussianReciprocal ha.ne' hx.ne').hasDerivWithinAt)
    hinj (gaussianHyperbolaKernel a b)
  rw [image_gaussianReciprocal ha hb] at hi
  have he : (∫ x in Ioi (0:ℝ), gaussianHyperbolaKernel a b x)=
      (∫ x in Ioi (0:ℝ), ((b/x^2)*gaussianHyperbolaKernel a b x)/a) := by
    rw [hi]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [smul_eq_mul, abs_of_nonpos (by apply div_nonpos_of_nonpos_of_nonneg; linarith; positivity)]
    unfold gaussianHyperbolaKernel
    rw [gaussianHyperbola_reciprocal ha.ne' hb.ne' hx.ne', neg_sq]
    ring
  rw [integral_div] at he
  exact (eq_div_iff ha.ne').mp he |>.symm.trans (mul_comm _ _)

theorem integral_gaussianHyperbolaKernel {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x in Ioi (0:ℝ), gaussianHyperbolaKernel a b x)=Real.sqrt (2*Real.pi)/(2*a) := by
  have h := integral_gaussianHyperbola_weighted ha hb
  simp_rw [add_mul] at h
  rw [integral_add ((integrable_gaussianHyperbolaKernel ha hb).const_mul a)
    (integrable_gaussianHyperbola_reciprocal_weight ha hb), integral_const_mul,
    integral_gaussianHyperbola_reciprocal ha hb] at h
  apply (eq_div_iff (by positivity : 2*a ≠ 0)).mpr
  linarith

end BrownianAffine
