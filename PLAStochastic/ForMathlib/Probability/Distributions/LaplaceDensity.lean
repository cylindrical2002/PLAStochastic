import PLAStochastic.ForMathlib.Probability.Hellinger.Convolution
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The positive Laplace smoothing density

The kernel is `exp (-|x| / δ) / (2 δ)` on the whole real line. Its integrability,
normalisation and strict positivity are proved from the two half-line integrals.
Smoothing uses the actual convolution probability density.
-/

set_option autoImplicit false

namespace ProbabilityTheory

noncomputable section

open MeasureTheory Set

def laplacePdf (δ x : ℝ) : ℝ := (1 / (2 * δ)) * Real.exp (-|x| / δ)

theorem laplacePdf_pos {δ : ℝ} (hδ : 0 < δ) (x : ℝ) : 0 < laplacePdf δ x := by
  unfold laplacePdf
  positivity

theorem laplacePdf_le {δ : ℝ} (hδ : 0 < δ) (x : ℝ) : laplacePdf δ x ≤ 1 / (2 * δ) := by
  have he : Real.exp (-|x| / δ) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (abs_nonneg x)) hδ.le
  simpa only [laplacePdf, mul_one] using mul_le_mul_of_nonneg_left he
    (show 0 ≤ 1 / (2 * δ) by positivity)

theorem laplacePdf_continuous (δ : ℝ) : Continuous (laplacePdf δ) := by
  unfold laplacePdf
  fun_prop

theorem laplace_exp_eq_on_Iic (δ : ℝ) :
    EqOn (fun x => Real.exp ((1 / δ) * x)) (fun x => Real.exp (-|x| / δ)) (Iic 0) := by
  intro x hx
  dsimp only
  rw [abs_of_nonpos hx]
  congr 1
  field_simp

theorem laplace_exp_eq_on_Ioi (δ : ℝ) :
    EqOn (fun x => Real.exp ((-1 / δ) * x)) (fun x => Real.exp (-|x| / δ)) (Ioi 0) := by
  intro x hx
  dsimp only
  rw [abs_of_pos hx]
  congr 1
  field_simp

theorem laplace_exp_integrable {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun x => Real.exp (-|x| / δ)) (volume : Measure ℝ) := by
  have hn := (integrableOn_exp_mul_Iic (one_div_pos.mpr hδ) 0).congr_fun
    (laplace_exp_eq_on_Iic δ) measurableSet_Iic
  have hp := (integrableOn_exp_mul_Ioi (div_neg_of_neg_of_pos (by norm_num) hδ) 0).congr_fun
    (laplace_exp_eq_on_Ioi δ) measurableSet_Ioi
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact hn.union hp

theorem integral_laplace_exp {δ : ℝ} (hδ : 0 < δ) :
    (∫ x : ℝ, Real.exp (-|x| / δ)) = 2 * δ := by
  have hi := laplace_exp_integrable hδ
  have hn : (∫ x : ℝ in Iic 0, Real.exp (-|x| / δ)) = δ := by
    rw [← setIntegral_congr_fun measurableSet_Iic (laplace_exp_eq_on_Iic δ),
      integral_exp_mul_Iic (one_div_pos.mpr hδ) 0]
    simp
  have hp : (∫ x : ℝ in Ioi 0, Real.exp (-|x| / δ)) = δ := by
    rw [← setIntegral_congr_fun measurableSet_Ioi (laplace_exp_eq_on_Ioi δ),
      integral_exp_mul_Ioi (div_neg_of_neg_of_pos (by norm_num) hδ) 0]
    simp
  have hdis : Disjoint (Iic (0 : ℝ)) (Ioi 0) := by
    apply disjoint_left.2
    intro x hx hy
    exact (not_lt_of_ge (show x ≤ 0 from hx)) (show 0 < x from hy)
  rw [← setIntegral_univ, ← Iic_union_Ioi (a := (0 : ℝ)),
    setIntegral_union hdis measurableSet_Ioi hi.integrableOn hi.integrableOn, hn, hp]
  ring

def laplaceDensity (δ : ℝ) (hδ : 0 < δ) : HellingerDensity (volume : Measure ℝ) where
  density := laplacePdf δ
  measurable := by unfold laplacePdf; fun_prop
  nonneg x := (laplacePdf_pos hδ x).le
  integrable := (laplace_exp_integrable hδ).const_mul _
  integral_eq_one := by
    change (∫ x : ℝ, (1 / (2 * δ)) * Real.exp (-|x| / δ)) = 1
    rw [integral_const_mul, integral_laplace_exp hδ]
    rw [one_div]
    exact inv_mul_cancel₀ (by positivity)

def laplaceSmooth (p : HellingerDensity (volume : Measure ℝ))
    (δ : ℝ) (hδ : 0 < δ) : HellingerDensity (volume : Measure ℝ) :=
  p.addConvolution (laplaceDensity δ hδ)

theorem laplaceSmooth_density (p : HellingerDensity (volume : Measure ℝ))
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    (laplaceSmooth p δ hδ).density y =
      ∫ x, p.density x * laplacePdf δ (y - x) := rfl

theorem laplaceSmooth_section_integrable (p : HellingerDensity (volume : Measure ℝ))
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    Integrable (fun x => p.density x * laplacePdf δ (y - x)) volume := by
  refine (p.integrable.mul_const (1 / (2 * δ))).mono' ?_ ?_
  · exact (p.measurable.mul ((laplaceDensity δ hδ).measurable.comp
      (measurable_const.sub measurable_id))).aestronglyMeasurable
  · exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (p.nonneg x) (laplacePdf_pos hδ _).le)]
      exact mul_le_mul_of_nonneg_left (laplacePdf_le hδ _) (p.nonneg x)

theorem laplaceSmooth_pos (p : HellingerDensity (volume : Measure ℝ))
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) : 0 < (laplaceSmooth p δ hδ).density y := by
  rw [laplaceSmooth_density]
  have hg : ∀ x, 0 ≤ p.density x * laplacePdf δ (y - x) :=
    fun x => mul_nonneg (p.nonneg x) (laplacePdf_pos hδ _).le
  by_contra h
  have hz : (∫ x, p.density x * laplacePdf δ (y - x)) = 0 :=
    le_antisymm (not_lt.mp h) (integral_nonneg hg)
  have hae := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ hg)
    (laplaceSmooth_section_integrable p hδ y)).1 hz
  have hpzero : p.density =ᵐ[volume] 0 := by
    filter_upwards [hae] with x hx
    change p.density x * laplacePdf δ (y - x) = 0 at hx
    exact (mul_eq_zero.mp hx).resolve_right (laplacePdf_pos hδ _).ne'
  have hi : (∫ x, p.density x) = 0 := by rw [integral_congr_ae hpzero]; simp
  linarith [p.integral_eq_one]

theorem laplaceSmooth_continuous (p : HellingerDensity (volume : Measure ℝ))
    {δ : ℝ} (hδ : 0 < δ) : Continuous (laplaceSmooth p δ hδ).density := by
  have hb : BddAbove (range fun x => ‖laplacePdf δ x‖) := by
    refine ⟨1 / (2 * δ), ?_⟩
    rintro _ ⟨x, rfl⟩
    dsimp only
    rw [Real.norm_eq_abs, abs_of_pos (laplacePdf_pos hδ x)]
    exact laplacePdf_le hδ x
  exact hb.continuous_convolution_right_of_integrable (ContinuousLinearMap.mul ℝ ℝ)
    p.integrable (laplacePdf_continuous δ)

theorem hellinger_laplaceSmooth_le (p q : HellingerDensity (volume : Measure ℝ))
    {δ : ℝ} (hδ : 0 < δ) :
    (laplaceSmooth p δ hδ).hellinger (laplaceSmooth q δ hδ) ≤ p.hellinger q :=
  HellingerDensity.hellinger_addConvolution_le _ _ _

end

end ProbabilityTheory
