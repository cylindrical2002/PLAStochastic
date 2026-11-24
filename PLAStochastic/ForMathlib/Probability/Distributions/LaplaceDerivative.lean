import PLAStochastic.ForMathlib.Probability.Distributions.LaplaceDensity
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Differentiating actual positive Laplace smoothing

The cusp of the kernel is a single null point for each output coordinate.
A global Lipschitz bound permits differentiation under the integral even for
an arbitrary measurable input density. The resulting derivative satisfies
`|qδ'| ≤ qδ / δ` everywhere.
-/

set_option autoImplicit false

namespace ProbabilityTheory

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

def laplacePdfDerivative (δ x : ℝ) : ℝ :=
  if x < 0 then laplacePdf δ x / δ else -(laplacePdf δ x / δ)

theorem laplacePdfDerivative_measurable (δ : ℝ) : Measurable (laplacePdfDerivative δ) := by
  apply Measurable.ite measurableSet_Iio
  · exact (laplacePdf_continuous δ).measurable.div_const δ
  · exact ((laplacePdf_continuous δ).measurable.div_const δ).neg

theorem laplacePdf_hasDerivAt {δ x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (laplacePdf δ) (laplacePdfDerivative δ x) x := by
  rcases lt_or_gt_of_ne hx with hx | hx
  · have h := ((hasDerivAt_abs_neg hx).neg.div_const δ).exp.const_mul (1 / (2 * δ))
    apply h.congr_deriv
    simp only [laplacePdfDerivative, if_pos hx, laplacePdf, Pi.neg_apply]
    ring
  · have h := ((hasDerivAt_abs_pos hx).neg.div_const δ).exp.const_mul (1 / (2 * δ))
    apply h.congr_deriv
    simp only [laplacePdfDerivative, if_neg (not_lt_of_ge hx.le), laplacePdf, Pi.neg_apply]
    ring

theorem abs_laplacePdfDerivative {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    |laplacePdfDerivative δ x| = laplacePdf δ x / δ := by
  unfold laplacePdfDerivative
  split_ifs <;> simp only [abs_neg, abs_of_nonneg (div_nonneg (laplacePdf_pos hδ x).le hδ.le)]

theorem laplacePdf_lipschitz_bound {δ : ℝ} (hδ : 0 < δ) (x y : ℝ) :
    |laplacePdf δ x - laplacePdf δ y| ≤ (1 / (2 * δ ^ 2)) * |x - y| := by
  have hexp : LipschitzOnWith 1 Real.exp (Iic 0) := by
    apply (convex_Iic (0 : ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    intro x hx
    rw [← NNReal.coe_le_coe]
    simp only [coe_nnnorm, NNReal.coe_one, Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)]
    exact Real.exp_le_one_iff.2 hx
  have hx0 : -|x| / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (abs_nonneg x)) hδ.le
  have hy0 : -|y| / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (abs_nonneg y)) hδ.le
  have h := hexp.dist_le_mul _ hx0 _ hy0
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
  have he : |- |x| / δ - - |y| / δ| = |(|x| - |y|)| / δ := by
    rw [← sub_div, abs_div, abs_of_pos hδ,
      show -|x| - -|y| = -(|x| - |y|) by ring, abs_neg]
  rw [he] at h
  have he' := div_le_div_of_nonneg_right (abs_abs_sub_abs_le_abs_sub x y) hδ.le
  calc
    |laplacePdf δ x - laplacePdf δ y| =
        (1 / (2 * δ)) * |Real.exp (-|x| / δ) - Real.exp (-|y| / δ)| := by
      unfold laplacePdf
      rw [← mul_sub, abs_mul, abs_of_pos (by positivity : 0 < 1 / (2 * δ))]
    _ ≤ (1 / (2 * δ)) * (|x - y| / δ) :=
      mul_le_mul_of_nonneg_left (h.trans he') (by positivity)
    _ = _ := by ring

def laplaceSmoothDerivative (p : HellingerDensity (volume : Measure ℝ))
    (δ y : ℝ) : ℝ := ∫ x, p.density x * laplacePdfDerivative δ (y - x)

set_option backward.isDefEq.respectTransparency.types false in
theorem laplaceSmooth_hasDerivAt (p : HellingerDensity (volume : Measure ℝ))
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    HasDerivAt (laplaceSmooth p δ hδ).density (laplaceSmoothDerivative p δ y) y := by
  have h := hasDerivAt_integral_of_dominated_loc_of_lip (μ := (volume : Measure ℝ))
    (F := fun y x => p.density x * laplacePdf δ (y - x))
    (F' := fun x => p.density x * laplacePdfDerivative δ (y - x))
    (bound := fun x => p.density x * (1 / (2 * δ ^ 2))) (s := univ)
    (by simp) ?_ (laplaceSmooth_section_integrable p hδ y) ?_ ?_
    (p.integrable.mul_const _) ?_
  · exact h.2
  · exact Eventually.of_forall fun y =>
      (p.measurable.mul ((laplaceDensity δ hδ).measurable.comp
        (measurable_const.sub measurable_id))).aestronglyMeasurable
  · exact (p.measurable.mul ((laplacePdfDerivative_measurable δ).comp
      (measurable_const.sub measurable_id))).aestronglyMeasurable
  · apply ae_of_all
    intro x
    apply LipschitzWith.lipschitzOnWith
    apply LipschitzWith.of_dist_le_mul
    intro a b
    have hbound : 0 ≤ p.density x * (1 / (2 * δ ^ 2)) := by
      exact mul_nonneg (p.nonneg x) (by positivity)
    rw [Real.dist_eq, Real.dist_eq, Real.coe_nnabs, abs_of_nonneg hbound,
      ← mul_sub, abs_mul, abs_of_nonneg (p.nonneg x)]
    have he : (a - x) - (b - x) = a - b := by ring
    have h := laplacePdf_lipschitz_bound hδ (a - x) (b - x)
    rw [he] at h
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h (p.nonneg x)
  · have hne : ∀ᵐ x : ℝ ∂volume, x ≠ y := by simp [ae_iff]
    filter_upwards [hne] with x hx
    have hxy : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
    have hd := (laplacePdf_hasDerivAt (δ := δ) hxy).comp y ((hasDerivAt_id y).sub_const x)
    simpa only [Function.comp_apply, id_eq, mul_one] using hd.const_mul (p.density x)

theorem laplacePdfDerivative_integrable {δ : ℝ} (hδ : 0 < δ) :
    Integrable (laplacePdfDerivative δ) (volume : Measure ℝ) := by
  refine ((laplaceDensity δ hδ).integrable.div_const δ).mono'
    (laplacePdfDerivative_measurable δ).aestronglyMeasurable ?_
  exact ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, abs_laplacePdfDerivative hδ]
    rfl

theorem laplaceSmoothDerivative_integrable (p : HellingerDensity (volume : Measure ℝ))
    {δ : ℝ} (hδ : 0 < δ) : Integrable (laplaceSmoothDerivative p δ) volume :=
  p.integrable.integrable_convolution (L := ContinuousLinearMap.mul ℝ ℝ)
    (laplacePdfDerivative_integrable hδ)

theorem laplaceSmoothDerivative_measurable (p : HellingerDensity (volume : Measure ℝ))
    (δ : ℝ) : Measurable (laplaceSmoothDerivative p δ) := by
  have hm : Measurable (fun z : ℝ × ℝ =>
      p.density z.2 * laplacePdfDerivative δ (z.1 - z.2)) :=
    (p.measurable.comp measurable_snd).mul
      ((laplacePdfDerivative_measurable δ).comp (measurable_fst.sub measurable_snd))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem abs_laplaceSmoothDerivative_le (p : HellingerDensity (volume : Measure ℝ))
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    |laplaceSmoothDerivative p δ y| ≤ (laplaceSmooth p δ hδ).density y / δ := by
  unfold laplaceSmoothDerivative
  calc
    |∫ x, p.density x * laplacePdfDerivative δ (y - x)| ≤
        ∫ x, ‖p.density x * laplacePdfDerivative δ (y - x)‖ := by
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (fun x => p.density x * laplacePdfDerivative δ (y - x))
    _ = ∫ x, (p.density x * laplacePdf δ (y - x)) / δ := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        dsimp only
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (p.nonneg x), abs_laplacePdfDerivative hδ]
        ring
    _ = (laplaceSmooth p δ hδ).density y / δ := by
      rw [integral_div, laplaceSmooth_density]

theorem laplaceSmooth_fisher_integrand_le (p : HellingerDensity (volume : Measure ℝ))
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    laplaceSmoothDerivative p δ y ^ 2 / (laplaceSmooth p δ hδ).density y ≤
      |laplaceSmoothDerivative p δ y| / δ := by
  have hg := laplaceSmooth_pos p hδ y
  have ha := abs_laplaceSmoothDerivative_le p hδ y
  have hr : |laplaceSmoothDerivative p δ y| / (laplaceSmooth p δ hδ).density y ≤ 1 / δ := by
    rw [div_le_div_iff₀ hg hδ]
    simpa only [one_mul] using (le_div_iff₀ hδ).1 ha
  calc
    laplaceSmoothDerivative p δ y ^ 2 / (laplaceSmooth p δ hδ).density y =
        |laplaceSmoothDerivative p δ y| *
          (|laplaceSmoothDerivative p δ y| / (laplaceSmooth p δ hδ).density y) := by
      rw [← sq_abs]
      ring
    _ ≤ |laplaceSmoothDerivative p δ y| * (1 / δ) :=
      mul_le_mul_of_nonneg_left hr (abs_nonneg _)
    _ = _ := by ring

theorem laplaceSmooth_fisher_integrable (p : HellingerDensity (volume : Measure ℝ))
    {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun y => laplaceSmoothDerivative p δ y ^ 2 /
      (laplaceSmooth p δ hδ).density y) volume := by
  refine ((laplaceSmoothDerivative_integrable p hδ).norm.div_const δ).mono' ?_ ?_
  · exact (((laplaceSmoothDerivative_measurable p δ).pow_const 2).div
      (laplaceSmooth p δ hδ).measurable).aestronglyMeasurable
  · exact ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _)
        (laplaceSmooth_pos p hδ y).le), Real.norm_eq_abs]
      exact laplaceSmooth_fisher_integrand_le p hδ y

/-- The actual smoothed information is controlled by its derivative's `L¹` norm.
The additional bound by the input variation is a separate Sobolev step. -/
theorem integral_laplaceSmooth_fisher_le (p : HellingerDensity (volume : Measure ℝ))
    {δ : ℝ} (hδ : 0 < δ) :
    (∫ y, laplaceSmoothDerivative p δ y ^ 2 / (laplaceSmooth p δ hδ).density y) ≤
      (∫ y, |laplaceSmoothDerivative p δ y|) / δ := by
  rw [← integral_div]
  exact integral_mono (laplaceSmooth_fisher_integrable p hδ)
    ((laplaceSmoothDerivative_integrable p hδ).abs.div_const δ)
    (laplaceSmooth_fisher_integrand_le p hδ)

end

end ProbabilityTheory
