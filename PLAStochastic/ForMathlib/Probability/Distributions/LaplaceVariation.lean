import PLAStochastic.ForMathlib.Probability.Distributions.LaplaceDerivative
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Input variation controls the actual smoothed Fisher information

Integration by parts is performed separately on the two sides of the Laplace
cusp. Both endpoint terms are retained and cancel. Integrability of the input
and its derivative supplies the boundary conditions at infinity.
-/

set_option autoImplicit false

namespace ProbabilityTheory

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

theorem integrable_mul_laplacePdf {g : ℝ → ℝ} (hg : Integrable g volume)
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    Integrable (fun x => g x * laplacePdf δ (y - x)) volume := by
  apply hg.mul_bdd
    ((laplacePdf_continuous δ).measurable.comp
      (measurable_const.sub measurable_id)).aestronglyMeasurable
  exact ae_of_all _ fun x => by
    change ‖laplacePdf δ (y - x)‖ ≤ 1 / (2 * δ)
    rw [Real.norm_eq_abs, abs_of_pos (laplacePdf_pos hδ _)]
    exact laplacePdf_le hδ _

theorem integrable_mul_laplacePdfDerivative {g : ℝ → ℝ} (hg : Integrable g volume)
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    Integrable (fun x => g x * laplacePdfDerivative δ (y - x)) volume := by
  apply hg.mul_bdd
    ((laplacePdfDerivative_measurable δ).comp
      (measurable_const.sub measurable_id)).aestronglyMeasurable
  exact ae_of_all _ fun x => by
    change ‖laplacePdfDerivative δ (y - x)‖ ≤ (1 / (2 * δ)) / δ
    rw [Real.norm_eq_abs, abs_laplacePdfDerivative hδ]
    exact div_le_div_of_nonneg_right (laplacePdf_le hδ _) hδ.le

set_option backward.isDefEq.respectTransparency.types false in
theorem laplaceSmoothDerivative_eq_input_convolution
    (p : HellingerDensity (volume : Measure ℝ)) {p' : ℝ → ℝ}
    (hp : ∀ x, HasDerivAt p.density (p' x) x) (hp' : Integrable p' volume)
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    laplaceSmoothDerivative p δ y = ∫ x, p' x * laplacePdf δ (y - x) := by
  let v : ℝ → ℝ := fun x => laplacePdf δ (y - x)
  let v' : ℝ → ℝ := fun x => -laplacePdfDerivative δ (y - x)
  have hv : ∀ x, x ≠ y → HasDerivAt v (v' x) x := by
    intro x hx
    have h := (laplacePdf_hasDerivAt (δ := δ) (sub_ne_zero.mpr (Ne.symm hx))).comp x
      ((hasDerivAt_const x y).sub (hasDerivAt_id x))
    convert h using 1 <;> first | rfl | simp [v']
  have hpi := integrable_mul_laplacePdf p.integrable hδ y
  have hdi := integrable_mul_laplacePdf hp' hδ y
  have hki := integrable_mul_laplacePdfDerivative p.integrable hδ y
  have hvi : Integrable (p.density * v') volume := by
    exact hki.neg.congr (ae_of_all _ fun x => by simp [v', Pi.mul_apply])
  have hderiv : ∀ x, x ≠ y →
      HasDerivAt (p.density * v) ((p' * v + p.density * v') x) x := by
    intro x hx
    exact (hp x).mul (hv x hx)
  have hprod : Integrable (p' * v + p.density * v') volume := hdi.add hvi
  have htop : Tendsto (p.density * v) atTop (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi
      (fun x hx => hderiv x (ne_of_gt hx)) hprod.integrableOn hpi.integrableOn
  have hbot : Tendsto (p.density * v) atBot (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a := y - 1)
      (fun x hx => hderiv x (by have h : x ≤ y - 1 := hx; linarith))
      hprod.integrableOn hpi.integrableOn
  have hcont : Continuous (p.density * v) :=
    (continuous_iff_continuousAt.mpr fun x => (hp x).continuousAt).mul
      ((laplacePdf_continuous δ).comp (continuous_const.sub continuous_id))
  have hlo := integral_Iic_mul_deriv_eq_deriv_mul
    (a := y) (fun x hx => hp x) (fun x hx => hv x (ne_of_lt hx))
    hvi.integrableOn hdi.integrableOn
    ((hcont.tendsto y).mono_left inf_le_left) hbot
  have hhi := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := y) (fun x hx => hp x) (fun x hx => hv x (ne_of_gt hx))
    hvi.integrableOn hdi.integrableOn
    ((hcont.tendsto y).mono_left inf_le_left) htop
  have he : (∫ x, p.density x * v' x) = -(∫ x, p' x * v x) := by
    have hsplit : ∀ (g : ℝ → ℝ), Integrable g volume →
        (∫ x, g x) = (∫ x in Iic y, g x) + ∫ x in Ioi y, g x := by
      intro g hg
      have hd : Disjoint (Iic y) (Ioi y) := disjoint_left.mpr
        (fun x (hx : x ≤ y) (hy : y < x) => not_lt_of_ge hx hy)
      rw [← setIntegral_union hd
        measurableSet_Ioi hg.integrableOn hg.integrableOn, Iic_union_Ioi,
        Measure.restrict_univ]
    rw [hsplit (fun x => p.density x * v' x) hvi, hsplit (fun x => p' x * v x) hdi]
    dsimp only [Pi.mul_apply] at hlo hhi
    linarith
  simpa only [laplaceSmoothDerivative, v, v', mul_neg, integral_neg, neg_inj] using he

theorem integral_abs_laplaceSmoothDerivative_le
    (p : HellingerDensity (volume : Measure ℝ)) {p' : ℝ → ℝ}
    (hp : ∀ x, HasDerivAt p.density (p' x) x) (hp' : Integrable p' volume)
    {δ : ℝ} (hδ : 0 < δ) :
    (∫ y, |laplaceSmoothDerivative p δ y|) ≤ ∫ x, |p' x| := by
  have hconv := hp'.abs.integrable_convolution (L := ContinuousLinearMap.mul ℝ ℝ)
    (laplaceDensity δ hδ).integrable
  calc
    (∫ y, |laplaceSmoothDerivative p δ y|) ≤
        ∫ y, ∫ x, |p' x| * laplacePdf δ (y - x) := by
      apply integral_mono (laplaceSmoothDerivative_integrable p hδ).abs hconv
      intro y
      change |laplaceSmoothDerivative p δ y| ≤
        ∫ x, |p' x| * laplacePdf δ (y - x)
      rw [laplaceSmoothDerivative_eq_input_convolution p hp hp' hδ y]
      calc
        |∫ x, p' x * laplacePdf δ (y - x)| ≤
            ∫ x, ‖p' x * laplacePdf δ (y - x)‖ := by
          simpa only [Real.norm_eq_abs] using
            norm_integral_le_integral_norm (fun x => p' x * laplacePdf δ (y - x))
        _ = _ := by
          apply integral_congr_ae
          exact ae_of_all _ fun x => by
            change ‖p' x * laplacePdf δ (y - x)‖ = |p' x| * laplacePdf δ (y - x)
            rw [Real.norm_eq_abs, abs_mul, abs_of_pos (laplacePdf_pos hδ _)]
    _ = (∫ x, |p' x|) * (∫ x, laplacePdf δ x) :=
      integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hp'.abs
        (laplaceDensity δ hδ).integrable
    _ = _ := by
      change (∫ x, |p' x|) * (∫ x, (laplaceDensity δ hδ).density x) = _
      rw [(laplaceDensity δ hδ).integral_eq_one, mul_one]

theorem integral_laplaceSmooth_fisher_le_input_variation
    (p : HellingerDensity (volume : Measure ℝ)) {p' : ℝ → ℝ}
    (hp : ∀ x, HasDerivAt p.density (p' x) x) (hp' : Integrable p' volume)
    {δ : ℝ} (hδ : 0 < δ) :
    (∫ y, laplaceSmoothDerivative p δ y ^ 2 / (laplaceSmooth p δ hδ).density y) ≤
      (∫ x, |p' x|) / δ :=
  (integral_laplaceSmooth_fisher_le p hδ).trans
    (div_le_div_of_nonneg_right (integral_abs_laplaceSmoothDerivative_le p hp hp' hδ) hδ.le)

end

end ProbabilityTheory
