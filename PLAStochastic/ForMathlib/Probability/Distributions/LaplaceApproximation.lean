import PLAStochastic.ForMathlib.Probability.Distributions.LaplaceMoments
import PLAStochastic.ForMathlib.Analysis.Calculus.Translation

/-!
# Second-order approximation by the actual positive Laplace kernel

The zero first moment removes the linear Taylor term. The integrable second
derivative bounds the integrated remainder, so the `L¹` approximation error is
at most twice its `L¹` norm times the square of the smoothing scale.
-/

set_option autoImplicit false

namespace ProbabilityTheory

noncomputable section

open MeasureTheory

theorem laplaceSmooth_density_swap (p : HellingerDensity (volume : Measure ℝ))
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    (laplaceSmooth p δ hδ).density y = ∫ u, p.density (y - u) * laplacePdf δ u := by
  change (convolution p.density (laplacePdf δ) (ContinuousLinearMap.mul ℝ ℝ) volume) y = _
  exact convolution_mul_swap

theorem laplaceSmooth_section_swap_integrable (p : HellingerDensity (volume : Measure ℝ))
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    Integrable (fun u => p.density (y - u) * laplacePdf δ u) volume := by
  have h := (laplaceSmooth_section_integrable p hδ y).comp_sub_left y
  convert h using 1
  funext u
  rw [sub_sub_cancel]

theorem laplaceSmooth_error_eq_remainder
    (p : HellingerDensity (volume : Measure ℝ)) (p' : ℝ → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    (laplaceSmooth p δ hδ).density y - p.density y =
      ∫ u, (p.density (y - u) - p.density y + u * p' y) * laplacePdf δ u := by
  have hi := laplaceSmooth_section_swap_integrable p hδ y
  have hk : Integrable (fun u => p.density y * laplacePdf δ u) volume :=
    (laplaceDensity δ hδ).integrable.const_mul (p.density y)
  have hm := (id_mul_laplacePdf_integrable hδ).mul_const (p' y)
  have he : (fun u => (p.density (y - u) - p.density y + u * p' y) * laplacePdf δ u) =
      fun u => (p.density (y - u) * laplacePdf δ u - p.density y * laplacePdf δ u) +
        (u * laplacePdf δ u) * p' y := by
    funext u
    ring
  rw [he]
  have his : Integrable (fun u => p.density (y - u) * laplacePdf δ u -
      p.density y * laplacePdf δ u) volume := hi.sub hk
  rw [integral_add his hm, integral_sub hi hk, integral_const_mul,
    integral_mul_const, integral_id_mul_laplacePdf, zero_mul, add_zero,
    ← laplaceSmooth_density_swap p hδ y]
  change (laplaceSmooth p δ hδ).density y - p.density y =
    (laplaceSmooth p δ hδ).density y - p.density y *
      (∫ u, (laplaceDensity δ hδ).density u)
  rw [(laplaceDensity δ hδ).integral_eq_one, mul_one]

theorem laplaceSmooth_remainder_integrable
    (p : HellingerDensity (volume : Measure ℝ)) {p' : ℝ → ℝ}
    (hp' : Integrable p' volume) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun z : ℝ × ℝ =>
      (p.density (z.1 - z.2) - p.density z.1 + z.2 * p' z.1) * laplacePdf δ z.2)
      (volume.prod volume) := by
  have ha := (laplaceDensity δ hδ).integrable.convolution_integrand
    (ContinuousLinearMap.mul ℝ ℝ) p.integrable
  have hb := p.integrable.mul_prod (laplaceDensity δ hδ).integrable
  have hc := hp'.mul_prod (id_mul_laplacePdf_integrable hδ)
  refine ((ha.sub hb).add hc).congr (ae_of_all _ fun z => ?_)
  dsimp only [ContinuousLinearMap.mul_apply', Pi.add_apply, Pi.sub_apply, laplaceDensity]
  ring

theorem integral_abs_laplaceSmooth_error_le
    (p : HellingerDensity (volume : Measure ℝ)) {p' p'' : ℝ → ℝ}
    (hp : ∀ x, HasDerivAt p.density (p' x) x)
    (hp' : ∀ x, HasDerivAt p' (p'' x) x)
    (hm' : Measurable p') (hm'' : Measurable p'')
    (hi' : Integrable p' volume) (hi'' : Integrable p'' volume)
    {δ : ℝ} (hδ : 0 < δ) :
    (∫ y, |(laplaceSmooth p δ hδ).density y - p.density y|) ≤
      2 * (∫ y, |p'' y|) * δ ^ 2 := by
  have hj := laplaceSmooth_remainder_integrable p hi' hδ
  calc
    (∫ y, |(laplaceSmooth p δ hδ).density y - p.density y|) ≤
        ∫ y, ∫ u, |(p.density (y - u) - p.density y + u * p' y) * laplacePdf δ u| := by
      apply integral_mono ((laplaceSmooth p δ hδ).integrable.sub p.integrable).abs
        hj.abs.integral_prod_left
      intro y
      change |(laplaceSmooth p δ hδ).density y - p.density y| ≤ _
      rw [laplaceSmooth_error_eq_remainder p p' hδ y]
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun u => (p.density (y - u) - p.density y + u * p' y) * laplacePdf δ u)
    _ = ∫ u, (∫ y, |p.density (y - u) - p.density y + u * p' y|) * laplacePdf δ u := by
      rw [integral_integral_swap hj.abs]
      apply integral_congr_ae
      exact ae_of_all _ fun u => by
        simp_rw [abs_mul, abs_of_pos (laplacePdf_pos hδ u)]
        rw [integral_mul_const]
    _ ≤ ∫ u, (u ^ 2 * (∫ y, |p'' y|)) * laplacePdf δ u := by
      have hi1 : Integrable (fun u =>
          (∫ y, |p.density (y - u) - p.density y + u * p' y|) * laplacePdf δ u) volume := by
        convert hj.abs.integral_prod_right using 1
        funext u
        simp_rw [abs_mul, abs_of_pos (laplacePdf_pos hδ u)]
        rw [integral_mul_const]
      have hi2 : Integrable (fun u => (u ^ 2 * (∫ y, |p'' y|)) * laplacePdf δ u) volume := by
        convert (sq_laplacePdf_integrable hδ).mul_const (∫ y, |p'' y|) using 1
        funext u
        ring
      apply integral_mono hi1 hi2
      intro u
      change (∫ y, |p.density (y - u) - p.density y + u * p' y|) * laplacePdf δ u ≤ _
      apply mul_le_mul_of_nonneg_right ?_ (laplacePdf_pos hδ u).le
      have h := integral_abs_translation_remainder_le hp hp' hm' hm''
        p.integrable hi' hi'' (-u)
      simpa only [sub_eq_add_neg, neg_mul, neg_neg, neg_sq] using h
    _ = 2 * (∫ y, |p'' y|) * δ ^ 2 := by
      have he : (fun u => (u ^ 2 * (∫ y, |p'' y|)) * laplacePdf δ u) =
          fun u => (u ^ 2 * laplacePdf δ u) * (∫ y, |p'' y|) := by funext u; ring
      rw [he, integral_mul_const, integral_sq_laplacePdf hδ]
      ring

end

end ProbabilityTheory
