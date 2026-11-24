import PLAStochastic.ForMathlib.Probability.Distributions.LaplaceVariation
import PLAStochastic.ForMathlib.Analysis.Calculus.Translation
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Square-root translation of the actual positive Laplace smoothing

The derivative of the square root is square integrable by the proved Fisher
bound. The Lebesgue `L²` translation estimate then gives a Hellinger estimate.
No uniform positive lower bound on the density is required.
-/

set_option autoImplicit false

namespace ProbabilityTheory

noncomputable section

open MeasureTheory

def laplaceSmoothRootDerivative (p : HellingerDensity (volume : Measure ℝ))
    (δ : ℝ) (hδ : 0 < δ) (y : ℝ) : ℝ :=
  laplaceSmoothDerivative p δ y / (2 * Real.sqrt ((laplaceSmooth p δ hδ).density y))

theorem laplaceSmoothRootDerivative_measurable
    (p : HellingerDensity (volume : Measure ℝ)) {δ : ℝ} (hδ : 0 < δ) :
    Measurable (laplaceSmoothRootDerivative p δ hδ) :=
  (laplaceSmoothDerivative_measurable p δ).div
    (measurable_const.mul (laplaceSmooth p δ hδ).measurable.sqrt)

theorem laplaceSmoothRootDerivative_sq
    (p : HellingerDensity (volume : Measure ℝ)) {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    laplaceSmoothRootDerivative p δ hδ y ^ 2 =
      (laplaceSmoothDerivative p δ y ^ 2 / (laplaceSmooth p δ hδ).density y) / 4 := by
  unfold laplaceSmoothRootDerivative
  rw [div_pow, mul_pow, Real.sq_sqrt (laplaceSmooth_pos p hδ y).le]
  ring

theorem laplaceSmoothRootDerivative_sq_integrable
    (p : HellingerDensity (volume : Measure ℝ)) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun y => laplaceSmoothRootDerivative p δ hδ y ^ 2) volume := by
  simp_rw [laplaceSmoothRootDerivative_sq p hδ]
  exact (laplaceSmooth_fisher_integrable p hδ).div_const 4

set_option backward.isDefEq.respectTransparency.types false in
theorem laplaceSmoothRoot_hasDerivAt
    (p : HellingerDensity (volume : Measure ℝ)) {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    HasDerivAt (fun y => Real.sqrt ((laplaceSmooth p δ hδ).density y))
      (laplaceSmoothRootDerivative p δ hδ y) y :=
  (laplaceSmooth_hasDerivAt p hδ y).sqrt (laplaceSmooth_pos p hδ y).ne'

theorem hellinger_translate_laplaceSmooth_sq_le
    (p : HellingerDensity (volume : Measure ℝ)) {δ : ℝ} (hδ : 0 < δ) (s : ℝ) :
    ((laplaceSmooth p δ hδ).translate s).hellinger (laplaceSmooth p δ hδ) ^ 2 ≤
      (s ^ 2 / 4) *
        ∫ y, laplaceSmoothDerivative p δ y ^ 2 / (laplaceSmooth p δ hδ).density y := by
  rw [HellingerDensity.hellinger_sq]
  have h := integral_sq_translation_sub_le (laplaceSmoothRoot_hasDerivAt p hδ)
    (laplaceSmoothRootDerivative_measurable p hδ)
    (laplaceSmoothRootDerivative_sq_integrable p hδ)
    (laplaceSmooth p δ hδ).sqrt_memLp (-s)
  simp_rw [laplaceSmoothRootDerivative_sq p hδ] at h
  simpa only [HellingerDensity.translate, sub_eq_add_neg, neg_sq, integral_div,
    mul_div_assoc, div_mul_eq_mul_div] using h

theorem hellinger_translate_laplaceSmooth_le_input_variation
    (p : HellingerDensity (volume : Measure ℝ)) {p' : ℝ → ℝ}
    (hp : ∀ x, HasDerivAt p.density (p' x) x) (hp' : Integrable p' volume)
    {δ : ℝ} (hδ : 0 < δ) (s : ℝ) :
    ((laplaceSmooth p δ hδ).translate s).hellinger (laplaceSmooth p δ hδ) ≤
      (|s| / 2) * Real.sqrt ((∫ x, |p' x|) / δ) := by
  have hb := (hellinger_translate_laplaceSmooth_sq_le p hδ s).trans
    (mul_le_mul_of_nonneg_left
      (integral_laplaceSmooth_fisher_le_input_variation p hp hp' hδ) (by positivity))
  have hn : 0 ≤ (∫ x, |p' x|) / δ := div_nonneg (integral_nonneg fun _ => abs_nonneg _) hδ.le
  have he : ((|s| / 2) * Real.sqrt ((∫ x, |p' x|) / δ)) ^ 2 =
      (s ^ 2 / 4) * ((∫ x, |p' x|) / δ) := by
    rw [mul_pow, div_pow, Real.sq_sqrt hn, sq_abs]
    ring
  have hpos : 0 ≤ (|s| / 2) * Real.sqrt ((∫ x, |p' x|) / δ) := by positivity
  nlinarith [((laplaceSmooth p δ hδ).translate s).hellinger_nonneg (laplaceSmooth p δ hδ)]

end

end ProbabilityTheory
