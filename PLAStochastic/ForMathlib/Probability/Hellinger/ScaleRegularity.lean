import PLAStochastic.ForMathlib.Probability.Distributions.LaplaceApproximation
import PLAStochastic.ForMathlib.Probability.Distributions.LaplaceTranslation

/-!
# A two-thirds Hellinger translation bound from two actual integrable derivatives

All smoothing estimates are proved for the actual Laplace convolution. The
constant depends only on the two derivative norms. The original density may
vanish and need not have finite Fisher information.
-/

set_option autoImplicit false

namespace ProbabilityTheory.HellingerDensity

noncomputable section

open MeasureTheory

theorem hellinger_laplaceSmooth_le_second_derivative
    (p : HellingerDensity (volume : Measure ℝ)) {p' p'' : ℝ → ℝ}
    (hp : ∀ x, HasDerivAt p.density (p' x) x)
    (hp' : ∀ x, HasDerivAt p' (p'' x) x)
    (hm' : Measurable p') (hm'' : Measurable p'')
    (hi' : Integrable p' volume) (hi'' : Integrable p'' volume)
    {δ : ℝ} (hδ : 0 < δ) :
    (laplaceSmooth p δ hδ).hellinger p ≤ Real.sqrt (2 * ∫ y, |p'' y|) * δ := by
  have h := ((laplaceSmooth p δ hδ).hellinger_sq_le_integral_abs p).trans
    (integral_abs_laplaceSmooth_error_le p hp hp' hm' hm'' hi' hi'' hδ)
  have hA : 0 ≤ 2 * ∫ y, |p'' y| := mul_nonneg (by norm_num)
    (integral_nonneg fun _ => abs_nonneg _)
  have he : (Real.sqrt (2 * ∫ y, |p'' y|) * δ) ^ 2 =
      2 * (∫ y, |p'' y|) * δ ^ 2 := by rw [mul_pow, Real.sq_sqrt hA]
  nlinarith [(laplaceSmooth p δ hδ).hellinger_nonneg p,
    mul_nonneg (Real.sqrt_nonneg (2 * ∫ y, |p'' y|)) hδ.le]

theorem hellinger_translate_le_laplace_budget
    (p : HellingerDensity (volume : Measure ℝ)) {p' p'' : ℝ → ℝ}
    (hp : ∀ x, HasDerivAt p.density (p' x) x)
    (hp' : ∀ x, HasDerivAt p' (p'' x) x)
    (hm' : Measurable p') (hm'' : Measurable p'')
    (hi' : Integrable p' volume) (hi'' : Integrable p'' volume)
    {δ : ℝ} (hδ : 0 < δ) (s : ℝ) :
    (p.translate s).hellinger p ≤
      2 * Real.sqrt (2 * ∫ y, |p'' y|) * δ +
        (|s| / 2) * Real.sqrt ((∫ y, |p' y|) / δ) := by
  have ha := hellinger_laplaceSmooth_le_second_derivative p hp hp' hm' hm'' hi' hi'' hδ
  have hb := hellinger_translate_laplaceSmooth_le_input_variation p hp hi' hδ s
  have h1 := (p.translate s).hellinger_triangle ((laplaceSmooth p δ hδ).translate s) p
  have h2 := ((laplaceSmooth p δ hδ).translate s).hellinger_triangle
    (laplaceSmooth p δ hδ) p
  rw [hellinger_translate, p.hellinger_comm] at h1
  linarith

/-- Two integrable derivatives give a `2/3` translation exponent. -/
theorem hellinger_translate_le_two_thirds
    (p : HellingerDensity (volume : Measure ℝ)) {p' p'' : ℝ → ℝ}
    (hp : ∀ x, HasDerivAt p.density (p' x) x)
    (hp' : ∀ x, HasDerivAt p' (p'' x) x)
    (hm' : Measurable p') (hm'' : Measurable p'')
    (hi' : Integrable p' volume) (hi'' : Integrable p'' volume) (s : ℝ) :
    (p.translate s).hellinger p ≤
      (2 * Real.sqrt (2 * ∫ y, |p'' y|) + Real.sqrt (∫ y, |p' y|) / 2) *
        |s| ^ (2 / 3 : ℝ) := by
  by_cases hs : s = 0
  · subst s
    have he : p.translate 0 = p := by
      cases p
      simp only [translate, sub_zero]
    rw [he, hellinger_self, abs_zero, Real.zero_rpow (by norm_num : (2 / 3 : ℝ) ≠ 0), mul_zero]
  have habs : 0 < |s| := abs_pos.mpr hs
  let δ := |s| ^ (2 / 3 : ℝ)
  have hδ : 0 < δ := Real.rpow_pos_of_pos habs _
  have he : δ * Real.sqrt δ = |s| := by
    dsimp only [δ]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul habs.le, ← Real.rpow_add habs]
    norm_num
  have hv : (|s| / 2) * Real.sqrt ((∫ y, |p' y|) / δ) =
      (Real.sqrt (∫ y, |p' y|) / 2) * δ := by
    rw [Real.sqrt_div (integral_nonneg fun _ => abs_nonneg _), ← he]
    field_simp [(Real.sqrt_pos.2 hδ).ne']
  have hb := hellinger_translate_le_laplace_budget p hp hp' hm' hm'' hi' hi'' hδ s
  rw [hv] at hb
  convert hb using 1
  ring

end

end ProbabilityTheory.HellingerDensity
