import PLAStochastic.ForMathlib.Analysis.Calculus.Translation

/-!
# An actual first-derivative bound from an integrable second derivative

The secant estimate and its integrated remainder yield a square-root dependence
on the second derivative norm. This is the sublinear term needed in reference
regularity induction.
-/

set_option autoImplicit false

namespace ProbabilityTheory.HellingerDensity

noncomputable section

open MeasureTheory

theorem integral_abs_density_translation_le_two
    (p : HellingerDensity (volume : Measure ℝ)) (s : ℝ) :
    (∫ x, |p.density (x + s) - p.density x|) ≤ 2 := by
  calc
    (∫ x, |p.density (x + s) - p.density x|) ≤
        ∫ x, p.density (x + s) + p.density x := by
      apply integral_mono ((p.integrable.comp_add_right s).sub p.integrable).abs
        ((p.integrable.comp_add_right s).add p.integrable)
      intro x
      change |p.density (x + s) - p.density x| ≤ p.density (x + s) + p.density x
      simpa only [Real.norm_eq_abs, abs_of_nonneg (p.nonneg _)] using
        norm_sub_le (p.density (x + s)) (p.density x)
    _ = 2 := by
      rw [integral_add (p.integrable.comp_add_right s) p.integrable,
        integral_add_right_eq_self, p.integral_eq_one]
      norm_num

theorem mul_integral_abs_derivative_le_secant
    (p : HellingerDensity (volume : Measure ℝ)) {p' p'' : ℝ → ℝ}
    (hp : ∀ x, HasDerivAt p.density (p' x) x)
    (hp' : ∀ x, HasDerivAt p' (p'' x) x)
    (hm' : Measurable p') (hm'' : Measurable p'')
    (hi' : Integrable p' volume) (hi'' : Integrable p'' volume)
    {h : ℝ} (hh : 0 ≤ h) :
    h * (∫ x, |p' x|) ≤ 2 + h ^ 2 * ∫ x, |p'' x| := by
  have hpoint : ∀ x, h * |p' x| ≤ |p.density (x + h) - p.density x| +
      |p.density (x + h) - p.density x - h * p' x| := by
    intro x
    calc
      h * |p' x| = |h * p' x| := by rw [abs_mul, abs_of_nonneg hh]
      _ = |(p.density (x + h) - p.density x) -
          (p.density (x + h) - p.density x - h * p' x)| := by congr 1; ring
      _ ≤ _ := by
        simpa only [Real.norm_eq_abs] using norm_sub_le (p.density (x + h) - p.density x)
          (p.density (x + h) - p.density x - h * p' x)
  have hd := (p.integrable.comp_add_right h).sub p.integrable
  calc
    h * (∫ x, |p' x|) = ∫ x, h * |p' x| := (integral_const_mul _ _).symm
    _ ≤ ∫ x, |p.density (x + h) - p.density x| +
        |p.density (x + h) - p.density x - h * p' x| :=
      integral_mono (hi'.abs.const_mul h) (hd.abs.add (hd.sub (hi'.const_mul h)).abs) hpoint
    _ = (∫ x, |p.density (x + h) - p.density x|) +
        ∫ x, |p.density (x + h) - p.density x - h * p' x| :=
      integral_add hd.abs (hd.sub (hi'.const_mul h)).abs
    _ ≤ 2 + h ^ 2 * ∫ x, |p'' x| := add_le_add
      (integral_abs_density_translation_le_two p h)
      (integral_abs_translation_remainder_le hp hp' hm' hm'' p.integrable hi' hi'' h)

theorem integral_abs_derivative_le_three_sqrt
    (p : HellingerDensity (volume : Measure ℝ)) {p' p'' : ℝ → ℝ}
    (hp : ∀ x, HasDerivAt p.density (p' x) x)
    (hp' : ∀ x, HasDerivAt p' (p'' x) x)
    (hm' : Measurable p') (hm'' : Measurable p'')
    (hi' : Integrable p' volume) (hi'' : Integrable p'' volume)
    {J : ℝ} (hJ : 1 ≤ J) (hA : (∫ x, |p'' x|) ≤ J) :
    (∫ x, |p' x|) ≤ 3 * Real.sqrt J := by
  have hJpos : 0 < J := lt_of_lt_of_le (by norm_num) hJ
  have hs : 0 < Real.sqrt J := Real.sqrt_pos.2 hJpos
  have he : Real.sqrt J ^ 2 = J := Real.sq_sqrt hJpos.le
  have hb := mul_integral_abs_derivative_le_secant p hp hp' hm' hm'' hi' hi''
    (show 0 ≤ 1 / Real.sqrt J by positivity)
  have hr : (1 / Real.sqrt J) ^ 2 * (∫ x, |p'' x|) ≤ 1 := by
    calc
      _ ≤ (1 / Real.sqrt J) ^ 2 * J :=
        mul_le_mul_of_nonneg_left hA (sq_nonneg _)
      _ = 1 := by rw [div_pow, one_pow, he, one_div, inv_mul_cancel₀ hJpos.ne']
  have hV : (∫ x, |p' x|) / Real.sqrt J ≤ 3 := by
    rw [← one_div_mul_eq_div]
    linarith
  exact (div_le_iff₀ hs).1 hV

end

end ProbabilityTheory.HellingerDensity
