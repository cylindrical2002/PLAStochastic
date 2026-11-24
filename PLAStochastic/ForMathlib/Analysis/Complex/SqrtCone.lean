import PLAStochastic.ForMathlib.Analysis.Complex.SqrtScale
import PLAStochastic.ForMathlib.Analysis.Complex.EvenSqrt
import Mathlib.Tactic

/-! # Explicit real-part sectors for principal square roots and their products -/

noncomputable section
open Complex
namespace PGM

theorem complex_sqrt_re_ge_half_norm {z : ℂ} (hz : 0 ≤ z.re) :
    ‖sqrt z‖ / 2 ≤ (sqrt z).re := by
  have hre : 0 ≤ (sqrt z).re := by
    rw [Complex.sqrt, cpow_inv_two_re]
    exact Real.sqrt_nonneg _
  have hs : (sqrt z).re ^ 2 - (sqrt z).im ^ 2 = z.re := by
    have hh := congrArg Complex.re (sqrt_sq_eq z)
    simpa [pow_two, mul_re] using hh
  have hn := Complex.sq_norm_sub_sq_re (sqrt z)
  nlinarith [norm_nonneg (sqrt z)]

theorem complex_sqrt_im_le_norm_div_sixteen {z : ℂ} (hz : 0 < z.re)
    (hi : |z.im| ≤ z.re / 8) : |(sqrt z).im| ≤ ‖sqrt z‖ / 16 := by
  have hr := complex_sqrt_re_ge_half_norm hz.le
  have hn : 0 < ‖sqrt z‖ := by
    have hz0 : z ≠ 0 := fun h => hz.ne' (congrArg Complex.re h)
    have hsq := norm_complex_sqrt_sq z
    nlinarith [norm_pos_iff.mpr hz0, norm_nonneg (sqrt z)]
  have hre : 0 < (sqrt z).re := by linarith
  have hsre : (sqrt z).re ^ 2 - (sqrt z).im ^ 2 = z.re := by
    have hh := congrArg Complex.re (sqrt_sq_eq z)
    simpa [pow_two, mul_re] using hh
  have hsim : 2 * (sqrt z).re * (sqrt z).im = z.im := by
    have hh := congrArg Complex.im (sqrt_sq_eq z)
    simp only [pow_two, mul_im] at hh
    nlinarith
  have ha : 2 * (sqrt z).re * |(sqrt z).im| = |z.im| := by
    rw [← hsim, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hre]
  have hsmall : |(sqrt z).im| ≤ (sqrt z).re / 16 := by
    nlinarith [sq_nonneg (sqrt z).im]
  exact hsmall.trans (div_le_div_of_nonneg_right (re_le_norm _) (by norm_num))

/-- One narrow square-root factor and a right-half-plane square-root factor give an
explicit sector for their product. -/
theorem complex_sqrt_product_re_lower {z w : ℂ} (hz : 0 < z.re)
    (hi : |z.im| ≤ z.re / 8) (hw : 0 ≤ w.re) :
    (3 / 16 : ℝ) * ‖sqrt z * sqrt w‖ ≤ (sqrt z * sqrt w).re := by
  have hzR := complex_sqrt_re_ge_half_norm hz.le
  have hwR := complex_sqrt_re_ge_half_norm hw
  have hzI := complex_sqrt_im_le_norm_div_sixteen hz hi
  have hwI := abs_im_le_norm (sqrt w)
  have hprod : ‖sqrt z‖ / 2 * (‖sqrt w‖ / 2) ≤ (sqrt z).re * (sqrt w).re :=
    mul_le_mul hzR hwR (by positivity) (by linarith [norm_nonneg (sqrt z)])
  have him : (sqrt z).im * (sqrt w).im ≤ ‖sqrt z‖ / 16 * ‖sqrt w‖ := by
    calc
      _ ≤ |(sqrt z).im * (sqrt w).im| := le_abs_self _
      _ = |(sqrt z).im| * |(sqrt w).im| := abs_mul _ _
      _ ≤ _ := mul_le_mul hzI hwI (abs_nonneg _) (by positivity)
  rw [mul_re, norm_mul]
  nlinarith

end PGM
