import Mathlib.Analysis.Complex.SqrtDeriv

/-! # The principal square root under positive real rescaling -/

noncomputable section
open Complex
namespace PGM

theorem norm_complex_sqrt_sq (z : ℂ) : ‖Complex.sqrt z‖ ^ 2 = ‖z‖ := by
  rw [← norm_pow, Complex.sqrt]
  congr 1
  exact cpow_ofNat_inv_pow z 2

theorem complex_sqrt_sq_real_mul {b : ℝ} (hb : 0 < b) (z : ℂ) :
    Complex.sqrt ((b : ℂ) ^ 2 * z) = (b : ℂ) * Complex.sqrt z := by
  by_cases hz : z = 0
  · simp only [hz, mul_zero, sqrt_zero]
  · have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
    have hb2c : ((b ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hb2.ne'
    have he : exp ((Real.log (b ^ 2) : ℂ) / 2) = (b : ℂ) := by
      rw [Complex.ofReal_log hb2.le, ← sqrt_eq_exp hb2c,
        Complex.sqrt_of_nonneg (by exact_mod_cast hb2.le), ofReal_re, Real.sqrt_sq hb.le]
    rw [← ofReal_pow, sqrt_eq_exp (mul_ne_zero hb2c hz),
      Complex.log_ofReal_mul hb2 hz, add_div, exp_add, he, ← sqrt_eq_exp hz]

end PGM
