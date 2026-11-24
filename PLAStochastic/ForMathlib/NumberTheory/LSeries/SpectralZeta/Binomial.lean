import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! # Binomial series with Pochhammer coefficients

For `‖y‖ < 1` and every complex `s`,

`(1 - y)^{-s} = ∑_k (s)_k / k! * y^k`,

where `(s)_k` is the rising factorial `ascPochhammer`. This is Mathlib's binomial series
`one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero`, with coefficients rewritten from
`Ring.choose (s + k - 1) k`. The coefficients obey `‖(s)_k / k!‖ ≤ 2^{‖s‖} 2^k`, which follows
from the real series at `y = 1/2`.
-/

noncomputable section

open Complex Polynomial

namespace BrownianAffine.SpectralZeta

/-- The binomial coefficient `(s)_k / k!` of `(1 - y)^{-s}`. -/
def pochCoeff (s : ℂ) (k : ℕ) : ℂ := (ascPochhammer ℂ k).eval s / k.factorial

/-- The real binomial coefficient `(t)_k / k!`. -/
def pochCoeffReal (t : ℝ) (k : ℕ) : ℝ := (ascPochhammer ℝ k).eval t / k.factorial

theorem ring_choose_eq_pochCoeff (s : ℂ) (k : ℕ) :
    Ring.choose (s + k - 1) k = pochCoeff s k := by
  rw [← Ring.multichoose_eq, pochCoeff, eq_div_iff (by exact_mod_cast k.factorial_ne_zero)]
  have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer s k
  rw [Polynomial.ascPochhammer_smeval_eq_eval, nsmul_eq_mul] at h
  rw [mul_comm]
  exact h

theorem ring_choose_eq_pochCoeffReal (t : ℝ) (k : ℕ) :
    Ring.choose (t + k - 1) k = pochCoeffReal t k := by
  rw [← Ring.multichoose_eq, pochCoeffReal, eq_div_iff (by exact_mod_cast k.factorial_ne_zero)]
  have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer t k
  rw [Polynomial.ascPochhammer_smeval_eq_eval, nsmul_eq_mul] at h
  rw [mul_comm]
  exact h

/-- The binomial series `(1 - y)^{-s} = ∑ (s)_k / k! y^k` for `‖y‖ < 1`. -/
theorem hasSum_pochCoeff_mul_pow (s : ℂ) {y : ℂ} (hy : ‖y‖ < 1) :
    HasSum (fun k => pochCoeff s k * y ^ k) ((1 - y) ^ (-s)) := by
  have hmem : y ∈ Metric.eball (0 : ℂ) 1 := by
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
    simpa using hy
  have h := (one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero s).hasSum hmem
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add,
    ring_choose_eq_pochCoeff] at h
  rw [cpow_neg, inv_eq_one_div]
  exact h

theorem hasSum_pochCoeffReal_mul_pow (t : ℝ) {y : ℝ} (hy : |y| < 1) :
    HasSum (fun k => pochCoeffReal t k * y ^ k) (1 / (1 - y) ^ t) := by
  have hmem : y ∈ Metric.eball (0 : ℝ) 1 := by
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
    simpa using hy
  have h := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero t).hasSum hmem
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add,
    ring_choose_eq_pochCoeffReal] at h
  exact h

theorem ascPochhammer_eval_real_nonneg {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    0 ≤ (ascPochhammer ℝ k).eval t := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ascPochhammer_succ_right, eval_mul, eval_add, eval_X, eval_natCast]
    exact mul_nonneg ih (by positivity)

theorem norm_ascPochhammer_eval_le (s : ℂ) (k : ℕ) :
    ‖(ascPochhammer ℂ k).eval s‖ ≤ (ascPochhammer ℝ k).eval ‖s‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ascPochhammer_succ_right, eval_mul, eval_add, eval_X, eval_natCast,
      ascPochhammer_succ_right, eval_mul, eval_add, eval_X, eval_natCast, norm_mul]
    refine mul_le_mul ih ?_ (norm_nonneg _) (ascPochhammer_eval_real_nonneg (norm_nonneg s) k)
    calc ‖s + (k : ℂ)‖ ≤ ‖s‖ + ‖(k : ℂ)‖ := norm_add_le _ _
      _ = ‖s‖ + k := by rw [Complex.norm_natCast]

theorem pochCoeffReal_nonneg {t : ℝ} (ht : 0 ≤ t) (k : ℕ) : 0 ≤ pochCoeffReal t k :=
  div_nonneg (ascPochhammer_eval_real_nonneg ht k) (by positivity)

theorem pochCoeffReal_le {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    pochCoeffReal t k ≤ 2 ^ t * 2 ^ k := by
  have h := hasSum_pochCoeffReal_mul_pow t (y := 1 / 2) (by norm_num [abs_of_pos])
  have hle := le_hasSum h k (fun j _ => mul_nonneg (pochCoeffReal_nonneg ht j) (by positivity))
  have h2 : (1 : ℝ) / (1 - 1 / 2) ^ t = 2 ^ t := by
    rw [show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num, Real.inv_rpow (by norm_num), one_div, inv_inv]
  rw [h2] at hle
  have h3 : pochCoeffReal t k = pochCoeffReal t k * (1 / 2) ^ k * 2 ^ k := by
    rw [mul_assoc, ← mul_pow]
    norm_num
  rw [h3]
  exact mul_le_mul_of_nonneg_right hle (by positivity)

/-- The locally uniform bound `‖(s)_k / k!‖ ≤ 2^{‖s‖} 2^k`. -/
theorem norm_pochCoeff_le (s : ℂ) (k : ℕ) : ‖pochCoeff s k‖ ≤ 2 ^ ‖s‖ * 2 ^ k := by
  calc ‖pochCoeff s k‖ ≤ pochCoeffReal ‖s‖ k := by
        rw [pochCoeff, pochCoeffReal, norm_div, Complex.norm_natCast]
        exact div_le_div_of_nonneg_right (norm_ascPochhammer_eval_le s k) (by positivity)
    _ ≤ 2 ^ ‖s‖ * 2 ^ k := pochCoeffReal_le (norm_nonneg s) k

theorem norm_pochCoeff_le_of_norm_le {s : ℂ} {R : ℝ} (hs : ‖s‖ ≤ R) (k : ℕ) :
    ‖pochCoeff s k‖ ≤ 2 ^ R * 2 ^ k :=
  (norm_pochCoeff_le s k).trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) hs) (by positivity))

theorem differentiable_pochCoeff (k : ℕ) : Differentiable ℂ (fun s => pochCoeff s k) :=
  (Polynomial.differentiable _).div_const _

end BrownianAffine.SpectralZeta
