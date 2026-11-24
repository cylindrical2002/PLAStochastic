import Mathlib.Probability.Distributions.Binomial
import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Differentiation of finite binomial expectations

This uses the Bernstein-polynomial identities and the actual finite-sum formula
for the binomial measure. The mean is proved here from the polynomial identity.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace ProbabilityTheory

noncomputable section

open MeasureTheory Finset Polynomial

def binomialPolynomial (n : ℕ) (a : ℕ → ℝ) : ℝ[X] :=
  ∑ k ∈ range (n + 1), C (a k) * bernsteinPolynomial ℝ n k

def binomialAverage (n : ℕ) (a : ℕ → ℝ) (p : ℝ) : ℝ :=
  ∑ k ∈ range (n + 1), a k * ((n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k))

theorem binomialPolynomial_eval (n : ℕ) (a : ℕ → ℝ) (p : ℝ) :
    (binomialPolynomial n a).eval p = binomialAverage n a p := by
  simp only [binomialPolynomial, binomialAverage, eval_finsetSum, eval_mul, eval_C,
    bernsteinPolynomial, eval_natCast, eval_pow, eval_X, eval_sub, eval_one]

theorem integral_binomial_eq_average (n : ℕ) (a : ℕ → ℝ) (p : unitInterval) :
    (∫ k, a k ∂binomial n p) = binomialAverage n a p := by
  rw [integral_binomial, binomialAverage]
  have hrange : Finset.Iic n = range (n + 1) := by ext k; simp
  simp only [smul_eq_mul, hrange, mul_comm]

theorem derivative_binomialPolynomial_succ (n : ℕ) (a : ℕ → ℝ) :
    (binomialPolynomial (n + 1) a).derivative = C (n + 1 : ℝ) *
      (binomialPolynomial n (fun k => a (k + 1)) - binomialPolynomial n a) := by
  have hshift : (∑ k ∈ range (n + 1), C (a (k + 1)) * bernsteinPolynomial ℝ n (k + 1)) +
      C (a 0) * bernsteinPolynomial ℝ n 0 = binomialPolynomial n a := by
    have he := sum_range_succ' (fun k => C (a k) * bernsteinPolynomial ℝ n k) (n + 1)
    rw [sum_range_succ] at he
    simpa only [bernsteinPolynomial.eq_zero_of_lt ℝ (Nat.lt_succ_self n),
      mul_zero, add_zero, binomialPolynomial] using he.symm
  have hmain : (binomialPolynomial (n + 1) a).derivative = C (n + 1 : ℝ) *
      ((∑ k ∈ range (n + 1), C (a (k + 1)) *
        (bernsteinPolynomial ℝ n k - bernsteinPolynomial ℝ n (k + 1))) -
        C (a 0) * bernsteinPolynomial ℝ n 0) := by
    rw [binomialPolynomial, sum_range_succ', derivative_add, derivative_sum]
    simp only [derivative_mul, derivative_C, zero_mul, zero_add,
      bernsteinPolynomial.derivative_succ_aux, bernsteinPolynomial.derivative_zero,
      Nat.add_one_sub_one]
    simp only [map_add, map_natCast, map_one]
    rw [mul_sub, mul_sum]
    congr 1
    · apply sum_congr rfl
      intro k _
      ring
    · push_cast
      ring
  rw [hmain]
  simp_rw [mul_sub]
  rw [sum_sub_distrib]
  have hshift' := hshift
  dsimp [binomialPolynomial]
  dsimp [binomialPolynomial] at hshift'
  linear_combination -C (n + 1 : ℝ) * hshift'

theorem hasDerivAt_binomialAverage_succ (n : ℕ) (a : ℕ → ℝ) (p : ℝ) :
    HasDerivAt (binomialAverage (n + 1) a)
      ((n + 1 : ℝ) * binomialAverage n (fun k => a (k + 1) - a k) p) p := by
  have hd := (binomialPolynomial (n + 1) a).hasDerivAt p
  rw [derivative_binomialPolynomial_succ, eval_mul, eval_C, eval_sub,
    binomialPolynomial_eval, binomialPolynomial_eval] at hd
  have he : binomialAverage n (fun k => a (k + 1) - a k) p =
      binomialAverage n (fun k => a (k + 1)) p - binomialAverage n a p := by
    simp only [binomialAverage, sub_mul, sum_sub_distrib]
  rw [he]
  simpa only [binomialPolynomial_eval] using hd

theorem binomialAverage_mean (n : ℕ) (p : ℝ) :
    binomialAverage n (fun k => (k : ℝ)) p = n * p := by
  have he := congrArg (fun b : ℝ[X] => b.eval p) (bernsteinPolynomial.sum_smul ℝ n)
  simpa only [eval_finsetSum, eval_smul, nsmul_eq_mul, eval_X,
    bernsteinPolynomial, eval_mul, eval_natCast, eval_pow, eval_sub, eval_one,
    binomialAverage] using he

theorem integral_binomial_natCast (n : ℕ) (p : unitInterval) :
    (∫ k, (k : ℝ) ∂binomial n p) = n * (p : ℝ) := by
  rw [integral_binomial_eq_average, binomialAverage_mean]

theorem binomialAverage_zero (n : ℕ) (a : ℕ → ℝ) : binomialAverage n a 0 = a 0 := by
  rw [← binomialPolynomial_eval]
  simp [binomialPolynomial, eval_finsetSum, bernsteinPolynomial.eval_at_0]

theorem binomialAverage_one (n : ℕ) (p : ℝ) :
    binomialAverage n (fun _ => 1) p = 1 := by
  rw [← binomialPolynomial_eval]
  simp only [binomialPolynomial, C_1, one_mul, bernsteinPolynomial.sum, eval_one]

end

end ProbabilityTheory
