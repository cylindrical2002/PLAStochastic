import PLAStochastic.ForMathlib.NumberTheory.LSeries.SpectralZeta.Remainder
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-! # The symmetric part of the splitting: Riemann zeta values

With `P = ((m+1)(m+2))^N`, `α = (m+1)^{-z}` and `β = (m+2)^{-z}`, expanding
`(m+2)^N = ∑_i C(N,i) (m+1)^{N-i}` and `(m+1)^N = ∑_i C(N,i) (-1)^i (m+2)^{N-i}` gives, for
`re z > N + 1/2`,

`∑_m P (α² + β²)/2 = symZeta N z
  = (∑_i C(N,i) (1 + (-1)^i) ζ(2z - 2N + i) - ∑_i C(N,i) (-1)^i) / 2`,

the function `A_N(z)` of (T7). It is holomorphic wherever no `2z - 2N + i` equals `1`.
-/

noncomputable section

open Complex Finset

namespace BrownianAffine.SpectralZeta

theorem hasSum_one_div_nat_add_one_cpow {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun m : ℕ => 1 / ((m : ℂ) + 1) ^ s) (riemannZeta s) := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  refine Summable.hasSum ?_
  have h := (summable_nat_add_iff 1).2 (Complex.summable_one_div_nat_cpow.2 hs)
  refine h.congr fun m => ?_
  push_cast
  rfl

theorem hasSum_one_div_nat_add_two_cpow {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun m : ℕ => 1 / ((m : ℂ) + 2) ^ s) (riemannZeta s - 1) := by
  have h := (hasSum_nat_add_iff' 1).2 (hasSum_one_div_nat_add_one_cpow hs)
  have e1 : (fun m : ℕ => 1 / ((m : ℂ) + 2) ^ s) =
      fun m : ℕ => 1 / (((m + 1 : ℕ) : ℂ) + 1) ^ s := by
    funext m
    push_cast
    ring_nf
  have e2 : riemannZeta s - 1 =
      riemannZeta s - ∑ i ∈ range 1, 1 / ((i : ℂ) + 1) ^ s := by
    simp
  rw [e1, e2]
  exact h

/-- `(v^{-z})² v^p = 1 / v^{2z - p}` for `v ≠ 0`. -/
theorem cpow_neg_sq_mul_pow {v : ℂ} (hv : v ≠ 0) (z : ℂ) (p : ℕ) :
    (v ^ (-z)) ^ 2 * v ^ p = 1 / v ^ (2 * z - p) := by
  have e : -(2 * z - p) = (p : ℂ) + ((2 : ℕ) : ℂ) * (-z) := by
    push_cast
    ring
  rw [one_div, ← cpow_neg, e, cpow_add _ _ hv, cpow_natCast, cpow_nat_mul]
  ring

theorem sym_term_one (N m : ℕ) (z : ℂ) :
    ((((m + 1) * (m + 2) : ℕ) : ℂ)) ^ N * ((((m + 1 : ℕ) : ℂ)) ^ (-z)) ^ 2 =
      ∑ i ∈ range (N + 1), (N.choose i : ℂ) * (1 / ((m : ℂ) + 1) ^ (2 * z - 2 * N + i)) := by
  have hv : ((m : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have h1 : ((((m + 1) * (m + 2) : ℕ) : ℂ)) ^ N =
      ((m : ℂ) + 1) ^ N * (1 + ((m : ℂ) + 1)) ^ N := by
    push_cast
    rw [← mul_pow]
    ring
  rw [h1, add_pow (1 : ℂ) ((m : ℂ) + 1) N, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hiN : i ≤ N := Nat.lt_succ_iff.1 (mem_range.1 hi)
  have e : (2 * z - 2 * N + i) = 2 * z - ((N + (N - i) : ℕ) : ℂ) := by
    push_cast [Nat.cast_sub hiN]
    ring
  rw [e, ← cpow_neg_sq_mul_pow hv z (N + (N - i)), pow_add]
  push_cast
  ring

theorem sym_term_two (N m : ℕ) (z : ℂ) :
    ((((m + 1) * (m + 2) : ℕ) : ℂ)) ^ N * ((((m + 2 : ℕ) : ℂ)) ^ (-z)) ^ 2 =
      ∑ i ∈ range (N + 1),
        (N.choose i : ℂ) * (-1) ^ i * (1 / ((m : ℂ) + 2) ^ (2 * z - 2 * N + i)) := by
  have hv : ((m : ℂ) + 2) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m + 1)
  have h1 : ((((m + 1) * (m + 2) : ℕ) : ℂ)) ^ N =
      ((m : ℂ) + 2) ^ N * ((-1) + ((m : ℂ) + 2)) ^ N := by
    push_cast
    rw [← mul_pow]
    ring
  rw [h1, add_pow (-1 : ℂ) ((m : ℂ) + 2) N, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hiN : i ≤ N := Nat.lt_succ_iff.1 (mem_range.1 hi)
  have e : (2 * z - 2 * N + i) = 2 * z - ((N + (N - i) : ℕ) : ℂ) := by
    push_cast [Nat.cast_sub hiN]
    ring
  rw [e, ← cpow_neg_sq_mul_pow hv z (N + (N - i)), pow_add]
  push_cast
  ring

/-- The symmetric part `A_N(z)` of (T7), written with Riemann zeta values. -/
def symZeta (N : ℕ) (z : ℂ) : ℂ :=
  (∑ i ∈ range (N + 1), (N.choose i : ℂ) * (1 + (-1) ^ i) * riemannZeta (2 * z - 2 * N + i) -
    ∑ i ∈ range (N + 1), (N.choose i : ℂ) * (-1) ^ i) / 2

/-- Summing the symmetric part: `∑_m P (α² + β²)/2 = symZeta N z` for `re z > N + 1/2`. -/
theorem hasSum_symmetric (N : ℕ) {z : ℂ} (hz : (N : ℝ) + 1 / 2 < z.re) :
    HasSum (fun m : ℕ => ((((m + 1) * (m + 2) : ℕ) : ℂ)) ^ N *
        (((((m + 1 : ℕ) : ℂ)) ^ (-z)) ^ 2 + ((((m + 2 : ℕ) : ℂ)) ^ (-z)) ^ 2) / 2)
      (symZeta N z) := by
  have hre : ∀ i ∈ range (N + 1), 1 < (2 * z - 2 * N + i).re := by
    intro i _
    simp only [add_re, sub_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero, natCast_re]
    linarith [i.cast_nonneg (α := ℝ)]
  have ha : HasSum (fun m : ℕ => ((((m + 1) * (m + 2) : ℕ) : ℂ)) ^ N *
      ((((m + 1 : ℕ) : ℂ)) ^ (-z)) ^ 2)
      (∑ i ∈ range (N + 1), (N.choose i : ℂ) * riemannZeta (2 * z - 2 * N + i)) := by
    simp_rw [sym_term_one N _ z]
    exact hasSum_sum fun i hi => (hasSum_one_div_nat_add_one_cpow (hre i hi)).mul_left _
  have hb : HasSum (fun m : ℕ => ((((m + 1) * (m + 2) : ℕ) : ℂ)) ^ N *
      ((((m + 2 : ℕ) : ℂ)) ^ (-z)) ^ 2)
      (∑ i ∈ range (N + 1), (N.choose i : ℂ) * (-1) ^ i *
        (riemannZeta (2 * z - 2 * N + i) - 1)) := by
    simp_rw [sym_term_two N _ z]
    exact hasSum_sum fun i hi => (hasSum_one_div_nat_add_two_cpow (hre i hi)).mul_left _
  have h := (ha.add hb).div_const 2
  have e1 : (fun m : ℕ => ((((m + 1) * (m + 2) : ℕ) : ℂ)) ^ N *
      (((((m + 1 : ℕ) : ℂ)) ^ (-z)) ^ 2 + ((((m + 2 : ℕ) : ℂ)) ^ (-z)) ^ 2) / 2) =
      fun m : ℕ => (((((m + 1) * (m + 2) : ℕ) : ℂ)) ^ N * ((((m + 1 : ℕ) : ℂ)) ^ (-z)) ^ 2 +
        ((((m + 1) * (m + 2) : ℕ) : ℂ)) ^ N * ((((m + 2 : ℕ) : ℂ)) ^ (-z)) ^ 2) / 2 := by
    funext m
    ring
  have e2 : symZeta N z = ((∑ i ∈ range (N + 1), (N.choose i : ℂ) *
      riemannZeta (2 * z - 2 * N + i)) + ∑ i ∈ range (N + 1), (N.choose i : ℂ) * (-1) ^ i *
        (riemannZeta (2 * z - 2 * N + i) - 1)) / 2 := by
    unfold symZeta
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2]
  exact h

theorem differentiableAt_symZeta (N : ℕ) {z : ℂ}
    (hz : ∀ i ∈ range (N + 1), 2 * z - 2 * N + i ≠ 1) :
    DifferentiableAt ℂ (symZeta N) z := by
  show DifferentiableAt ℂ (fun z => (∑ i ∈ range (N + 1), (N.choose i : ℂ) * (1 + (-1) ^ i) *
    riemannZeta (2 * z - 2 * N + i) - ∑ i ∈ range (N + 1), (N.choose i : ℂ) * (-1) ^ i) / 2) z
  refine DifferentiableAt.div_const (DifferentiableAt.sub_const ?_ _) _
  refine DifferentiableAt.fun_sum fun i hi => (differentiableAt_const _).mul ?_
  exact (differentiableAt_riemannZeta (hz i hi)).comp
    (f := fun z : ℂ => 2 * z - 2 * N + i) z (by fun_prop)

/-- The derivative of the symmetric part at `0`. -/
theorem hasDerivAt_symZeta_zero (N : ℕ) :
    HasDerivAt (symZeta N) (∑ i ∈ range (N + 1),
      (N.choose i : ℂ) * (1 + (-1) ^ i) * deriv riemannZeta (-2 * N + i)) 0 := by
  have hne : ∀ i ∈ range (N + 1), (-2 * N + i : ℂ) ≠ 1 := by
    intro i hi h
    have hiN : i ≤ N := Nat.lt_succ_iff.1 (mem_range.1 hi)
    have := congrArg Complex.re h
    simp only [add_re, mul_re, neg_re, re_ofNat, im_ofNat, sub_zero, natCast_re,
      neg_im, natCast_im, mul_zero, one_re] at this
    have : (i : ℝ) ≤ N := by exact_mod_cast hiN
    linarith
  have hterm : ∀ i ∈ range (N + 1), HasDerivAt (fun z : ℂ => (N.choose i : ℂ) * (1 + (-1) ^ i) *
      riemannZeta (2 * z - 2 * N + i))
      ((N.choose i : ℂ) * (1 + (-1) ^ i) * (deriv riemannZeta (-2 * N + i) * 2)) 0 := by
    intro i hi
    refine HasDerivAt.const_mul _ ?_
    have haff : HasDerivAt (fun z : ℂ => 2 * z - 2 * N + i) 2 0 := by
      have := ((hasDerivAt_id (0 : ℂ)).const_mul 2).sub_const (2 * (N : ℂ)) |>.add_const (i : ℂ)
      simpa using this
    have hz : (2 * (0 : ℂ) - 2 * N + i) = -2 * N + i := by ring
    have hζ : HasDerivAt riemannZeta (deriv riemannZeta (-2 * N + i))
        (2 * (0 : ℂ) - 2 * N + i) := by
      rw [hz]
      exact (differentiableAt_riemannZeta (hne i hi)).hasDerivAt
    exact hζ.comp (0 : ℂ) haff
  have hsum := (HasDerivAt.fun_sum hterm).sub_const
    (∑ i ∈ range (N + 1), (N.choose i : ℂ) * (-1) ^ i) |>.div_const 2
  refine hsum.congr_deriv ?_
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by ring

end BrownianAffine.SpectralZeta
