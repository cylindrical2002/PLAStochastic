import PLAStochastic.Affine.Moments.Anchored.AllIntegerMoments
import Mathlib.Algebra.Polynomial.Roots

/-! # The anchored coefficient recurrence and its odd-zeta readout

The moment polynomial `P_q(y) = Im((y + i)(y² + 2iy)^q)` is `V_q(y²)` for the integer
polynomials `V_0 = 1`, `V_1 = 3X`, `V_{q+2} = 2X V_{q+1} - (X² + 4X) V_q`. This gives the
closed finite form of `V_q`, the coefficient recurrence, and the explicit readout of every
positive integer moment of the actual anchored Brownian lifetime from the coefficients.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Finset Polynomial
open scoped NNReal
namespace BrownianAffine

/-- The anchored recurrence polynomials `V_q ∈ ℤ[X]`. -/
def anchoredRecurrencePoly : ℕ → ℤ[X]
  | 0 => 1
  | 1 => 3 * X
  | q + 2 => 2 * X * anchoredRecurrencePoly (q + 1) - (X ^ 2 + 4 * X) * anchoredRecurrencePoly q

theorem anchoredRecurrencePoly_zero : anchoredRecurrencePoly 0 = 1 := rfl

theorem anchoredRecurrencePoly_one : anchoredRecurrencePoly 1 = 3 * X := rfl

theorem anchoredRecurrencePoly_add_two (q : ℕ) :
    anchoredRecurrencePoly (q + 2) =
      2 * X * anchoredRecurrencePoly (q + 1) - (X ^ 2 + 4 * X) * anchoredRecurrencePoly q := rfl

/-- `w = y² + 2iy` is a root of `w² - 2y²w + (y⁴ + 4y²)`, so `P_q` obeys the same recurrence. -/
theorem anchoredMomentPolynomial_add_two (q : ℕ) (y : ℝ) :
    anchoredMomentPolynomial (q + 2) y =
      2 * y ^ 2 * anchoredMomentPolynomial (q + 1) y -
        (y ^ 4 + 4 * y ^ 2) * anchoredMomentPolynomial q y := by
  unfold anchoredMomentPolynomial
  set w : ℂ := (y : ℂ) ^ 2 + 2 * (y : ℂ) * Complex.I
  have hw : w ^ 2 = ((2 * y ^ 2 : ℝ) : ℂ) * w - ((y ^ 4 + 4 * y ^ 2 : ℝ) : ℂ) := by
    simp only [w]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have he : ((y : ℂ) + Complex.I) * w ^ (q + 2) =
      ((2 * y ^ 2 : ℝ) : ℂ) * (((y : ℂ) + Complex.I) * w ^ (q + 1)) -
        ((y ^ 4 + 4 * y ^ 2 : ℝ) : ℂ) * (((y : ℂ) + Complex.I) * w ^ q) := by
    rw [pow_add, hw]
    ring
  rw [he, Complex.sub_im, Complex.im_ofReal_mul, Complex.im_ofReal_mul]

theorem anchoredMomentPolynomial_zero (y : ℝ) : anchoredMomentPolynomial 0 y = 1 := by
  simp [anchoredMomentPolynomial]

/-- The analytic moment polynomial is the recurrence polynomial evaluated at `y²`. -/
theorem anchoredMomentPolynomial_eq_eval (q : ℕ) (y : ℝ) :
    anchoredMomentPolynomial q y =
      ((anchoredRecurrencePoly q).map (Int.castRingHom ℝ)).eval (y ^ 2) := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    match q, ih with
    | 0, _ => simp [anchoredMomentPolynomial_zero, anchoredRecurrencePoly]
    | 1, _ =>
      simp [anchoredMomentPolynomial_one, anchoredRecurrencePoly]
    | q + 2, ih =>
      rw [anchoredMomentPolynomial_add_two, ih (q + 1) (by omega), ih q (by omega),
        anchoredRecurrencePoly_add_two]
      simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_pow,
        Polynomial.map_ofNat, Polynomial.map_X, eval_sub, eval_mul, eval_add, eval_pow, eval_X,
        eval_ofNat]
      ring

/-- (A2): `V_q = Σ_{r ≤ q/2} (-4)^r (C(q,2r) + 2 C(q,2r+1)) X^(q-r)`. -/
theorem anchoredRecurrencePoly_eq_sum (q : ℕ) :
    anchoredRecurrencePoly q = ∑ r ∈ range (q / 2 + 1),
      C ((-4 : ℤ) ^ r * ((q.choose (2 * r) : ℤ) + 2 * (q.choose (2 * r + 1) : ℤ))) *
        X ^ (q - r) := by
  apply Polynomial.map_injective (Int.castRingHom ℝ) Int.cast_injective
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.Infinite.mono _ (Set.Ici_infinite (0 : ℝ))
  intro x hx
  change 0 ≤ x at hx
  obtain ⟨y, rfl⟩ : ∃ y, y ^ 2 = x := ⟨Real.sqrt x, Real.sq_sqrt hx⟩
  change _ = _
  rw [← anchoredMomentPolynomial_eq_eval, anchoredMomentPolynomial_eq_sum,
    Polynomial.map_sum, eval_finsetSum]
  apply sum_congr rfl
  intro r _
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, eval_mul,
    eval_C, eval_pow, eval_X]
  simp only [eq_intCast]
  push_cast
  rw [← pow_mul, show ((-4 : ℝ)) ^ r = (-1) ^ r * 4 ^ r by rw [← mul_pow]; norm_num]

/-! ### The coefficient recurrence (A3) -/

private theorem anchoredRecurrencePoly_add_two_shift (q : ℕ) :
    anchoredRecurrencePoly (q + 2) =
      X * (2 * anchoredRecurrencePoly (q + 1) - 4 * anchoredRecurrencePoly q) -
        X ^ 2 * anchoredRecurrencePoly q := by
  rw [anchoredRecurrencePoly_add_two]
  ring

/-- `v_{0,j} = 1_{j = 0}`. -/
theorem coeff_anchoredRecurrencePoly_zero (j : ℕ) :
    (anchoredRecurrencePoly 0).coeff j = if j = 0 then 1 else 0 := by
  rw [anchoredRecurrencePoly_zero, coeff_one]

/-- `v_{1,j} = 3 · 1_{j = 1}`. -/
theorem coeff_anchoredRecurrencePoly_one (j : ℕ) :
    (anchoredRecurrencePoly 1).coeff j = if j = 1 then 3 else 0 := by
  rw [anchoredRecurrencePoly_one, coeff_ofNat_mul, coeff_X]
  rcases eq_or_ne j 1 with rfl | h
  · simp
  · simp [h, Ne.symm h]

/-- (A3) at indices `j + 2 ≥ 2`: `v_{q+2,j+2} = 2v_{q+1,j+1} - v_{q,j} - 4v_{q,j+1}`. -/
theorem coeff_anchoredRecurrencePoly_add_two (q j : ℕ) :
    (anchoredRecurrencePoly (q + 2)).coeff (j + 2) =
      2 * (anchoredRecurrencePoly (q + 1)).coeff (j + 1) - (anchoredRecurrencePoly q).coeff j -
        4 * (anchoredRecurrencePoly q).coeff (j + 1) := by
  have h1 : (X * (2 * anchoredRecurrencePoly (q + 1) - 4 * anchoredRecurrencePoly q)).coeff
      (j + 2) = (2 * anchoredRecurrencePoly (q + 1) - 4 * anchoredRecurrencePoly q).coeff
      (j + 1) := coeff_X_mul _ (j + 1)
  have h2 : (X ^ 2 * anchoredRecurrencePoly q).coeff (j + 2) =
      (anchoredRecurrencePoly q).coeff j := coeff_X_pow_mul _ 2 j
  rw [anchoredRecurrencePoly_add_two_shift, coeff_sub, h1, h2, coeff_sub, coeff_ofNat_mul,
    coeff_ofNat_mul]
  ring

/-- (A3) at index `1`, where the out-of-range coefficient `v_{q,-1}` is zero. -/
theorem coeff_anchoredRecurrencePoly_add_two_one (q : ℕ) :
    (anchoredRecurrencePoly (q + 2)).coeff 1 =
      2 * (anchoredRecurrencePoly (q + 1)).coeff 0 - 4 * (anchoredRecurrencePoly q).coeff 0 := by
  have h1 : (X * (2 * anchoredRecurrencePoly (q + 1) - 4 * anchoredRecurrencePoly q)).coeff 1 =
      (2 * anchoredRecurrencePoly (q + 1) - 4 * anchoredRecurrencePoly q).coeff 0 :=
    coeff_X_mul _ 0
  rw [anchoredRecurrencePoly_add_two_shift, coeff_sub, h1, coeff_X_pow_mul', coeff_sub,
    coeff_ofNat_mul, coeff_ofNat_mul, if_neg (by norm_num), sub_zero]

/-- (A3) at index `0`, where both out-of-range coefficients are zero. -/
theorem coeff_anchoredRecurrencePoly_add_two_zero (q : ℕ) :
    (anchoredRecurrencePoly (q + 2)).coeff 0 = 0 := by
  rw [anchoredRecurrencePoly_add_two_shift, coeff_sub, coeff_X_mul_zero, coeff_X_pow_mul',
    if_neg (by norm_num), sub_zero]

/-- The coefficients `v_{q,j}` for every integer `j`, with `v_{q,j} = 0` for `j < 0`. -/
def anchoredRecurrenceCoeff (q : ℕ) (j : ℤ) : ℤ :=
  if 0 ≤ j then (anchoredRecurrencePoly q).coeff j.toNat else 0

/-- (A3) for all integer indices, with the out-of-range convention built in. -/
theorem anchoredRecurrenceCoeff_add_two (q : ℕ) (j : ℤ) :
    anchoredRecurrenceCoeff (q + 2) j =
      2 * anchoredRecurrenceCoeff (q + 1) (j - 1) - anchoredRecurrenceCoeff q (j - 2) -
        4 * anchoredRecurrenceCoeff q (j - 1) := by
  rcases lt_or_ge j 0 with hj | hj
  · simp only [anchoredRecurrenceCoeff, if_neg (show ¬ 0 ≤ j by omega),
      if_neg (show ¬ 0 ≤ j - 1 by omega), if_neg (show ¬ 0 ≤ j - 2 by omega)]
    ring
  · rcases (show j = 0 ∨ j = 1 ∨ 2 ≤ j by omega) with rfl | rfl | hj2
    · simp [anchoredRecurrenceCoeff, coeff_anchoredRecurrencePoly_add_two_zero]
    · simp [anchoredRecurrenceCoeff, coeff_anchoredRecurrencePoly_add_two_one]
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = n + 2 := ⟨(j - 2).toNat, by omega⟩
      have h0 : ((n : ℤ) + 2).toNat = n + 2 := by omega
      have h1 : ((n : ℤ) + 2 - 1).toNat = n + 1 := by omega
      have h2 : ((n : ℤ) + 2 - 2).toNat = n := by omega
      simp only [anchoredRecurrenceCoeff]
      rw [if_pos (show (0 : ℤ) ≤ n + 2 by omega), if_pos (show (0 : ℤ) ≤ n + 2 - 1 by omega),
        if_pos (show (0 : ℤ) ≤ n + 2 - 1 by omega), if_pos (show (0 : ℤ) ≤ n + 2 - 2 by omega),
        h0, h1, h2, coeff_anchoredRecurrencePoly_add_two]

/-! ### Degree bounds -/

/-- `V_q` has degree at most `q`. -/
theorem coeff_anchoredRecurrencePoly_eq_zero_of_lt {q j : ℕ} (h : q < j) :
    (anchoredRecurrencePoly q).coeff j = 0 := by
  induction q using Nat.strong_induction_on generalizing j with
  | _ q ih =>
    match q, ih, h with
    | 0, _, h => rw [coeff_anchoredRecurrencePoly_zero, if_neg (by omega)]
    | 1, _, h => rw [coeff_anchoredRecurrencePoly_one, if_neg (by omega)]
    | q + 2, ih, h =>
      obtain ⟨j, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
      rw [coeff_anchoredRecurrencePoly_add_two, ih (q + 1) (by omega) (by omega),
        ih q (by omega) (by omega), ih q (by omega) (by omega)]
      ring

theorem natDegree_anchoredRecurrencePoly_le (q : ℕ) : (anchoredRecurrencePoly q).natDegree ≤ q :=
  natDegree_le_iff_coeff_eq_zero.mpr fun _ h => coeff_anchoredRecurrencePoly_eq_zero_of_lt h

/-- For `q ≥ 1` the constant coefficient vanishes: every monomial of `V_q(y²)` is a positive even
power of `y`. -/
theorem coeff_zero_anchoredRecurrencePoly {q : ℕ} (hq : 1 ≤ q) :
    (anchoredRecurrencePoly q).coeff 0 = 0 := by
  match q, hq with
  | 1, _ => rw [coeff_anchoredRecurrencePoly_one, if_neg (by norm_num)]
  | q + 2, _ => exact coeff_anchoredRecurrencePoly_add_two_zero q

/-- The moment polynomial written through the coefficients `v_{q,j}`, `1 ≤ j ≤ q`. -/
theorem anchoredMomentPolynomial_eq_sum_coeff {q : ℕ} (hq : 1 ≤ q) (y : ℝ) :
    anchoredMomentPolynomial q y =
      ∑ j ∈ Icc 1 q, ((anchoredRecurrencePoly q).coeff j : ℝ) * y ^ (2 * j) := by
  have hd : ((anchoredRecurrencePoly q).map (Int.castRingHom ℝ)).natDegree < q + 1 :=
    natDegree_map_le.trans_lt (Nat.lt_succ_of_le (natDegree_anchoredRecurrencePoly_le q))
  rw [anchoredMomentPolynomial_eq_eval, eval_eq_sum_range' hd]
  simp only [coeff_map, eq_intCast, ← pow_mul]
  symm
  apply sum_subset
  · intro j hj
    rw [mem_Icc] at hj
    rw [mem_range]
    omega
  · intro j hj hj'
    rw [mem_range] at hj
    rw [mem_Icc] at hj'
    obtain rfl : j = 0 := by omega
    rw [coeff_zero_anchoredRecurrencePoly hq, Int.cast_zero, zero_mul]

/-! ### The readout (A4) -/

/-- Termwise integration of `V_q(y²) / sinh(πy/2)` gives the coefficient readout. -/
theorem anchoredMomentIntegral_eq_coeff_readout {q : ℕ} (hq : 1 ≤ q) :
    anchoredMomentIntegral q =
      1 / (2 ^ q * ((q - 1).factorial : ℝ)) *
        ∑ j ∈ Icc 1 q, ((anchoredRecurrencePoly q).coeff j : ℝ) * ((2 * j).factorial : ℝ) *
          (2 ^ (2 * j + 1) - 1) * (riemannZeta (2 * j + 1)).re / Real.pi ^ (2 * j) := by
  have hpoly (y : ℝ) : anchoredMomentPolynomial q y / Real.sinh (Real.pi * y / 2) =
      ∑ j ∈ Icc 1 q, ((anchoredRecurrencePoly q).coeff j : ℝ) *
        (y ^ (2 * j) / Real.sinh (Real.pi * y / 2)) := by
    rw [anchoredMomentPolynomial_eq_sum_coeff hq, sum_div]
    apply sum_congr rfl
    intro j _
    ring
  have hpos {j : ℕ} (h : j ∈ Icc 1 q) : 0 < j := by
    rw [mem_Icc] at h
    omega
  unfold anchoredMomentIntegral
  simp only [hpoly]
  rw [integral_finsetSum _ (fun j h => (integrableOn_even_pow_div_sinh_pi (hpos h)).const_mul _)]
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  have hg : Real.Gamma ((n + 1 : ℕ) : ℝ) = (n.factorial : ℝ) := by
    rw [Nat.cast_add_one, Real.Gamma_nat_eq_factorial]
  rw [hg, Nat.add_sub_cancel, mul_sum, mul_sum]
  apply sum_congr rfl
  intro j h
  rw [integral_const_mul, integral_even_pow_div_sinh_pi (hpos h)]
  have hz : ((2 * j + 1 : ℕ) : ℂ) = 2 * (j : ℂ) + 1 := by push_cast; ring
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  rw [hz]
  field_simp
  ring

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- (A4): every positive integer moment of the actual anchored Brownian lifetime is the linear
odd-zeta readout of the coefficients of the recurrence polynomial `V_q`. -/
theorem anchoredUnitLifetime_moment_eq_coeff_readout (hB : IsBrownianReal B μ) {q : ℕ}
    (hq : 1 ≤ q) :
    (∫ ω, anchoredUnitLifetime B ω ^ q ∂μ) =
      1 / (2 ^ q * ((q - 1).factorial : ℝ)) *
        ∑ j ∈ Icc 1 q, ((anchoredRecurrencePoly q).coeff j : ℝ) * ((2 * j).factorial : ℝ) *
          (2 ^ (2 * j + 1) - 1) * (riemannZeta (2 * j + 1)).re / Real.pi ^ (2 * j) := by
  rw [anchoredUnitLifetime_moment_eq_anchoredMomentIntegral hB hq,
    anchoredMomentIntegral_eq_coeff_readout hq]

/-! ### Low-order checks -/

theorem anchoredRecurrencePoly_two : anchoredRecurrencePoly 2 = 5 * X ^ 2 - 4 * X := by
  have h : anchoredRecurrencePoly 2 = 2 * X * (3 * X) - (X ^ 2 + 4 * X) * 1 := rfl
  rw [h]
  ring

theorem anchoredRecurrencePoly_three : anchoredRecurrencePoly 3 = 7 * X ^ 3 - 20 * X ^ 2 := by
  have h : anchoredRecurrencePoly 3 =
      2 * X * anchoredRecurrencePoly 2 - (X ^ 2 + 4 * X) * (3 * X) := rfl
  rw [h, anchoredRecurrencePoly_two]
  ring

theorem anchoredRecurrencePoly_four :
    anchoredRecurrencePoly 4 = 9 * X ^ 4 - 56 * X ^ 3 + 16 * X ^ 2 := by
  have h : anchoredRecurrencePoly 4 =
      2 * X * anchoredRecurrencePoly 3 - (X ^ 2 + 4 * X) * anchoredRecurrencePoly 2 := rfl
  rw [h, anchoredRecurrencePoly_three, anchoredRecurrencePoly_two]
  ring

/-- The right side of (A4), the readout used in `anchoredUnitLifetime_moment_eq_coeff_readout`. -/
def anchoredCoeffReadout (q : ℕ) : ℝ :=
  1 / (2 ^ q * ((q - 1).factorial : ℝ)) *
    ∑ j ∈ Icc 1 q, ((anchoredRecurrencePoly q).coeff j : ℝ) * ((2 * j).factorial : ℝ) *
      (2 ^ (2 * j + 1) - 1) * (riemannZeta (2 * j + 1)).re / Real.pi ^ (2 * j)

theorem anchoredCoeffReadout_one :
    anchoredCoeffReadout 1 = 21 * (riemannZeta 3).re / Real.pi ^ 2 := by
  rw [anchoredCoeffReadout, show Icc 1 1 = {1} by rfl, sum_singleton,
    coeff_anchoredRecurrencePoly_one, if_pos rfl]
  norm_num [Nat.factorial]
  ring

theorem anchoredCoeffReadout_two :
    anchoredCoeffReadout 2 =
      930 * (riemannZeta 5).re / Real.pi ^ 4 - 14 * (riemannZeta 3).re / Real.pi ^ 2 := by
  rw [anchoredCoeffReadout, show Icc 1 2 = {1, 2} by rfl, sum_pair (by norm_num),
    anchoredRecurrencePoly_two]
  norm_num [coeff_X, Nat.factorial]
  ring

/-- Cross-check at `q = 1` against the separately evaluated `anchoredUnitLifetime_mean_zeta`. -/
theorem anchoredCoeffReadout_one_eq_mean (hB : IsBrownianReal B μ) :
    anchoredCoeffReadout 1 = ∫ ω, anchoredUnitLifetime B ω ∂μ := by
  rw [anchoredCoeffReadout_one, anchoredUnitLifetime_mean_zeta hB]

/-- Cross-check at `q = 2` against `anchoredUnitLifetime_second_moment_zeta`. -/
theorem anchoredCoeffReadout_two_eq_second_moment (hB : IsBrownianReal B μ) :
    anchoredCoeffReadout 2 = ∫ ω, anchoredUnitLifetime B ω ^ 2 ∂μ := by
  rw [anchoredCoeffReadout_two, anchoredUnitLifetime_second_moment_zeta hB]

end BrownianAffine
