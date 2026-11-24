import PLAStochastic.ForMathlib.NumberTheory.LSeries.RiemannZetaDerivNegEven
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.BigOperators.Intervals

/-! # Optimal lifetime moments of all orders: the coefficient algebra

The optimal spectral polynomials `U_n ∈ ℤ[X]` satisfy `U_0 = 1`, `U_1 = X` and
`U_(n+2) = 2X U_(n+1) - (X^2 - X) U_n` (O1), with the finite form
`U_n = ∑_(r ≤ n/2) choose n (2r) X^(n-r)` (O2) and the coefficient recurrence (O3).
The weights `d_j = (-1)^j (2j)!/2^(2j+1) · ζ(2j+1)/π^(2j)` (O4) are the values `ζ'(-2j)`.
The sums `J_N = 2 ∑_(j=1)^N [X^j]U_N · d_j` (O5) are the finite symmetric zeta sums
`2 ∑_(r ≤ N/2) choose N (2r) ζ'(-2N+2r)`. The readout (O7) combines `J_(q+1)`, `J_q`, `J_(q-1)`.
The leading weight `d_(q+1)` cancels, so the readout involves only `ζ(3), …, ζ(2q+1)`. -/
noncomputable section
open Polynomial Finset
open scoped Real
namespace BrownianAffine

/-- The optimal spectral polynomials `U_n` (O1). -/
noncomputable def optimalSpectralPoly : ℕ → Polynomial ℤ
  | 0 => 1
  | 1 => X
  | n + 2 => 2 * X * optimalSpectralPoly (n + 1) - (X ^ 2 - X) * optimalSpectralPoly n

@[simp] theorem optimalSpectralPoly_zero : optimalSpectralPoly 0 = 1 := by
  rw [optimalSpectralPoly]

@[simp] theorem optimalSpectralPoly_one : optimalSpectralPoly 1 = X := by
  rw [optimalSpectralPoly]

/-- **(O1).** The two-step recurrence of `U_n`. -/
theorem optimalSpectralPoly_add_two (n : ℕ) :
    optimalSpectralPoly (n + 2) =
      2 * X * optimalSpectralPoly (n + 1) - (X ^ 2 - X) * optimalSpectralPoly n := by
  rw [optimalSpectralPoly]

/-- The coefficient recurrence (O3) in natural-number indices: the cases `j = 0`, `j = 1` and
`j + 2`, the first two with the out-of-range coefficients removed. -/
theorem optimalSpectralPoly_coeff_add_two_zero (n : ℕ) :
    (optimalSpectralPoly (n + 2)).coeff 0 = 0 := by
  rw [optimalSpectralPoly_add_two]
  simp [mul_assoc]

theorem optimalSpectralPoly_coeff_add_two_one (n : ℕ) :
    (optimalSpectralPoly (n + 2)).coeff 1 =
      2 * (optimalSpectralPoly (n + 1)).coeff 0 + (optimalSpectralPoly n).coeff 0 := by
  rw [optimalSpectralPoly_add_two, sub_mul, mul_assoc]
  simp only [coeff_sub, ← C_ofNat, coeff_C_mul, coeff_X_pow_mul', coeff_X_mul]
  simp

theorem optimalSpectralPoly_coeff_add_two_add_two (n j : ℕ) :
    (optimalSpectralPoly (n + 2)).coeff (j + 2) =
      2 * (optimalSpectralPoly (n + 1)).coeff (j + 1) - (optimalSpectralPoly n).coeff j +
        (optimalSpectralPoly n).coeff (j + 1) := by
  rw [optimalSpectralPoly_add_two, sub_mul, mul_assoc]
  simp only [coeff_sub, ← C_ofNat, coeff_C_mul, coeff_X_pow_mul, coeff_X_mul]
  ring

/-- Pascal-type identity behind the closed form of the coefficients. -/
private theorem choose_add_three_two_mul_add_two (N m : ℕ) :
    ((N + 2).choose (2 * m + 2) : ℤ) =
      2 * ((N + 1).choose (2 * m + 2) : ℤ) - (N.choose (2 * m + 2) : ℤ) +
        (N.choose (2 * m) : ℤ) := by
  have h1 : (N + 2).choose (2 * m + 2) = (N + 1).choose (2 * m + 1) + (N + 1).choose (2 * m + 2) :=
    Nat.choose_succ_succ' (N + 1) (2 * m + 1)
  have h2 : (N + 1).choose (2 * m + 1) = N.choose (2 * m) + N.choose (2 * m + 1) :=
    Nat.choose_succ_succ' N (2 * m)
  have h3 : (N + 1).choose (2 * m + 2) = N.choose (2 * m + 1) + N.choose (2 * m + 2) :=
    Nat.choose_succ_succ' N (2 * m + 1)
  rw [h1, h2, h3]
  push_cast
  ring

/-- Closed form of the coefficients: `[X^j] U_n = choose n (2 (n - j))` for `j ≤ n`. -/
theorem optimalSpectralPoly_coeff (n j : ℕ) :
    (optimalSpectralPoly n).coeff j = if j ≤ n then (n.choose (2 * (n - j)) : ℤ) else 0 := by
  induction n using Nat.strong_induction_on generalizing j with
  | _ n ih =>
    match n, ih with
    | 0, _ => rcases j with _ | j <;> simp [coeff_one]
    | 1, _ => rcases j with _ | _ | j <;> simp [coeff_X]
    | n + 2, ih =>
      have h1 := ih (n + 1) (by omega)
      have h0 := ih n (by omega)
      rcases j with _ | _ | j
      · rw [optimalSpectralPoly_coeff_add_two_zero, if_pos (Nat.zero_le _),
          Nat.choose_eq_zero_of_lt (by omega)]
        simp
      · rw [optimalSpectralPoly_coeff_add_two_one, h1, h0, if_pos (Nat.zero_le _),
          if_pos (Nat.zero_le _), if_pos (by omega), Nat.choose_eq_zero_of_lt (by omega)]
        rcases n with _ | n
        · simp
        · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]
          simp
      · rw [optimalSpectralPoly_coeff_add_two_add_two, h1, h0, h0]
        by_cases hjn : j ≤ n
        · rcases Nat.lt_or_eq_of_le hjn with hlt | rfl
          · obtain ⟨m, rfl⟩ : ∃ m, n = j + m + 1 := ⟨n - j - 1, by omega⟩
            have e1 : j + m + 1 + 1 - (j + 1) = m + 1 := by omega
            have e2 : j + m + 1 - j = m + 1 := by omega
            have e3 : j + m + 1 - (j + 1) = m := by omega
            have e4 : j + m + 1 + 2 - (j + 2) = m + 1 := by omega
            rw [if_pos (show j + 1 ≤ j + m + 1 + 1 by omega), if_pos (show j ≤ j + m + 1 by omega),
              if_pos (show j + 1 ≤ j + m + 1 by omega),
              if_pos (show j + 2 ≤ j + m + 1 + 2 by omega), e1, e2, e3, e4, mul_add, mul_one]
            exact (choose_add_three_two_mul_add_two (j + m + 1) m).symm
          · rw [if_pos (show j + 1 ≤ j + 1 by omega), if_pos le_rfl,
              if_neg (show ¬(j + 1 ≤ j) by omega), if_pos (show j + 2 ≤ j + 2 by omega)]
            simp
        · rw [if_neg (show ¬(j + 1 ≤ n + 1) by omega), if_neg hjn,
            if_neg (show ¬(j + 1 ≤ n) by omega), if_neg (show ¬(j + 2 ≤ n + 2) by omega)]
          simp

theorem optimalSpectralPoly_coeff_of_lt {n j : ℕ} (h : n < j) :
    (optimalSpectralPoly n).coeff j = 0 := by
  rw [optimalSpectralPoly_coeff, if_neg (by omega)]

theorem optimalSpectralPoly_coeff_self (n : ℕ) : (optimalSpectralPoly n).coeff n = 1 := by
  rw [optimalSpectralPoly_coeff, if_pos le_rfl, Nat.sub_self, mul_zero, Nat.choose_zero_right,
    Nat.cast_one]

/-- `U_n` has no constant term for `n ≥ 1`. -/
theorem optimalSpectralPoly_coeff_zero {n : ℕ} (hn : 1 ≤ n) :
    (optimalSpectralPoly n).coeff 0 = 0 := by
  rw [optimalSpectralPoly_coeff, if_pos (Nat.zero_le _), Nat.sub_zero,
    Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]

theorem optimalSpectralPoly_natDegree (n : ℕ) : (optimalSpectralPoly n).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    exact optimalSpectralPoly_coeff_of_lt hN
  · rw [optimalSpectralPoly_coeff_self]
    exact one_ne_zero

/-- `U_n` is monic of degree `n`. -/
theorem optimalSpectralPoly_monic (n : ℕ) : (optimalSpectralPoly n).Monic := by
  rw [Monic, leadingCoeff, optimalSpectralPoly_natDegree, optimalSpectralPoly_coeff_self]

/-- **(O2).** The finite form of `U_n`. -/
theorem optimalSpectralPoly_eq_sum (n : ℕ) :
    optimalSpectralPoly n =
      ∑ r ∈ range (n / 2 + 1), C (n.choose (2 * r) : ℤ) * X ^ (n - r) := by
  ext j
  rw [finsetSum_coeff, optimalSpectralPoly_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (n - j)]
  · by_cases hj : j ≤ n
    · rw [if_pos hj, if_pos (by omega)]
    · rw [if_neg hj, if_neg (by omega)]
  · intro r hr hne
    rw [if_neg]
    rw [Finset.mem_range] at hr
    omega
  · intro hnot
    rw [Finset.mem_range] at hnot
    split_ifs with h
    · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
    · rfl

/-- The coefficients `u_(n,j) = [X^j] U_n` indexed by all integers, set to zero out of range. -/
def optimalSpectralCoeff (n : ℕ) (j : ℤ) : ℤ :=
  if 0 ≤ j then (optimalSpectralPoly n).coeff j.toNat else 0

theorem optimalSpectralCoeff_natCast (n j : ℕ) :
    optimalSpectralCoeff n j = (optimalSpectralPoly n).coeff j := by
  rw [optimalSpectralCoeff, if_pos (Int.natCast_nonneg j), Int.toNat_natCast]

theorem optimalSpectralCoeff_of_neg (n : ℕ) {j : ℤ} (hj : j < 0) :
    optimalSpectralCoeff n j = 0 := by
  rw [optimalSpectralCoeff, if_neg (by omega)]

/-- Initial values of (O3). -/
theorem optimalSpectralCoeff_zero (j : ℤ) : optimalSpectralCoeff 0 j = if j = 0 then 1 else 0 := by
  rcases lt_or_ge j 0 with hj | hj
  · rw [optimalSpectralCoeff_of_neg 0 hj, if_neg (by omega)]
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hj
    rw [optimalSpectralCoeff_natCast, optimalSpectralPoly_zero, coeff_one]
    rcases k with _ | k
    · simp
    · simp only [Nat.cast_add, Nat.cast_one]
      rw [if_neg (by omega), if_neg (by omega)]

theorem optimalSpectralCoeff_one (j : ℤ) : optimalSpectralCoeff 1 j = if j = 1 then 1 else 0 := by
  rcases lt_or_ge j 0 with hj | hj
  · rw [optimalSpectralCoeff_of_neg 1 hj, if_neg (by omega)]
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hj
    rw [optimalSpectralCoeff_natCast, optimalSpectralPoly_one, coeff_X]
    rcases k with _ | _ | k <;> simp
    omega

/-- **(O3).** `u_(n+2,j) = 2 u_(n+1,j-1) - u_(n,j-2) + u_(n,j-1)` for every integer `j`. -/
theorem optimalSpectralCoeff_add_two (n : ℕ) (j : ℤ) :
    optimalSpectralCoeff (n + 2) j =
      2 * optimalSpectralCoeff (n + 1) (j - 1) - optimalSpectralCoeff n (j - 2) +
        optimalSpectralCoeff n (j - 1) := by
  rcases lt_or_ge j 0 with hj | hj
  · rw [optimalSpectralCoeff_of_neg _ hj,
      optimalSpectralCoeff_of_neg (n + 1) (show j - 1 < 0 by omega),
      optimalSpectralCoeff_of_neg n (show j - 2 < 0 by omega),
      optimalSpectralCoeff_of_neg n (show j - 1 < 0 by omega)]
    ring
  rcases (show j = 0 ∨ j = 1 ∨ 2 ≤ j by omega) with rfl | rfl | hj2
  · have h := optimalSpectralCoeff_natCast (n + 2) 0
    rw [Nat.cast_zero] at h
    rw [h, optimalSpectralPoly_coeff_add_two_zero,
      optimalSpectralCoeff_of_neg (n + 1) (show (0 : ℤ) - 1 < 0 by norm_num),
      optimalSpectralCoeff_of_neg n (show (0 : ℤ) - 2 < 0 by norm_num),
      optimalSpectralCoeff_of_neg n (show (0 : ℤ) - 1 < 0 by norm_num)]
    ring
  · have h1 := optimalSpectralCoeff_natCast (n + 2) 1
    have h0 := optimalSpectralCoeff_natCast (n + 1) 0
    have h0' := optimalSpectralCoeff_natCast n 0
    rw [Nat.cast_one] at h1
    rw [Nat.cast_zero] at h0 h0'
    rw [show (1 : ℤ) - 1 = 0 by norm_num, h1, h0, h0',
      optimalSpectralCoeff_of_neg n (show (1 : ℤ) - 2 < 0 by norm_num),
      optimalSpectralPoly_coeff_add_two_one]
    ring
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = k + 2 := ⟨(j - 2).toNat, by omega⟩
    have e1 : (k : ℤ) + 2 - 1 = ((k + 1 : ℕ) : ℤ) := by push_cast; ring
    have e2 : (k : ℤ) + 2 - 2 = ((k : ℕ) : ℤ) := by ring
    have e0 : (k : ℤ) + 2 = ((k + 2 : ℕ) : ℤ) := by push_cast; ring
    rw [e1, e2, e0, optimalSpectralCoeff_natCast, optimalSpectralCoeff_natCast,
      optimalSpectralCoeff_natCast, optimalSpectralCoeff_natCast,
      optimalSpectralPoly_coeff_add_two_add_two]

/-! ## The zeta weights and the spectral derivative sums -/

/-- **(O4).** `d_j = (-1)^j (2j)!/2^(2j+1) · ζ(2j+1)/π^(2j)`. -/
def optimalZetaWeight (j : ℕ) : ℝ :=
  (-1) ^ j * ((2 * j).factorial : ℝ) / 2 ^ (2 * j + 1) * (riemannZeta (2 * j + 1)).re /
    π ^ (2 * j)

/-- **(O4).** `d_j = ζ'(-2j)` for `j ≥ 1`. -/
theorem ofReal_optimalZetaWeight {j : ℕ} (hj : 1 ≤ j) :
    (optimalZetaWeight j : ℂ) = deriv riemannZeta (-2 * j) := by
  rw [deriv_riemannZeta_neg_two_mul_nat_eq_ofReal hj, optimalZetaWeight]

/-- **(O5).** `J_N = 2 ∑_(j=1)^N [X^j]U_N · d_j`. -/
def optimalSpectralDeriv (N : ℕ) : ℝ :=
  2 * ∑ j ∈ Icc 1 N, ((optimalSpectralPoly N).coeff j : ℝ) * optimalZetaWeight j

/-- The symmetric zeta-derivative sum `2 ∑_(r ≤ N/2) choose N (2r) ζ'(-2N+2r)` of (T6). -/
def optimalZetaDerivSum (N : ℕ) : ℂ :=
  2 * ∑ r ∈ range (N / 2 + 1), (N.choose (2 * r) : ℂ) * deriv riemannZeta (-2 * N + 2 * r)

/-- **(O5) = (T6).** For `N ≥ 1`, `J_N = 2 ∑_(r ≤ N/2) choose N (2r) ζ'(-2N+2r)`. -/
theorem ofReal_optimalSpectralDeriv {N : ℕ} (hN : 1 ≤ N) :
    (optimalSpectralDeriv N : ℂ) =
      2 * ∑ r ∈ range (N / 2 + 1), (N.choose (2 * r) : ℂ) * deriv riemannZeta (-2 * N + 2 * r) := by
  set g : ℕ → ℂ := fun r => (N.choose (2 * r) : ℂ) * deriv riemannZeta (-2 * N + 2 * r) with hg
  have hterm : ∀ j ∈ Icc 1 N,
      ((((optimalSpectralPoly N).coeff j : ℝ) * optimalZetaWeight j : ℝ) : ℂ) = g (N - j) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    rw [Complex.ofReal_mul, ofReal_optimalZetaWeight hj.1, optimalSpectralPoly_coeff, if_pos hj.2,
      hg]
    have harg : (-2 * (j : ℂ)) = -2 * N + 2 * ((N - j : ℕ) : ℂ) := by
      rw [Nat.cast_sub hj.2]
      ring
    rw [harg]
    push_cast
    rfl
  have hreflect : ∑ j ∈ Icc 1 N, g (N - j) = ∑ r ∈ range N, g r := by
    apply Finset.sum_nbij' (fun j => N - j) (fun r => N - r)
    · intro j hj
      simp only [Finset.mem_Icc, Finset.mem_range] at hj ⊢
      omega
    · intro r hr
      simp only [Finset.mem_Icc, Finset.mem_range] at hr ⊢
      omega
    · intro j hj
      simp only [Finset.mem_Icc] at hj
      omega
    · intro r hr
      simp only [Finset.mem_range] at hr
      omega
    · intro j _
      rfl
  have hsubset : ∑ r ∈ range (N / 2 + 1), g r = ∑ r ∈ range N, g r := by
    apply Finset.sum_subset
    · intro r hr
      simp only [Finset.mem_range] at hr ⊢
      omega
    · intro r _ hr
      simp only [Finset.mem_range] at hr
      rw [hg]
      simp only
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
  rw [optimalSpectralDeriv, Complex.ofReal_mul, Complex.ofReal_sum, Finset.sum_congr rfl hterm,
    hreflect, ← hsubset, Complex.ofReal_ofNat]

theorem optimalZetaDerivSum_eq {N : ℕ} (hN : 1 ≤ N) :
    optimalZetaDerivSum N = (optimalSpectralDeriv N : ℂ) :=
  (ofReal_optimalSpectralDeriv hN).symm

/-! ## The moment readout -/

/-- **(O7).** The readout of the `q`-th optimal lifetime moment from `J_(q+1)`, `J_q`, `J_(q-1)`. -/
def optimalMomentReadout (q : ℕ) : ℝ :=
  8 ^ q * (-1) ^ (q + 1) / (3 * (q + 1) * q.factorial) *
    (4 * (2 * q + 1) * (2 * q + 3) *
        (-optimalSpectralDeriv (q + 1) + 2 * optimalZetaWeight (q + 1)) +
      4 * q * (2 * q + 1) * (-optimalSpectralDeriv q + 2 * optimalZetaWeight q) -
      q * (q - 1) * optimalSpectralDeriv (q - 1))

/-- `U_(q+1)` is monic, so `d_(q+1)` cancels: `-J_(q+1) + 2 d_(q+1)` involves only
`d_1, …, d_q`, hence only `ζ(3), …, ζ(2q+1)`. -/
theorem neg_optimalSpectralDeriv_succ_add_two_mul (q : ℕ) :
    -optimalSpectralDeriv (q + 1) + 2 * optimalZetaWeight (q + 1) =
      -2 * ∑ j ∈ Icc 1 q, ((optimalSpectralPoly (q + 1)).coeff j : ℝ) * optimalZetaWeight j := by
  rw [optimalSpectralDeriv, Finset.sum_Icc_succ_top (by omega : 1 ≤ q + 1),
    optimalSpectralPoly_coeff_self]
  push_cast
  ring

/-! ## Consistency with the first four moments -/

/-- Small values of `J_N`, read off from `U_1, …, U_5`. -/
theorem optimalSpectralDeriv_one : optimalSpectralDeriv 1 = 2 * optimalZetaWeight 1 := by
  simp [optimalSpectralDeriv]

theorem optimalSpectralDeriv_two :
    optimalSpectralDeriv 2 = 2 * optimalZetaWeight 1 + 2 * optimalZetaWeight 2 := by
  simp [optimalSpectralDeriv, optimalSpectralPoly_coeff, Finset.sum_Icc_succ_top]
  ring

theorem optimalSpectralDeriv_three :
    optimalSpectralDeriv 3 = 6 * optimalZetaWeight 2 + 2 * optimalZetaWeight 3 := by
  simp [optimalSpectralDeriv, optimalSpectralPoly_coeff, Finset.sum_Icc_succ_top]
  ring

theorem optimalSpectralDeriv_four :
    optimalSpectralDeriv 4 =
      2 * optimalZetaWeight 2 + 12 * optimalZetaWeight 3 + 2 * optimalZetaWeight 4 := by
  simp [optimalSpectralDeriv, optimalSpectralPoly_coeff, Finset.sum_Icc_succ_top]
  norm_num [Nat.choose]
  ring

theorem optimalSpectralDeriv_five :
    optimalSpectralDeriv 5 =
      10 * optimalZetaWeight 3 + 20 * optimalZetaWeight 4 + 2 * optimalZetaWeight 5 := by
  simp [optimalSpectralDeriv, optimalSpectralPoly_coeff, Finset.sum_Icc_succ_top]
  norm_num [Nat.choose]
  ring

/-- **(O6).** The `q = 1` form of the readout, with the boundary value `-1` in place of the
`J_0` term, is the known mean `40 ζ(3)/π^2 - 4/3`. -/
theorem optimalMomentReadout_boundary_one :
    (4 / 3 : ℝ) * (60 * (-optimalSpectralDeriv 2 + 2 * optimalZetaWeight 2) +
        12 * (-optimalSpectralDeriv 1 + 2 * optimalZetaWeight 1) - 1) =
      40 * (riemannZeta 3).re / π ^ 2 - 4 / 3 := by
  rw [optimalSpectralDeriv_two, optimalSpectralDeriv_one]
  norm_num [optimalZetaWeight, Nat.factorial]
  ring

/-- The readout at `q = 2` is the second moment of `optimalUnitLifetime_second_moment`. -/
theorem optimalMomentReadout_two :
    optimalMomentReadout 2 =
      2240 * (riemannZeta (5 : ℂ)).re / π ^ 4 - 224 * (riemannZeta (3 : ℂ)).re / (3 * π ^ 2) := by
  rw [optimalMomentReadout, show 2 + 1 = 3 from rfl, show 2 - 1 = 1 from rfl,
    optimalSpectralDeriv_three, optimalSpectralDeriv_two, optimalSpectralDeriv_one]
  norm_num [optimalZetaWeight, Nat.factorial]
  ring

/-- The readout at `q = 3` is the third moment of `optimalUnitLifetime_third_moment`. -/
theorem optimalMomentReadout_three :
    optimalMomentReadout 3 =
      120960 * (riemannZeta (7 : ℂ)).re / π ^ 6 - 5440 * (riemannZeta (5 : ℂ)).re / π ^ 4 +
        64 * (riemannZeta (3 : ℂ)).re / (3 * π ^ 2) := by
  rw [optimalMomentReadout, show 3 + 1 = 4 from rfl, show 3 - 1 = 2 from rfl,
    optimalSpectralDeriv_four, optimalSpectralDeriv_three, optimalSpectralDeriv_two]
  norm_num [optimalZetaWeight, Nat.factorial]
  ring

/-- The readout at `q = 4` is the fourth moment of `optimalUnitLifetime_fourth_moment`. -/
theorem optimalMomentReadout_four :
    optimalMomentReadout 4 =
      7096320 * (riemannZeta (9 : ℂ)).re / π ^ 8 - 365568 * (riemannZeta (7 : ℂ)).re / π ^ 6 +
        3072 * (riemannZeta (5 : ℂ)).re / π ^ 4 := by
  rw [optimalMomentReadout, show 4 + 1 = 5 from rfl, show 4 - 1 = 3 from rfl,
    optimalSpectralDeriv_five, optimalSpectralDeriv_four, optimalSpectralDeriv_three]
  norm_num [optimalZetaWeight, Nat.factorial]
  ring

/-! ## Bridge to the zeta-derivative form (T9) -/

/-- **(T9) → (O7).** For `q ≥ 2`, the readout written with `ζ'(-2q-2)`, `ζ'(-2q)` and the
symmetric zeta-derivative sums `S N = 2 ∑_(r ≤ N/2) choose N (2r) ζ'(-2N+2r)` of (T6) equals
`optimalMomentReadout q`. -/
theorem optimalMomentReadout_eq_zetaDeriv {q : ℕ} (hq : 2 ≤ q) :
    (8 : ℂ) ^ q * (-1) ^ (q + 1) / (3 * (q + 1) * q.factorial) *
        (4 * (2 * q + 1) * (2 * q + 3) *
            (-optimalZetaDerivSum (q + 1) + 2 * deriv riemannZeta (-2 * q - 2)) +
          4 * q * (2 * q + 1) * (-optimalZetaDerivSum q + 2 * deriv riemannZeta (-2 * q)) -
          q * (q - 1) * optimalZetaDerivSum (q - 1)) =
      (optimalMomentReadout q : ℂ) := by
  rw [optimalZetaDerivSum_eq (by omega : 1 ≤ q + 1), optimalZetaDerivSum_eq (by omega : 1 ≤ q),
    optimalZetaDerivSum_eq (by omega : 1 ≤ q - 1)]
  have h1 : deriv riemannZeta (-2 * (q : ℂ) - 2) = (optimalZetaWeight (q + 1) : ℂ) := by
    rw [ofReal_optimalZetaWeight (by omega : 1 ≤ q + 1)]
    congr 1
    push_cast
    ring
  rw [h1, ← ofReal_optimalZetaWeight (by omega : 1 ≤ q), optimalMomentReadout]
  push_cast
  ring

/-- **(T11) → (O6).** The `q = 1` boundary form in zeta-derivative coordinates. -/
theorem optimalMomentReadout_boundary_one_eq_zetaDeriv :
    (4 / 3 : ℂ) * (60 * (-optimalZetaDerivSum 2 + 2 * deriv riemannZeta (-4)) +
        12 * (-optimalZetaDerivSum 1 + 2 * deriv riemannZeta (-2)) - 1) =
      ((40 * (riemannZeta 3).re / π ^ 2 - 4 / 3 : ℝ) : ℂ) := by
  rw [optimalZetaDerivSum_eq (by norm_num : 1 ≤ 2), optimalZetaDerivSum_eq le_rfl]
  have h2 : deriv riemannZeta (-4) = (optimalZetaWeight 2 : ℂ) := by
    rw [ofReal_optimalZetaWeight (by norm_num : 1 ≤ 2)]
    norm_num
  have h1 : deriv riemannZeta (-2) = (optimalZetaWeight 1 : ℂ) := by
    rw [ofReal_optimalZetaWeight le_rfl]
    norm_num
  rw [h2, h1, ← optimalMomentReadout_boundary_one]
  push_cast
  ring

end BrownianAffine
