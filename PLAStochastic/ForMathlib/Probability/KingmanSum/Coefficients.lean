import PLAStochastic.ForMathlib.Probability.KingmanSum.ExponentialSeries
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Exact coefficients for finite exponential holding-time sums

The factorial ratios have a uniform bound and converge to one. Their two
recurrences supply the finite convolution formula and its normalization.
-/

noncomputable section
open Filter Finset
open scoped Topology

namespace BrownianAffine

set_option backward.isDefEq.respectTransparency false

def kingmanRatio (N k : ℕ) : ℝ :=
  if k ≤ N then (N.factorial : ℝ) * ((N + 1).factorial : ℝ) /
    (((N - k).factorial : ℝ) * ((N + k + 1).factorial : ℝ)) else 0

def kingmanCDFCoeff (N n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) * (2 * ((n : ℝ) + 1) + 1) * kingmanRatio N (n + 1)

private theorem factorial_cast_pos (n : ℕ) : (0 : ℝ) < n.factorial := by
  exact_mod_cast Nat.factorial_pos n

private theorem factorial_cast_ne_zero (n : ℕ) : (n.factorial : ℝ) ≠ 0 :=
  (factorial_cast_pos n).ne'

theorem kingmanRatio_zero (N : ℕ) : kingmanRatio N 0 = 1 := by
  simp only [kingmanRatio, Nat.zero_le, if_true, Nat.sub_zero, Nat.add_zero]
  exact div_self (mul_ne_zero (factorial_cast_ne_zero _) (factorial_cast_ne_zero _))

theorem kingmanRatio_eq_zero {N k : ℕ} (hk : N < k) : kingmanRatio N k = 0 :=
  if_neg (not_le.mpr hk)

theorem kingmanRatio_nonneg (N k : ℕ) : 0 ≤ kingmanRatio N k := by
  unfold kingmanRatio
  split_ifs <;> positivity

theorem kingmanRatio_succ_index (N k : ℕ) :
    kingmanRatio N (k + 1) = kingmanRatio N k * ((N : ℝ) - k) / ((N : ℝ) + k + 2) := by
  by_cases hk : k < N
  · have h₁ : N - k = (N - (k + 1)) + 1 := by omega
    have h₂ : N + (k + 1) + 1 = (N + k + 1) + 1 := by omega
    simp only [kingmanRatio, if_pos (Nat.succ_le_of_lt hk), if_pos hk.le]
    rw [h₁, h₂, Nat.factorial_succ (N - (k + 1)), Nat.factorial_succ (N + k + 1)]
    push_cast
    have h₃ : ((N - (k + 1) : ℕ) : ℝ) + 1 = (N : ℝ) - k := by
      rw [Nat.cast_sub (Nat.succ_le_of_lt hk)]
      push_cast
      ring
    rw [h₃]
    have hnk : (0 : ℝ) < (N : ℝ) - k := sub_pos.mpr (by exact_mod_cast hk)
    field_simp [hnk.ne']
    ring
  · by_cases hke : k = N
    · subst k
      rw [kingmanRatio_eq_zero (Nat.lt_succ_self _)]
      simp
    · have hkn : N < k := by omega
      rw [kingmanRatio_eq_zero hkn, kingmanRatio_eq_zero (by omega)]
      simp

theorem kingmanRatio_le_one (N k : ℕ) : kingmanRatio N k ≤ 1 := by
  induction k with
  | zero => rw [kingmanRatio_zero]
  | succ k ih =>
      by_cases hk : k < N
      · rw [kingmanRatio_succ_index]
        have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        have hkR : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        have hnk : (k : ℝ) ≤ N := by exact_mod_cast hk.le
        have hd : 0 < (N : ℝ) + k + 2 := by positivity
        rw [div_le_iff₀ hd, one_mul]
        have hm := mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr hnk)
        nlinarith
      · rw [kingmanRatio_eq_zero (by omega)]
        norm_num

theorem kingmanCDFCoeff_eq_zero {N n : ℕ} (hn : N ≤ n) : kingmanCDFCoeff N n = 0 := by
  rw [kingmanCDFCoeff, kingmanRatio_eq_zero (by omega), mul_zero]

theorem kingmanCDFCoeff_bound (N n : ℕ) :
    ‖kingmanCDFCoeff N n‖ ≤ 2 * ((n : ℝ) + 1) + 1 := by
  simp only [kingmanCDFCoeff, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 2 * ((n : ℝ) + 1) + 1),
    abs_of_nonneg (kingmanRatio_nonneg N (n + 1))]
  nlinarith [mul_le_mul_of_nonneg_left (kingmanRatio_le_one N (n + 1))
    (show 0 ≤ 2 * ((n : ℝ) + 1) + 1 by positivity)]

private theorem tendsto_ratio_factor (k : ℕ) :
    Tendsto (fun N : ℕ => ((N : ℝ) - k) / ((N : ℝ) + k + 2)) atTop (𝓝 1) := by
  have hd : Tendsto (fun N : ℕ => (N : ℝ) + k + 2) atTop atTop :=
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).atTop_add tendsto_const_nhds
  have hi := (tendsto_inv_atTop_zero.comp hd).const_mul (2 * (k : ℝ) + 2)
  have he : (fun N : ℕ => ((N : ℝ) - k) / ((N : ℝ) + k + 2)) =
      (fun N : ℕ => 1 - (2 * (k : ℝ) + 2) * ((N : ℝ) + k + 2)⁻¹) := by
    funext N
    have hn : (N : ℝ) + k + 2 ≠ 0 := by positivity
    field_simp
    ring
  rw [he]
  simpa only [mul_zero, sub_zero, Function.comp_def] using hi.const_sub 1

theorem tendsto_kingmanRatio (k : ℕ) : Tendsto (fun N => kingmanRatio N k) atTop (𝓝 1) := by
  induction k with
  | zero => simpa only [kingmanRatio_zero] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  | succ k ih =>
      simpa only [kingmanRatio_succ_index, mul_div_assoc, mul_one] using ih.mul (tendsto_ratio_factor k)

theorem tendsto_kingmanCDFCoeff (n : ℕ) :
    Tendsto (fun N => kingmanCDFCoeff N n) atTop
      (𝓝 ((-1 : ℝ) ^ (n + 1) * (2 * ((n : ℝ) + 1) + 1))) := by
  simpa only [kingmanCDFCoeff, mul_one] using
    (tendsto_kingmanRatio (n + 1)).const_mul ((-1 : ℝ) ^ (n + 1) * (2 * ((n : ℝ) + 1) + 1))

private def kingmanTelescope (N k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * (k : ℝ) * ((N : ℝ) + k + 1) / N * kingmanRatio N k

private theorem kingman_weight_telescope {N : ℕ} (hN : 0 < N) (k : ℕ) :
    (-1 : ℝ) ^ k * (2 * (k : ℝ) + 1) * kingmanRatio N k =
      kingmanTelescope N k - kingmanTelescope N (k + 1) := by
  unfold kingmanTelescope
  rw [kingmanRatio_succ_index]
  simp only [Nat.cast_add, Nat.cast_one, pow_succ (-1 : ℝ)]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hd : (N : ℝ) + k + 2 ≠ 0 := by positivity
  field_simp
  ring

theorem kingmanCDFCoeff_sum (N : ℕ) :
    1 + ∑ n ∈ range (N + 1), kingmanCDFCoeff (N + 1) n = 0 := by
  have ht : (∑ k ∈ range (N + 1 + 1),
      (-1 : ℝ) ^ k * (2 * (k : ℝ) + 1) * kingmanRatio (N + 1) k) = 0 := by
    simp_rw [kingman_weight_telescope (Nat.succ_pos N)]
    rw [sum_range_sub']
    simp [kingmanTelescope, kingmanRatio_eq_zero (Nat.lt_succ_self (N + 1))]
  rw [sum_range_succ'] at ht
  simp only [Nat.cast_zero, pow_zero, mul_zero, zero_add, one_mul, kingmanRatio_zero,
    Nat.cast_add, Nat.cast_one] at ht
  simpa only [kingmanCDFCoeff, add_comm] using ht

theorem kingmanRatio_succ_size {N k : ℕ} (hk : k ≤ N) :
    kingmanRatio (N + 1) k = kingmanRatio N k * (((N : ℝ) + 1) * ((N : ℝ) + 2)) /
      (((N : ℝ) + 1 - k) * ((N : ℝ) + k + 2)) := by
  have h₁ : N + 1 - k = (N - k) + 1 := by omega
  have h₂ : N + 1 + k + 1 = (N + k + 1) + 1 := by omega
  simp only [kingmanRatio, if_pos (hk.trans (Nat.le_succ N)), if_pos hk]
  rw [h₁, h₂, Nat.factorial_succ (N + 1), Nat.factorial_succ (N - k),
    Nat.factorial_succ (N + k + 1), Nat.factorial_succ N]
  push_cast
  rw [Nat.cast_sub hk]
  have hkn : (k : ℝ) ≤ N := by exact_mod_cast hk
  have hpos : (N : ℝ) + 1 - k ≠ 0 := by linarith
  have hpos' : (1 : ℝ) + N - k ≠ 0 := by linarith
  field_simp [hpos, hpos']
  ring_nf
  field_simp [hpos']
  ring

/-- The coefficient update when one more exponential holding time is convolved. -/
theorem kingmanCDFCoeff_succ {N n : ℕ} (hn : n < N) :
    kingmanCDFCoeff (N + 1) n =
      kingmanCDFCoeff N n * kingmanRate N / (kingmanRate N - kingmanRate n) := by
  rw [kingmanCDFCoeff, kingmanCDFCoeff, kingmanRatio_succ_size (Nat.succ_le_of_lt hn)]
  have hNn : (n : ℝ) < N := by exact_mod_cast hn
  have hdiff : kingmanRate N - kingmanRate n =
      ((N : ℝ) - n) * ((N : ℝ) + n + 3) := by unfold kingmanRate; ring
  have hne : (N : ℝ) - n ≠ 0 := by linarith
  rw [hdiff]
  unfold kingmanRate
  push_cast
  have he : (N : ℝ) + 1 - ((n : ℝ) + 1) = (N : ℝ) - n := by ring
  rw [he]
  field_simp [hne]
  ring

end BrownianAffine
