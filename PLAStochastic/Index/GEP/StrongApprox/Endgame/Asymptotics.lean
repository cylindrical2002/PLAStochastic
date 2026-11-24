import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Elementary asymptotic estimates for the final error and probability budgets -/

namespace PGM

open Filter Topology

/-- Every fixed power of the logarithm, with any fixed coefficient, is eventually
bounded by a positive power of the horizon. -/
theorem sa_eventually_log_pow_le_rpow (C : ℝ) (p : ℕ) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ x : ℝ in atTop, C * (Real.log x) ^ p ≤ x ^ r := by
  have h := ((isLittleO_log_rpow_rpow_atTop (p : ℝ) hr).const_mul_left C).bound
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with x hx hx0
  simp only [Real.rpow_natCast, one_mul, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hx0 r)] at hx
  exact (le_abs_self _).trans hx

/-- An exponential remainder beats every fixed polynomial probability budget. -/
theorem sa_eventually_pow_mul_exp_le_neg_pow (C : ℝ) (p q : ℕ) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, C * x ^ p * Real.exp (-b * x) ≤ x ^ (-(q : ℝ)) := by
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((p + q : ℕ) : ℝ) b hb).const_mul C
  have hsmall : ∀ᶠ x : ℝ in atTop, C * (x ^ ((p + q : ℕ) : ℝ) * Real.exp (-b * x)) ≤ 1 :=
    hlim.eventually (ge_mem_nhds (by norm_num))
  filter_upwards [hsmall, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  rw [Real.rpow_natCast, pow_add] at hx
  rw [Real.rpow_neg hx0.le, Real.rpow_natCast, ← one_div, le_div_iff₀ (pow_pos hx0 q)]
  nlinarith [hx]

/-- The dyadic fourth-power horizons tend to infinity. -/
theorem sa_tendsto_pow_sixteen : Tendsto (fun k : ℕ => ((16 ^ k : ℕ) : ℝ)) atTop atTop := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 16))

/-- A useful error-scale identity at the chosen block partition. -/
theorem sa_pow_sixteen_eighth (k : ℕ) :
    (((16 ^ k : ℕ) : ℝ) ^ ((1 : ℝ) / 8)) = Real.sqrt (2 ^ k : ℝ) := by
  push_cast
  have he : (16 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ 4 := by
    rw [← pow_mul, mul_comm k 4, pow_mul]
    norm_num
  rw [he, ← Real.rpow_natCast ((2 : ℝ) ^ k) 4,
    ← Real.rpow_mul (by positivity), Real.sqrt_eq_rpow]
  norm_num

theorem sa_pow_sixteen_quarter (k : ℕ) :
    (((16 ^ k : ℕ) : ℝ) ^ ((1 : ℝ) / 4)) = (2 ^ k : ℝ) := by
  push_cast
  have he : (16 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ 4 := by
    rw [← pow_mul, mul_comm k 4, pow_mul]
    norm_num
  rw [he, ← Real.rpow_natCast ((2 : ℝ) ^ k) 4, ← Real.rpow_mul (by positivity)]
  norm_num

/-- A single threshold controls the deterministic error and the Gaussian
desmoothing probability on the fourth-power dyadic horizons. -/
theorem sa_eventually_final_scales (w H₀ : ℝ) :
    ∀ᶠ k : ℕ in atTop,
      let N : ℝ := (16 ^ k : ℕ)
      16 ≤ N ∧ H₀ ≤ Real.log N ∧ 1 ≤ Real.log N ∧
        w * Real.log N ≤ (2 ^ k : ℝ) ∧
        (Real.log N) ^ 2 ≤ Real.sqrt (2 ^ k : ℝ) ∧
        8 * N * Real.exp (-(N / 2)) ≤ N ^ (-(3 : ℝ)) := by
  have hlog := Real.tendsto_log_atTop.comp sa_tendsto_pow_sixteen
  have hm := sa_tendsto_pow_sixteen.eventually
    (sa_eventually_log_pow_le_rpow w 1 (show (0 : ℝ) < 1 / 4 by norm_num))
  have he := sa_tendsto_pow_sixteen.eventually
    (sa_eventually_log_pow_le_rpow 1 2 (show (0 : ℝ) < 1 / 8 by norm_num))
  have hn := sa_tendsto_pow_sixteen.eventually
    (sa_eventually_pow_mul_exp_le_neg_pow 8 1 3 (show (0 : ℝ) < 1 / 2 by norm_num))
  filter_upwards [sa_tendsto_pow_sixteen.eventually_ge_atTop 16,
    hlog.eventually_ge_atTop H₀, hlog.eventually_ge_atTop 1, hm, he, hn]
    with k hk hH hH1 hm he hn
  refine ⟨hk, hH, hH1, ?_, ?_, ?_⟩
  · simpa only [pow_one, sa_pow_sixteen_quarter] using hm
  · simpa only [one_mul, sa_pow_sixteen_eighth] using he
  · simpa only [pow_one, neg_div, one_div, neg_mul, ← div_eq_inv_mul, Nat.cast_ofNat] using hn

end PGM
