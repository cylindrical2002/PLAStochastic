import PLAStochastic.Index.GEP.StrongApprox.Endgame.FinalNumerics

/-! # Exact arithmetic for the fourth-power dyadic partition -/

namespace PGM

/-- The leaf length and leaf count multiply to the selected horizon. -/
theorem sa_pow_sixteen_partition (k : ℕ) : 2 ^ (3 * k) * 2 ^ k = 16 ^ k := by
  rw [← pow_add]
  have he : 3 * k + k = 4 * k := by omega
  rw [he, pow_mul]
  norm_num

/-- The inverse smoothing scale is the eighth power of the bottom block length. -/
theorem sa_pow_sixteen_square (k : ℕ) :
    (((16 ^ k : ℕ) : ℝ) ^ 2) = (2 ^ k : ℝ) ^ 8 := by
  push_cast
  rw [← pow_mul, ← pow_mul]
  have he : (16 : ℝ) = 2 ^ 4 := by norm_num
  rw [he, ← pow_mul]
  congr 1
  omega

/-- The bottom block is exactly the lower endpoint of the analytic window. -/
theorem sa_pow_sixteen_window (k : ℕ) :
    Real.exp (Real.log (16 ^ k : ℕ) / 4) = (2 ^ k : ℝ) := by
  rw [← sa_pow_sixteen_quarter]
  rw [Real.rpow_def_of_pos (by positivity)]
  congr 1
  ring

/-- The number of tree generations is bounded by a fixed multiple of the logarithm. -/
theorem sa_pow_sixteen_depth (k : ℕ) (hH : 1 ≤ Real.log (16 ^ k : ℕ)) :
    ((3 * k + 1 : ℕ) : ℝ) ≤ (3 / Real.log 16 + 1) * Real.log (16 ^ k : ℕ) := by
  have hl : 0 < Real.log 16 := Real.log_pos (by norm_num)
  have he : Real.log (16 ^ k : ℕ) = (k : ℝ) * Real.log 16 := by
    push_cast
    rw [Real.log_pow]
  rw [he] at hH ⊢
  push_cast
  have hh : (3 / Real.log 16 + 1) * ((k : ℝ) * Real.log 16) =
      3 * k + k * Real.log 16 := by field_simp
  rw [hh]
  linarith

/-- The tree union bound fits inside the leaf failure budget. -/
theorem sa_tree_failure_budget {N L : ℝ} (hN : 3 ≤ N) (hL : L ≤ N) :
    3 * L * Real.exp (-(5 * Real.log N)) ≤ N ^ (-(3 : ℝ)) := by
  have hN0 : 0 < N := by linarith
  have he : Real.exp (-(5 * Real.log N)) = N ^ (-(5 : ℝ)) := by
    rw [Real.rpow_def_of_pos hN0]
    congr 1
    ring
  rw [he]
  calc
    _ ≤ 3 * N * N ^ (-(5 : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ ≤ N * N * N ^ (-(5 : ℝ)) :=
      mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
    _ = _ := by
      have hx : N * N = N ^ (2 : ℝ) := by norm_num [pow_two]
      rw [hx, ← Real.rpow_add hN0]
      norm_num

/-- Both smoothing corrections have bounded total contribution. -/
theorem sa_smoothing_scale_bounds {N : ℝ} (hN : 1 ≤ N) :
    0 < 1 / N ^ 2 ∧ 1 / N ^ 2 ≤ 1 ∧
      (1 / N ^ 2) * N ≤ 1 ∧ (1 / N ^ 2) ^ 2 * N ≤ 1 := by
  have hN0 : 0 < N := by linarith
  have hNs : 1 ≤ N ^ 2 := by nlinarith
  have hs : 0 < 1 / N ^ 2 := by positivity
  have hs1 : 1 / N ^ 2 ≤ 1 := (div_le_one (by positivity)).2 hNs
  have hn : (1 / N ^ 2) * N ≤ 1 := by
    have he : (1 / N ^ 2) * N = 1 / N := by field_simp
    rw [he]
    exact (div_le_one hN0).2 hN
  refine ⟨hs, hs1, hn, ?_⟩
  have hsq : (1 / N ^ 2) ^ 2 ≤ 1 / N ^ 2 := by nlinarith
  exact (mul_le_mul_of_nonneg_right hsq hN0.le).trans hn

end PGM
