import PLAStochastic.Index.GEP.StrongApprox.Tree.EndpointProbability

/-! # Elementary block-size and parent-window calculations for the dyadic tree -/

namespace PGM

/-- All intermediate aggregation sizes lie between the leaf and root block sizes. -/
theorem sa_dyadic_block_bounds (m J j : ℕ) (hj : j ≤ J) :
    m ≤ m * 2 ^ j ∧ m * 2 ^ j ≤ m * 2 ^ J := by
  constructor
  · exact Nat.le_mul_of_pos_right m (by positivity)
  · exact Nat.mul_le_mul_left m (Nat.pow_le_pow_right (by norm_num) hj)

/-- The parent of a split has exactly twice the child block size. -/
theorem sa_dyadic_parent_length (m J d : ℕ) (hd : d < J) :
    m * 2 ^ (J - d) = 2 * (m * 2 ^ (J - d - 1)) := by
  have hj : J - d = (J - d - 1) + 1 := by omega
  conv_lhs => rw [hj, pow_succ]
  ring

/-- Converting a bound on the actual parent total to the mean parameter of its conditional density. -/
theorem sa_parent_window_to_split_mean {A H l a : ℝ}
    (hA : 0 ≤ A) (_hH : 0 ≤ H) (hl : 0 < l)
    (ha : |a| ≤ A * Real.sqrt (2 * l * H)) :
    |a / (2 * l)| * Real.sqrt l ≤ A * Real.sqrt H := by
  have hsl : 0 < Real.sqrt l := Real.sqrt_pos.mpr hl
  have hsqrt : Real.sqrt (2 * l * H) ≤ 2 * Real.sqrt l * Real.sqrt H := by
    rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * l), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have htwo : Real.sqrt (2 : ℝ) ≤ 2 := by
      rw [Real.sqrt_le_iff]
      norm_num
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right htwo hsl.le)
      (Real.sqrt_nonneg H)
  rw [abs_div, abs_of_pos (by positivity : 0 < 2 * l)]
  apply (mul_le_mul_iff_left₀ (by positivity : 0 < 2 * l)).mp
  calc
    (|a| / (2 * l) * Real.sqrt l) * (2 * l) = |a| * Real.sqrt l := by field_simp
    _ ≤ (A * (2 * Real.sqrt l * Real.sqrt H)) * Real.sqrt l :=
      mul_le_mul_of_nonneg_right (ha.trans (mul_le_mul_of_nonneg_left hsqrt hA)) hsl.le
    _ = (A * Real.sqrt H * 2) * (Real.sqrt l ^ 2) := by ring
    _ = (A * Real.sqrt H) * (2 * l) := by rw [Real.sq_sqrt hl.le]; ring

end PGM
