import PLAStochastic.Index.GRE.Exact.WindowArithmetic

/-! # The two jump lattices of the exact Model K height -/

namespace PGM
noncomputable section

/-- The fixed-density coordinate, with the constant in the window absorbed. -/
def kreZ (n : ℕ) (eps : ℝ) : ℝ :=
  Real.logb 2 (Real.log n / (6 * Real.log eps) + 1 / 2)

/-- The deterministic integer selected away from the two jump lattices. -/
def kreExactHeight (z : ℝ) : ℕ :=
  2 * Nat.ceil z + 1 + if (Nat.ceil z : ℝ) - z < Real.logb 2 (3 / 2) then 1 else 0

/-- Separation from both the integer and the shifted integer jump lattice. -/
def KREOutside (z w : ℝ) : Prop :=
  (∀ m : ℤ, w ≤ |z - m|) ∧
    (∀ m : ℤ, w ≤ |z - ((m : ℝ) - Real.logb 2 (3 / 2))|)

private theorem logb_relative {d : ℝ} (hd : |d| ≤ 1 / 2) :
    |Real.logb 2 (1 + d)| ≤ 3 * |d| := by
  have hd1 := neg_abs_le d
  have hd2 := le_abs_self d
  have hp : 0 < 1 + d := by linarith
  have hu : Real.log (1 + d) ≤ |d| := by
    have := Real.log_le_sub_one_of_pos hp
    linarith
  have hl : -(2 * |d|) ≤ Real.log (1 + d) := by
    have h := Real.one_sub_inv_le_log_of_pos hp
    have heq : 1 - (1 + d)⁻¹ = d / (1 + d) := by field_simp; ring
    rw [heq] at h
    have : -(2 * |d|) ≤ d / (1 + d) := by
      rw [le_div_iff₀ hp]
      rcases le_or_gt 0 d with h0 | h0
      · rw [abs_of_nonneg h0]; nlinarith
      · rw [abs_of_neg h0]; nlinarith
    linarith
  have h2 : 2 / 3 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have h2p : 0 < Real.log 2 := by linarith
  have hk := mul_nonneg (abs_nonneg d) (show 0 ≤ Real.log 2 - 2 / 3 by linarith)
  rw [Real.logb, abs_div, abs_of_pos h2p, div_le_iff₀ h2p, abs_le]
  constructor <;> nlinarith [abs_nonneg d]

private theorem separation {q y w : ℝ} (_hq : 0 < q) (hy : 0 < y)
    (hw : 0 < w) (hw1 : w ≤ 1)
    (h : w ≤ |Real.logb 2 q - Real.logb 2 y|) : w * y / 6 ≤ |q - y| := by
  by_contra h'
  have hlt : |q - y| / y < w / 6 := by
    rw [div_lt_iff₀ hy]
    linarith
  let d := (q - y) / y
  have hd : |d| = |q - y| / y := by dsimp [d]; rw [abs_div, abs_of_pos hy]
  have hsmall : |d| ≤ 1 / 2 := by rw [hd]; linarith
  have heq : q = y * (1 + d) := by dsimp [d]; field_simp; ring
  have hp : 0 < 1 + d := by have := neg_abs_le d; linarith
  have hl := logb_relative hsmall
  have hlog : Real.logb 2 q - Real.logb 2 y = Real.logb 2 (1 + d) := by
    rw [heq, Real.logb_mul hy.ne' hp.ne']; ring
  rw [hlog] at h
  rw [hd] at hl
  linarith

/-- Separation in logarithmic coordinates gives linear margins at all
three relevant boundaries in one octave. -/
theorem kre_window_margins {q w : ℝ} (hq : 1 < q) (hw : 0 < w) (hw1 : w ≤ 1)
    (hwin : KREOutside (Real.logb 2 q) w) :
    let P := Nat.ceil (Real.logb 2 q)
    let u := (2 : ℝ) ^ P
    1 ≤ P ∧ u / 2 + w / 16 * u ≤ q ∧ q + w / 16 * u ≤ u ∧
      (q + w / 16 * u ≤ 2 * u / 3 ∨ 2 * u / 3 + w / 16 * u ≤ q) := by
  dsimp only
  let P := Nat.ceil (Real.logb 2 q)
  let u := (2 : ℝ) ^ P
  have hqp : 0 < q := by linarith
  have hz : 0 < Real.logb 2 q := (Real.logb_pos_iff one_lt_two hqp).2 hq
  have hP : 1 ≤ P := Nat.one_le_ceil_iff.mpr hz
  have hu : 0 < u := by dsimp [u]; positivity
  have hlu : Real.logb 2 u = P := by
    dsimp [u]; rw [Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one]
  have hlu2 : Real.logb 2 (u / 2) = (P : ℝ) - 1 := by
    rw [Real.logb_div hu.ne' (by norm_num), hlu, Real.logb_self_eq_one one_lt_two]
  have hlu3 : Real.logb 2 (2 * u / 3) = (P : ℝ) - Real.logb 2 (3 / 2) := by
    rw [show 2 * u / 3 = u / (3 / 2) by ring,
      Real.logb_div hu.ne' (by norm_num), hlu]
  have hqu : q ≤ u := by
    apply (Real.logb_le_logb one_lt_two hqp hu).mp
    rw [hlu]
    exact Nat.le_ceil _
  have huq : u / 2 ≤ q := by
    apply (Real.logb_le_logb one_lt_two (by positivity) hqp).mp
    rw [hlu2]
    have := Nat.ceil_lt_add_one hz.le
    dsimp [P] at *
    linarith
  have huSep := separation hqp hu hw hw1 (by
    rw [hlu]; simpa only [Int.cast_natCast] using hwin.1 (P : ℤ))
  have hlSep := separation hqp (show 0 < u / 2 by positivity) hw hw1 (by
    rw [hlu2]; simpa only [Int.cast_sub, Int.cast_natCast, Int.cast_one] using
      hwin.1 ((P : ℤ) - 1))
  have hmSep := separation hqp (show 0 < 2 * u / 3 by positivity) hw hw1 (by
    rw [hlu3]; simpa only [Int.cast_natCast] using hwin.2 (P : ℤ))
  rw [abs_of_nonpos (sub_nonpos.mpr hqu)] at huSep
  rw [abs_of_nonneg (sub_nonneg.mpr huq)] at hlSep
  have hwu : 0 ≤ w * u := mul_nonneg hw.le hu.le
  refine ⟨hP, by nlinarith, by nlinarith, ?_⟩
  rcases le_or_gt q (2 * u / 3) with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h)] at hmSep
    exact Or.inl (by nlinarith)
  · rw [abs_of_nonneg (sub_nonneg.mpr h.le)] at hmSep
    exact Or.inr (by nlinarith)

/-- The branch in the integer formula is exactly the side of the middle
boundary `2 · 2^P / 3`. -/
theorem kre_exact_branch {q : ℝ} (hq : 0 < q) :
    let P := Nat.ceil (Real.logb 2 q)
    ((P : ℝ) - Real.logb 2 q < Real.logb 2 (3 / 2)) ↔ (2 : ℝ) ^ P * (2 / 3) < q := by
  dsimp only
  have hu : 0 < (2 : ℝ) ^ Nat.ceil (Real.logb 2 q) := by positivity
  have hl : Real.logb 2 ((2 : ℝ) ^ Nat.ceil (Real.logb 2 q) * (2 / 3)) =
      (Nat.ceil (Real.logb 2 q) : ℝ) - Real.logb 2 (3 / 2) := by
    rw [show (2 : ℝ) ^ Nat.ceil (Real.logb 2 q) * (2 / 3) =
      (2 : ℝ) ^ Nat.ceil (Real.logb 2 q) / (3 / 2) by ring,
      Real.logb_div hu.ne' (by norm_num), Real.logb_pow,
      Real.logb_self_eq_one one_lt_two, mul_one]
  rw [← Real.logb_lt_logb_iff one_lt_two (by positivity) hq, hl]
  constructor <;> intro h <;> linarith

end
end PGM
