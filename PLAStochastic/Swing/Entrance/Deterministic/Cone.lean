import PLAStochastic.Swing.Entrance.Defs

/-!
# The running cone of an anchored path

Elementary facts about the running endpoints `a_n = max_{1 ≤ i ≤ n} (y_i - E)/i` and
`b_n = min_{1 ≤ i ≤ n} (y_i + E)/i` of `Defs.lean` for an anchored path `y` with `y 0 = 0`:
the sample bounds, attainment, monotonicity in `n`, the identification of `[a_n, b_n]` with the
slopes whose anchored line stays within `E` of `y_1, …, y_n`, the native feasibility test in the
same form, and the bookkeeping of which endpoint is refreshed at an index.
-/

namespace SwingRepair

noncomputable section

variable {y : ℕ → ℝ} {E : ℝ}

/-- The constraint `|y_i - m i| ≤ E` of a positive index as an interval of slopes. -/
theorem abs_sub_mul_le_iff_bounds {i : ℕ} (hi : 1 ≤ i) {m : ℝ} :
    |y i - m * i| ≤ E ↔ (y i - E) / i ≤ m ∧ m ≤ (y i + E) / i := by
  have hi' : (0 : ℝ) < i := by exact_mod_cast hi
  rw [abs_le, div_le_iff₀ hi', le_div_iff₀ hi']
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

theorem entranceLower_eq (hy0 : y 0 = 0) {n : ℕ} (hn : 1 ≤ n) :
    entranceLower y E n =
      (Finset.Icc 1 n).sup' (Finset.nonempty_Icc.mpr hn) (fun i => (y i - E) / i) := by
  rw [entranceLower, dif_pos (Finset.nonempty_Icc.mpr hn)]
  simp only [nativeConeLower, slopeLower, hy0, sub_zero]

theorem entranceUpper_eq (hy0 : y 0 = 0) {n : ℕ} (hn : 1 ≤ n) :
    entranceUpper y E n =
      (Finset.Icc 1 n).inf' (Finset.nonempty_Icc.mpr hn) (fun i => (y i + E) / i) := by
  rw [entranceUpper, dif_pos (Finset.nonempty_Icc.mpr hn)]
  simp only [nativeConeUpper, slopeUpper, hy0, sub_zero]

theorem sample_le_entranceLower (hy0 : y 0 = 0) {n i : ℕ} (hi : i ∈ Finset.Icc 1 n) :
    (y i - E) / i ≤ entranceLower y E n := by
  have hi' := Finset.mem_Icc.mp hi
  rw [entranceLower_eq hy0 (hi'.1.trans hi'.2)]
  exact Finset.le_sup' (fun i => (y i - E) / (i : ℝ)) hi

theorem entranceUpper_le_sample (hy0 : y 0 = 0) {n i : ℕ} (hi : i ∈ Finset.Icc 1 n) :
    entranceUpper y E n ≤ (y i + E) / i := by
  have hi' := Finset.mem_Icc.mp hi
  rw [entranceUpper_eq hy0 (hi'.1.trans hi'.2)]
  exact Finset.inf'_le (fun i => (y i + E) / (i : ℝ)) hi

theorem exists_entranceLower_eq_anchored (hy0 : y 0 = 0) {n : ℕ} (hn : 1 ≤ n) :
    ∃ i ∈ Finset.Icc 1 n, entranceLower y E n = (y i - E) / i := by
  rw [entranceLower_eq hy0 hn]
  exact Finset.exists_mem_eq_sup' _ _

theorem exists_entranceUpper_eq_anchored (hy0 : y 0 = 0) {n : ℕ} (hn : 1 ≤ n) :
    ∃ i ∈ Finset.Icc 1 n, entranceUpper y E n = (y i + E) / i := by
  rw [entranceUpper_eq hy0 hn]
  exact Finset.exists_mem_eq_inf' _ _

theorem entranceLower_le_iff_anchored (hy0 : y 0 = 0) {n : ℕ} (hn : 1 ≤ n) {m : ℝ} :
    entranceLower y E n ≤ m ↔ ∀ i ∈ Finset.Icc 1 n, (y i - E) / i ≤ m := by
  rw [entranceLower_eq hy0 hn]
  exact Finset.sup'_le_iff _ _

theorem le_entranceUpper_iff_anchored (hy0 : y 0 = 0) {n : ℕ} (hn : 1 ≤ n) {m : ℝ} :
    m ≤ entranceUpper y E n ↔ ∀ i ∈ Finset.Icc 1 n, m ≤ (y i + E) / i := by
  rw [entranceUpper_eq hy0 hn]
  exact Finset.le_inf'_iff _ _

theorem entranceLower_mono (hy0 : y 0 = 0) {k n : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    entranceLower y E k ≤ entranceLower y E n := by
  rw [entranceLower_le_iff_anchored hy0 hk]
  intro i hi
  have hi' := Finset.mem_Icc.mp hi
  exact sample_le_entranceLower hy0 (Finset.mem_Icc.mpr ⟨hi'.1, hi'.2.trans hkn⟩)

theorem entranceUpper_anti (hy0 : y 0 = 0) {k n : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    entranceUpper y E n ≤ entranceUpper y E k := by
  rw [le_entranceUpper_iff_anchored hy0 hk]
  intro i hi
  have hi' := Finset.mem_Icc.mp hi
  exact entranceUpper_le_sample hy0 (Finset.mem_Icc.mpr ⟨hi'.1, hi'.2.trans hkn⟩)

/-- `[a_n, b_n]` is exactly the set of slopes meeting the `n` sample constraints. -/
theorem mem_entranceCone_iff (hy0 : y 0 = 0) {n : ℕ} (hn : 1 ≤ n) {m : ℝ} :
    (entranceLower y E n ≤ m ∧ m ≤ entranceUpper y E n) ↔
      ∀ i ∈ Finset.Icc 1 n, |y i - m * i| ≤ E := by
  rw [entranceLower_le_iff_anchored hy0 hn, le_entranceUpper_iff_anchored hy0 hn]
  constructor
  · rintro ⟨h₁, h₂⟩ i hi
    exact (abs_sub_mul_le_iff_bounds (Finset.mem_Icc.mp hi).1).mpr ⟨h₁ i hi, h₂ i hi⟩
  · intro h
    exact ⟨fun i hi => ((abs_sub_mul_le_iff_bounds (Finset.mem_Icc.mp hi).1).mp (h i hi)).1,
      fun i hi => ((abs_sub_mul_le_iff_bounds (Finset.mem_Icc.mp hi).1).mp (h i hi)).2⟩

/-- The native feasibility test of the first prefix in path form. -/
theorem nativePrefixFeasible_iff_path (hy0 : y 0 = 0) (j : ℕ) :
    nativePrefixFeasible (fun i => (i : ℝ)) y E 0 j (y 0) ↔
      ∃ m, ∀ i ∈ Finset.Icc 1 j, |y i - m * i| ≤ E := by
  simp only [nativePrefixFeasible, feasibleSlope, hy0, Nat.cast_zero, sub_zero, zero_add]

theorem entranceWidth_one_anchored (hy0 : y 0 = 0) : entranceWidth y E 1 = 2 * E := by
  rw [entranceWidth, entranceLower_eq hy0 le_rfl, entranceUpper_eq hy0 le_rfl]
  simp only [Finset.Icc_self, Finset.sup'_singleton, Finset.inf'_singleton, Nat.cast_one,
    div_one, one_mul]
  ring

/-- The rescaled width of a cone whose two endpoints are both the current sample's bounds. -/
theorem width_of_both_refreshed {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * ((y n + E) / n - (y n - E) / n) = 2 * E := by
  have hn' : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact this.ne'
  field_simp
  ring

/-- If the lower endpoint is not attained by the current sample, it is the previous endpoint. -/
theorem entranceLower_eq_prev (hy0 : y 0 = 0) {n : ℕ} (hn : 2 ≤ n)
    (h : entranceLower y E n ≠ (y n - E) / n) :
    entranceLower y E n = entranceLower y E (n - 1) := by
  obtain ⟨i, hi, hia⟩ := exists_entranceLower_eq_anchored (E := E) hy0 (by omega : 1 ≤ n)
  have hin : i ≠ n := by
    rintro rfl
    exact h hia
  have hi' : i ∈ Finset.Icc 1 (n - 1) := by
    have := Finset.mem_Icc.mp hi
    exact Finset.mem_Icc.mpr ⟨this.1, by omega⟩
  apply le_antisymm
  · rw [hia]
    exact sample_le_entranceLower hy0 hi'
  · exact entranceLower_mono hy0 (by omega) (by omega)

/-- If the upper endpoint is not attained by the current sample, it is the previous endpoint. -/
theorem entranceUpper_eq_prev (hy0 : y 0 = 0) {n : ℕ} (hn : 2 ≤ n)
    (h : entranceUpper y E n ≠ (y n + E) / n) :
    entranceUpper y E n = entranceUpper y E (n - 1) := by
  obtain ⟨i, hi, hia⟩ := exists_entranceUpper_eq_anchored (E := E) hy0 (by omega : 1 ≤ n)
  have hin : i ≠ n := by
    rintro rfl
    exact h hia
  have hi' : i ∈ Finset.Icc 1 (n - 1) := by
    have := Finset.mem_Icc.mp hi
    exact Finset.mem_Icc.mpr ⟨this.1, by omega⟩
  apply le_antisymm
  · exact entranceUpper_anti hy0 (by omega) (by omega)
  · rw [hia]
    exact entranceUpper_le_sample hy0 hi'

theorem entranceRefreshesLower_iff (hy0 : y 0 = 0) (n : ℕ) :
    entranceRefreshesLower y E n ↔ entranceLower y E n = (y n - E) / n := by
  simp only [entranceRefreshesLower, slopeLower, hy0, sub_zero]

theorem entranceSide_of_refresh {n : ℕ} (h : entranceRefreshesLower y E n) :
    entranceSide y E n = 1 := by
  classical
  simp only [entranceSide, if_pos h]

theorem entranceSide_of_not_refresh {n : ℕ} (h : ¬ entranceRefreshesLower y E n) :
    entranceSide y E n = -1 := by
  classical
  simp only [entranceSide, if_neg h]

theorem entranceFrozenSlope_of_refresh {n : ℕ} (h : entranceRefreshesLower y E n) :
    entranceFrozenSlope y E n = entranceUpper y E n := by
  classical
  simp only [entranceFrozenSlope, if_pos h]

theorem entranceFrozenSlope_of_not_refresh {n : ℕ} (h : ¬ entranceRefreshesLower y E n) :
    entranceFrozenSlope y E n = entranceLower y E n := by
  classical
  simp only [entranceFrozenSlope, if_neg h]

/-- A sign `±1` preserves the two-sided bound `|x| ≤ E`. -/
theorem sign_mul_bounds {s x : ℝ} (hs : s = 1 ∨ s = -1) (hx : |x| ≤ E) :
    -E ≤ s * x ∧ s * x ≤ E := by
  rcases hs with rfl | rfl
  · simpa only [one_mul] using abs_le.mp hx
  · have := abs_le.mp hx
    constructor <;> linarith

theorem abs_le_of_sign_mul_bounds {s x : ℝ} (hs : s = 1 ∨ s = -1)
    (h₁ : -E ≤ s * x) (h₂ : s * x ≤ E) : |x| ≤ E := by
  rcases hs with rfl | rfl
  · rw [abs_le]
    constructor <;> linarith
  · rw [abs_le]
    constructor <;> linarith

end

end SwingRepair
