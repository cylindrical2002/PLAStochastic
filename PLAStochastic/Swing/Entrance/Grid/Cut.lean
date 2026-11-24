import PLAStochastic.Swing.Entrance.Defs

/-!
# The adaptive cut of the entrance cone

Deterministic facts about the running cone endpoints `a_n = max_{i ≤ n} (y_i - y_0 - E)/i`,
`b_n = min_{i ≤ n} (y_i - y_0 + E)/i`, the rescaled width `n (b_n - a_n)` and the adaptive cut
`τ = inf {n ≥ 1 : n (b_n - a_n) ≤ d_E}` of the entrance law, (E5) and (E8):

* the endpoints obey the one-step recursions `a_{n+1} = max a_n ((y_{n+1} - y_0 - E)/(n+1))`
  and `b_{n+1} = min b_n ((y_{n+1} - y_0 + E)/(n+1))`;
* whenever `0 ≤ E` and `d_E < 2E`, a finite cut satisfies `τ ≥ 2`; exactly one endpoint is
  attained by the current sample, and the other one is frozen at its value at `τ - 1`;
* the width before the cut exceeds `d_E`, the cut width `D` is at most `d_E`, and in the
  reflected coordinates `ỹ = s y`, `β̃ = s β` one has `ỹ_τ - β̃ τ = E - D`,
  `D_prev := E - (ỹ_{τ-1} - β̃ (τ - 1)) > d_E` and `D = D_prev + β̃ - (ỹ_τ - ỹ_{τ-1})`.
-/

open Finset

namespace SwingRepair

noncomputable section

variable (y : ℕ → ℝ) (E : ℝ)

/-! ## The running endpoints -/

theorem entranceLower_eq_sup' {n : ℕ} (hn : 1 ≤ n) :
    entranceLower y E n = (Icc 1 n).sup' (nonempty_Icc.mpr hn)
      (fun i => slopeLower (i : ℝ) (y i) 0 (y 0) E) := by
  rw [entranceLower, dif_pos (nonempty_Icc.mpr hn)]
  rfl

theorem entranceUpper_eq_inf' {n : ℕ} (hn : 1 ≤ n) :
    entranceUpper y E n = (Icc 1 n).inf' (nonempty_Icc.mpr hn)
      (fun i => slopeUpper (i : ℝ) (y i) 0 (y 0) E) := by
  rw [entranceUpper, dif_pos (nonempty_Icc.mpr hn)]
  rfl

@[simp] theorem entranceLower_zero : entranceLower y E 0 = 0 := by
  rw [entranceLower, dif_neg (by simp)]

@[simp] theorem entranceUpper_zero : entranceUpper y E 0 = 0 := by
  rw [entranceUpper, dif_neg (by simp)]

theorem slopeLower_le_entranceLower {n i : ℕ} (hi1 : 1 ≤ i) (hin : i ≤ n) :
    slopeLower (i : ℝ) (y i) 0 (y 0) E ≤ entranceLower y E n := by
  rw [entranceLower_eq_sup' y E (hi1.trans hin)]
  exact le_sup' (fun i : ℕ => slopeLower (i : ℝ) (y i) 0 (y 0) E) (mem_Icc.mpr ⟨hi1, hin⟩)

theorem entranceUpper_le_slopeUpper {n i : ℕ} (hi1 : 1 ≤ i) (hin : i ≤ n) :
    entranceUpper y E n ≤ slopeUpper (i : ℝ) (y i) 0 (y 0) E := by
  rw [entranceUpper_eq_inf' y E (hi1.trans hin)]
  exact inf'_le (fun i : ℕ => slopeUpper (i : ℝ) (y i) 0 (y 0) E) (mem_Icc.mpr ⟨hi1, hin⟩)

theorem entranceLower_le_iff {n : ℕ} (hn : 1 ≤ n) {c : ℝ} :
    entranceLower y E n ≤ c ↔ ∀ i, 1 ≤ i → i ≤ n → slopeLower (i : ℝ) (y i) 0 (y 0) E ≤ c := by
  rw [entranceLower_eq_sup' y E hn, sup'_le_iff]
  exact ⟨fun h i hi1 hin => h i (mem_Icc.mpr ⟨hi1, hin⟩),
    fun h i hi => h i (mem_Icc.mp hi).1 (mem_Icc.mp hi).2⟩

theorem le_entranceUpper_iff {n : ℕ} (hn : 1 ≤ n) {c : ℝ} :
    c ≤ entranceUpper y E n ↔ ∀ i, 1 ≤ i → i ≤ n → c ≤ slopeUpper (i : ℝ) (y i) 0 (y 0) E := by
  rw [entranceUpper_eq_inf' y E hn, le_inf'_iff]
  exact ⟨fun h i hi1 hin => h i (mem_Icc.mpr ⟨hi1, hin⟩),
    fun h i hi => h i (mem_Icc.mp hi).1 (mem_Icc.mp hi).2⟩

theorem exists_entranceLower_eq {n : ℕ} (hn : 1 ≤ n) :
    ∃ i, 1 ≤ i ∧ i ≤ n ∧ entranceLower y E n = slopeLower (i : ℝ) (y i) 0 (y 0) E := by
  rw [entranceLower_eq_sup' y E hn]
  obtain ⟨i, hi, he⟩ := exists_mem_eq_sup' (nonempty_Icc.mpr hn)
    (fun i => slopeLower (i : ℝ) (y i) 0 (y 0) E)
  exact ⟨i, (mem_Icc.mp hi).1, (mem_Icc.mp hi).2, he⟩

theorem exists_entranceUpper_eq {n : ℕ} (hn : 1 ≤ n) :
    ∃ i, 1 ≤ i ∧ i ≤ n ∧ entranceUpper y E n = slopeUpper (i : ℝ) (y i) 0 (y 0) E := by
  rw [entranceUpper_eq_inf' y E hn]
  obtain ⟨i, hi, he⟩ := exists_mem_eq_inf' (nonempty_Icc.mpr hn)
    (fun i => slopeUpper (i : ℝ) (y i) 0 (y 0) E)
  exact ⟨i, (mem_Icc.mp hi).1, (mem_Icc.mp hi).2, he⟩

theorem entranceLower_one :
    entranceLower y E 1 = slopeLower ((1 : ℕ) : ℝ) (y 1) 0 (y 0) E := by
  rw [entranceLower_eq_sup' y E le_rfl]
  simp only [Icc_self, sup'_singleton]

theorem entranceUpper_one :
    entranceUpper y E 1 = slopeUpper ((1 : ℕ) : ℝ) (y 1) 0 (y 0) E := by
  rw [entranceUpper_eq_inf' y E le_rfl]
  simp only [Icc_self, inf'_singleton]

/-- `a_{n+1} = max a_n ((y_{n+1} - y_0 - E)/(n+1))`. -/
theorem entranceLower_succ {n : ℕ} (hn : 1 ≤ n) :
    entranceLower y E (n + 1) =
      max (entranceLower y E n) (slopeLower ((n + 1 : ℕ) : ℝ) (y (n + 1)) 0 (y 0) E) := by
  apply le_antisymm
  · apply (entranceLower_le_iff y E (by omega)).mpr
    intro i hi1 hin
    rcases (show i ≤ n ∨ i = n + 1 by omega) with h | h
    · exact le_max_of_le_left (slopeLower_le_entranceLower y E hi1 h)
    · subst h
      exact le_max_right _ _
  · apply max_le
    · apply (entranceLower_le_iff y E hn).mpr
      intro i hi1 hin
      exact slopeLower_le_entranceLower y E hi1 (by omega)
    · exact slopeLower_le_entranceLower y E (by omega) le_rfl

/-- `b_{n+1} = min b_n ((y_{n+1} - y_0 + E)/(n+1))`. -/
theorem entranceUpper_succ {n : ℕ} (hn : 1 ≤ n) :
    entranceUpper y E (n + 1) =
      min (entranceUpper y E n) (slopeUpper ((n + 1 : ℕ) : ℝ) (y (n + 1)) 0 (y 0) E) := by
  apply le_antisymm
  · apply le_min
    · apply (le_entranceUpper_iff y E hn).mpr
      intro i hi1 hin
      exact entranceUpper_le_slopeUpper y E hi1 (by omega)
    · exact entranceUpper_le_slopeUpper y E (by omega) le_rfl
  · apply (le_entranceUpper_iff y E (by omega)).mpr
    intro i hi1 hin
    rcases (show i ≤ n ∨ i = n + 1 by omega) with h | h
    · exact min_le_of_left_le (entranceUpper_le_slopeUpper y E hi1 h)
    · subst h
      exact min_le_right _ _

/-- The two sample bounds of one index are `2E / n` apart. -/
theorem slopeUpper_sub_slopeLower_mul {n : ℕ} (hn : 1 ≤ n) (v v₀ : ℝ) :
    (n : ℝ) * (slopeUpper (n : ℝ) v 0 v₀ E - slopeLower (n : ℝ) v 0 v₀ E) = 2 * E := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  unfold slopeUpper slopeLower
  rw [sub_zero]
  field_simp
  ring

theorem entranceWidth_one : entranceWidth y E 1 = 2 * E := by
  unfold entranceWidth
  rw [entranceLower_one, entranceUpper_one]
  exact slopeUpper_sub_slopeLower_mul E le_rfl (y 1) (y 0)

/-! ## The cut level -/

theorem entranceCutLevel_nonneg {E : ℝ} (hE : 0 ≤ E) : 0 ≤ entranceCutLevel E :=
  Real.rpow_nonneg hE _

theorem entranceCutLevel_le_self {E : ℝ} (hE : 1 ≤ E) : entranceCutLevel E ≤ E := by
  unfold entranceCutLevel
  calc E ^ (1 / 4 : ℝ) ≤ E ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hE (by norm_num)
    _ = E := Real.rpow_one E

theorem entranceCutLevel_lt_two_mul {E : ℝ} (hE : 1 ≤ E) : entranceCutLevel E < 2 * E := by
  have := entranceCutLevel_le_self hE
  linarith

/-! ## The adaptive cut -/

theorem entranceCut_eq_coe_iff {n : ℕ} :
    entranceCut y E = n ↔ 1 ≤ n ∧ entranceWidth y E n ≤ entranceCutLevel E ∧
      ∀ k, 1 ≤ k → k < n → entranceCutLevel E < entranceWidth y E k := by
  classical
  unfold entranceCut
  split_ifs with h
  · rw [ENat.natCast_inj, Nat.find_eq_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2, fun k hk1 hkn => lt_of_not_ge (fun hle => h3 k hkn ⟨hk1, hle⟩)⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, fun k hkn hk => (h3 k hk.1 hkn).not_ge hk.2⟩
  · simp only [ENat.top_ne_natCast, false_iff]
    rintro ⟨h1, h2, _⟩
    exact h ⟨n, h1, h2⟩

theorem entranceCut_eq_top_iff :
    entranceCut y E = ⊤ ↔ ∀ n, 1 ≤ n → entranceCutLevel E < entranceWidth y E n := by
  classical
  unfold entranceCut
  split_ifs with h
  · simp only [ENat.natCast_ne_top, false_iff]
    intro hall
    obtain ⟨n, hn, hle⟩ := h
    exact (hall n hn).not_ge hle
  · simp only [true_iff]
    intro n hn
    by_contra hle
    exact h ⟨n, hn, le_of_not_gt hle⟩

/-- A cut is reached at the first index with width at most `d_E`. -/
theorem entranceCut_le_of_width_le {n : ℕ} (hn : 1 ≤ n)
    (hw : entranceWidth y E n ≤ entranceCutLevel E) : entranceCut y E ≤ n := by
  classical
  unfold entranceCut
  have h : ∃ n : ℕ, 1 ≤ n ∧ entranceWidth y E n ≤ entranceCutLevel E := ⟨n, hn, hw⟩
  rw [dif_pos h]
  exact_mod_cast Nat.find_min' h ⟨hn, hw⟩

variable {y E}

theorem entranceCut_ge_two (hE : entranceCutLevel E < 2 * E) {n : ℕ}
    (hn : entranceCut y E = n) : 2 ≤ n := by
  obtain ⟨h1, h2, _⟩ := (entranceCut_eq_coe_iff y E).mp hn
  by_contra h
  have hn1 : n = 1 := by omega
  subst hn1
  rw [entranceWidth_one] at h2
  linarith

theorem entranceCut_width_le {n : ℕ} (hn : entranceCut y E = n) :
    entranceWidth y E n ≤ entranceCutLevel E :=
  ((entranceCut_eq_coe_iff y E).mp hn).2.1

/-- The width just before the cut exceeds the cut level. -/
theorem entranceCut_width_prev (hE : entranceCutLevel E < 2 * E) {n : ℕ}
    (hn : entranceCut y E = n) : entranceCutLevel E < entranceWidth y E (n - 1) := by
  have h2 := entranceCut_ge_two hE hn
  exact ((entranceCut_eq_coe_iff y E).mp hn).2.2 (n - 1) (by omega) (by omega)

/-- At a finite cut the two endpoints cannot both be attained by the current sample, and they
cannot both be inherited from the previous index. -/
theorem entranceCut_exactly_one (hE0 : 0 ≤ E) (hE : entranceCutLevel E < 2 * E) {n : ℕ}
    (hn : entranceCut y E = n) :
    entranceRefreshesLower y E n ↔
      entranceUpper y E n ≠ slopeUpper (n : ℝ) (y n) 0 (y 0) E := by
  have h2 := entranceCut_ge_two hE hn
  have hle := entranceCut_width_le hn
  have hprev := entranceCut_width_prev hE hn
  have hd := entranceCutLevel_nonneg hE0
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  simp only [Nat.add_sub_cancel] at hprev
  unfold entranceRefreshesLower
  constructor
  · intro hl hu
    have hw : entranceWidth y E (m + 1) = 2 * E := by
      unfold entranceWidth
      rw [hl, hu]
      exact slopeUpper_sub_slopeLower_mul E (by omega) _ _
    linarith
  · intro hu
    by_contra hl
    have hl' : entranceLower y E (m + 1) = entranceLower y E m := by
      rw [entranceLower_succ y E hm] at hl ⊢
      rcases max_choice (entranceLower y E m)
        (slopeLower ((m + 1 : ℕ) : ℝ) (y (m + 1)) 0 (y 0) E) with h | h
      · exact h
      · exact absurd h hl
    have hu' : entranceUpper y E (m + 1) = entranceUpper y E m := by
      rw [entranceUpper_succ y E hm] at hu ⊢
      rcases min_choice (entranceUpper y E m)
        (slopeUpper ((m + 1 : ℕ) : ℝ) (y (m + 1)) 0 (y 0) E) with h | h
      · exact h
      · exact absurd h hu
    unfold entranceWidth at hle hprev
    rw [hl', hu'] at hle
    have hpos : 0 < entranceUpper y E m - entranceLower y E m := by
      by_contra hneg
      have hm0 : (0 : ℝ) ≤ m := by positivity
      nlinarith
    push_cast at hle
    nlinarith

/-- The refreshed endpoint is attained by the current sample and the other one is frozen. -/
theorem entranceCut_refresh (hE0 : 0 ≤ E) (hE : entranceCutLevel E < 2 * E) {n : ℕ}
    (hn : entranceCut y E = n) :
    (entranceRefreshesLower y E n ∧ entranceUpper y E n = entranceUpper y E (n - 1)) ∨
      (¬ entranceRefreshesLower y E n ∧
        entranceUpper y E n = slopeUpper (n : ℝ) (y n) 0 (y 0) E ∧
        entranceLower y E n = entranceLower y E (n - 1)) := by
  have hone := entranceCut_exactly_one hE0 hE hn
  have h2 := entranceCut_ge_two hE hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  simp only [Nat.add_sub_cancel]
  by_cases hl : entranceRefreshesLower y E (m + 1)
  · left
    refine ⟨hl, ?_⟩
    have hu := hone.mp hl
    rw [entranceUpper_succ y E hm] at hu ⊢
    rcases min_choice (entranceUpper y E m)
      (slopeUpper ((m + 1 : ℕ) : ℝ) (y (m + 1)) 0 (y 0) E) with h | h
    · exact h
    · exact absurd h hu
  · right
    have hu : entranceUpper y E (m + 1) = slopeUpper ((m + 1 : ℕ) : ℝ) (y (m + 1)) 0 (y 0) E := by
      by_contra h
      exact hl (hone.mpr h)
    refine ⟨hl, hu, ?_⟩
    unfold entranceRefreshesLower at hl
    rw [entranceLower_succ y E hm] at hl ⊢
    rcases max_choice (entranceLower y E m)
      (slopeLower ((m + 1 : ℕ) : ℝ) (y (m + 1)) 0 (y 0) E) with h | h
    · exact h
    · exact absurd h hl

theorem abs_entranceSide (n : ℕ) : |entranceSide y E n| = 1 := by
  rcases entranceSide_eq_one_or (y := y) (E := E) n with h | h <;> rw [h] <;> norm_num

/-- The frozen endpoint at the cut is the inherited endpoint of index `τ - 1`. -/
theorem entranceCut_frozen_eq (hE0 : 0 ≤ E) (hE : entranceCutLevel E < 2 * E) {n : ℕ}
    (hn : entranceCut y E = n) :
    entranceFrozenSlope y E n = entranceUpper y E (n - 1) ∨
      entranceFrozenSlope y E n = entranceLower y E (n - 1) := by
  classical
  unfold entranceFrozenSlope
  rcases entranceCut_refresh hE0 hE hn with ⟨hl, hu⟩ | ⟨hl, _, hlo⟩
  · left
    rw [if_pos hl, hu]
  · right
    rw [if_neg hl, hlo]

/-! ## The cut width in reflected coordinates -/

/-- `ỹ_τ - β̃ τ = E - D` with `D = τ (b_τ - a_τ)`. -/
theorem entranceCut_reflected_residual (hy0 : y 0 = 0) (hE0 : 0 ≤ E)
    (hE : entranceCutLevel E < 2 * E) {n : ℕ} (hn : entranceCut y E = n) :
    entranceSide y E n * y n - entranceSide y E n * entranceFrozenSlope y E n * n =
      E - entranceWidth y E n := by
  classical
  have h2 := entranceCut_ge_two hE hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  unfold entranceSide entranceFrozenSlope entranceWidth
  rcases entranceCut_refresh hE0 hE hn with ⟨hl, _⟩ | ⟨hl, hu, _⟩
  · rw [if_pos hl, if_pos hl]
    unfold entranceRefreshesLower at hl
    rw [hl]
    unfold slopeLower
    simp only [hy0, sub_zero]
    field_simp
    ring
  · rw [if_neg hl, if_neg hl, hu]
    unfold slopeUpper
    simp only [hy0, sub_zero]
    field_simp
    ring

/-- The reflected width before the cut, `D_prev = E - (ỹ_{τ-1} - β̃ (τ - 1))`, exceeds `d_E`. -/
theorem entranceCut_reflected_prev (hy0 : y 0 = 0) (hE0 : 0 ≤ E)
    (hE : entranceCutLevel E < 2 * E) {n : ℕ} (hn : entranceCut y E = n) :
    entranceCutLevel E < E - (entranceSide y E n * y (n - 1) -
      entranceSide y E n * entranceFrozenSlope y E n * ((n - 1 : ℕ) : ℝ)) := by
  classical
  have h2 := entranceCut_ge_two hE hn
  have hprev := entranceCut_width_prev hE hn
  have hm1 : 1 ≤ n - 1 := by omega
  have hm : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - 1 by omega)
  unfold entranceWidth at hprev
  unfold entranceSide entranceFrozenSlope
  rcases entranceCut_refresh hE0 hE hn with ⟨hl, hu⟩ | ⟨hl, _, hlo⟩
  · rw [if_pos hl, if_pos hl, hu]
    have hlow := slopeLower_le_entranceLower y E hm1 le_rfl
    unfold slopeLower at hlow
    simp only [hy0, sub_zero] at hlow
    rw [div_le_iff₀ hm] at hlow
    nlinarith
  · rw [if_neg hl, if_neg hl, hlo]
    have hup := entranceUpper_le_slopeUpper y E hm1 le_rfl
    unfold slopeUpper at hup
    simp only [hy0, sub_zero] at hup
    rw [le_div_iff₀ hm] at hup
    nlinarith

/-- The one-step identity (E8): `D = D_prev + β̃ - (ỹ_τ - ỹ_{τ-1})`. -/
theorem entranceCut_width_step (hy0 : y 0 = 0) (hE0 : 0 ≤ E)
    (hE : entranceCutLevel E < 2 * E) {n : ℕ} (hn : entranceCut y E = n) :
    entranceWidth y E n =
      (E - (entranceSide y E n * y (n - 1) -
        entranceSide y E n * entranceFrozenSlope y E n * ((n - 1 : ℕ) : ℝ))) +
      entranceSide y E n * entranceFrozenSlope y E n -
      (entranceSide y E n * y n - entranceSide y E n * y (n - 1)) := by
  have h2 := entranceCut_ge_two hE hn
  have hres := entranceCut_reflected_residual hy0 hE0 hE hn
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  rw [hcast]
  linear_combination hres

end

end SwingRepair
