import PLAStochastic.Swing.Entrance.Deterministic.Cut

/-!
# The first rejection is the crossing of the local process (E13)

On the deterministic local event `EntranceLocalEvent y E n T` (anchored path, `E ≥ 1`, cut `n`
with nonnegative width `D`, crossing time `T` of the local process `Q`, and `Q_j ≥ -E` before
the crossing) the reflected residual of the frozen line is `s (y_{n+j} - β (n+j)) = E - D + Q_j`.
Hence the frozen slope `β` stays feasible up to `n + T - 1`, and no slope is feasible on
`1, …, n + T`: a feasible slope `m` must satisfy `s (β - m) ≥ 0` at the sample attaining the
frozen endpoint, and then violates the constraint at `n + T`, where `Q_T > D`.  So the first
rejected index is `J = n + T`, the frozen endpoint is unchanged up to `N = n + T - 1`, and the
native overshoot `s (y_J - β J) - E` is the local overshoot `Q_T - D`.
-/

namespace SwingRepair

noncomputable section

variable {y : ℕ → ℝ} {E : ℝ}

/-- The deterministic local event after the cut. -/
structure EntranceLocalEvent (y : ℕ → ℝ) (E : ℝ) (n T : ℕ) : Prop where
  anchor : y 0 = 0
  one_le : 1 ≤ E
  cut : entranceCut y E = n
  width_nonneg : 0 ≤ entranceWidth y E n
  crossing : entranceCrossing y E n = T
  local_lower : ∀ j, 1 ≤ j → j < T → -E ≤ entranceLocal y E n j

/-- The defining properties of a finite crossing. -/
theorem entranceCrossing_spec {n T : ℕ} (h : entranceCrossing y E n = T) :
    1 ≤ T ∧ entranceWidth y E n < entranceLocal y E n T ∧
      ∀ j, 1 ≤ j → j < T → entranceLocal y E n j ≤ entranceWidth y E n := by
  classical
  unfold entranceCrossing at h
  split_ifs at h with hex
  · have hn : Nat.find hex = T := by exact_mod_cast h
    subst hn
    refine ⟨(Nat.find_spec hex).1, (Nat.find_spec hex).2, fun k hk hkn => ?_⟩
    have := Nat.find_min hex hkn
    push Not at this
    exact this hk
  · exact absurd h (by simp)

@[simp] theorem entranceLocal_zero (n : ℕ) : entranceLocal y E n 0 = 0 := by
  simp [entranceLocal]

/-- The reflected residual of the frozen line after the cut. -/
theorem EntranceCutFacts.residual_shift {n : ℕ} (hF : EntranceCutFacts y E n) (j : ℕ) :
    entranceSide y E n * (y (n + j) - entranceFrozenSlope y E n * ((n + j : ℕ) : ℝ)) =
      E - entranceWidth y E n + entranceLocal y E n j := by
  have h := hF.residual
  unfold entranceLocal
  push_cast
  linear_combination h

namespace EntranceLocalEvent

variable {n T : ℕ}

theorem facts (h : EntranceLocalEvent y E n T) : EntranceCutFacts y E n :=
  entranceCutFacts_of_cut h.anchor h.one_le h.cut h.width_nonneg

theorem one_le_crossing (h : EntranceLocalEvent y E n T) : 1 ≤ T :=
  (entranceCrossing_spec h.crossing).1

theorem width_lt_local (h : EntranceLocalEvent y E n T) :
    entranceWidth y E n < entranceLocal y E n T :=
  (entranceCrossing_spec h.crossing).2.1

theorem local_le_width (h : EntranceLocalEvent y E n T) {j : ℕ} (hj : j < T) :
    entranceLocal y E n j ≤ entranceWidth y E n := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simpa using h.width_nonneg
  · exact (entranceCrossing_spec h.crossing).2.2 j hj0 hj

theorem width_le (h : EntranceLocalEvent y E n T) : entranceWidth y E n ≤ E :=
  h.facts.width_le.trans h.facts.level_le

/-- The frozen slope is feasible on `1, …, n + T - 1`. -/
theorem frozen_feasible (h : EntranceLocalEvent y E n T) :
    ∀ i ∈ Finset.Icc 1 (n + T - 1), |y i - entranceFrozenSlope y E n * i| ≤ E := by
  intro i hi
  have hi' := Finset.mem_Icc.mp hi
  by_cases hin : i ≤ n
  · exact h.facts.feasible i (Finset.mem_Icc.mpr ⟨hi'.1, hin⟩)
  · obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
    have hres := h.facts.residual_shift k
    have hk1 : 1 ≤ k := by omega
    have hkT : k < T := by omega
    have hlo := h.local_lower k hk1 hkT
    have hhi := h.local_le_width hkT
    have hDE := h.width_le
    have hD0 := h.width_nonneg
    exact abs_le_of_sign_mul_bounds (entranceSide_eq_one_or n) (by linarith) (by linarith)

/-- The cone of `1, …, j` is nonempty exactly when `j < n + T`. -/
theorem feasible_iff (h : EntranceLocalEvent y E n T) (j : ℕ) :
    (∃ m, ∀ i ∈ Finset.Icc 1 j, |y i - m * i| ≤ E) ↔ j < n + T := by
  constructor
  · rintro ⟨m, hm⟩
    by_contra hj
    push Not at hj
    set s := entranceSide y E n with hs
    set β := entranceFrozenSlope y E n with hβ
    have hsign := entranceSide_eq_one_or (y := y) (E := E) n
    rw [← hs] at hsign
    obtain ⟨i, hi, hia⟩ := h.facts.attained
    have hi' := Finset.mem_Icc.mp hi
    have hipos : (0 : ℝ) < i := by exact_mod_cast hi'.1
    have hmi := sign_mul_bounds hsign (hm i (Finset.mem_Icc.mpr ⟨hi'.1, hi'.2.trans (by omega)⟩))
    have hsb : 0 ≤ s * (β - m) := by
      have h1 : 0 ≤ s * (β - m) * i := by linarith [hmi.1]
      by_contra hneg
      push Not at hneg
      nlinarith
    have hJ := hm (n + T) (Finset.mem_Icc.mpr ⟨by have := h.one_le_crossing; omega, hj⟩)
    have hmJ := sign_mul_bounds hsign hJ
    have hres := h.facts.residual_shift T
    rw [← hs, ← hβ] at hres
    have hQ := h.width_lt_local
    have hJpos : (0 : ℝ) ≤ ((n + T : ℕ) : ℝ) := Nat.cast_nonneg _
    have : s * (y (n + T) - m * ((n + T : ℕ) : ℝ)) =
        s * (y (n + T) - β * ((n + T : ℕ) : ℝ)) + s * (β - m) * ((n + T : ℕ) : ℝ) := by ring
    nlinarith [mul_nonneg hsb hJpos]
  · intro hj
    refine ⟨entranceFrozenSlope y E n, fun i hi => h.frozen_feasible i ?_⟩
    have hi' := Finset.mem_Icc.mp hi
    exact Finset.mem_Icc.mpr ⟨hi'.1, by omega⟩

/-- The native feasibility threshold of the first prefix is `n + T`. -/
theorem nativePrefixFeasible_iff (h : EntranceLocalEvent y E n T) (j : ℕ) :
    nativePrefixFeasible (fun i => (i : ℝ)) y E 0 j (y 0) ↔ j < n + T :=
  (nativePrefixFeasible_iff_path h.anchor j).trans (h.feasible_iff j)

theorem cut_le_last (h : EntranceLocalEvent y E n T) : n ≤ n + T - 1 := by
  have := h.one_le_crossing
  omega

theorem one_le_last (h : EntranceLocalEvent y E n T) : 1 ≤ n + T - 1 := by
  have := h.facts.two_le
  have := h.cut_le_last
  omega

/-- On the side `s = 1` the upper endpoint is frozen up to `N = n + T - 1`. -/
theorem upper_eq_frozen (h : EntranceLocalEvent y E n T) (hs : entranceSide y E n = 1) :
    entranceUpper y E (n + T - 1) = entranceFrozenSlope y E n := by
  have hN := h.one_le_last
  apply le_antisymm
  · obtain ⟨i, hi, hia⟩ := h.facts.attained
    rw [hs] at hia
    have hi' := Finset.mem_Icc.mp hi
    have hipos : (0 : ℝ) < i := by exact_mod_cast hi'.1
    have hle := entranceUpper_le_sample (E := E) h.anchor
      (Finset.mem_Icc.mpr ⟨hi'.1, hi'.2.trans h.cut_le_last⟩)
    have : (y i + E) / i = entranceFrozenSlope y E n := by
      rw [div_eq_iff hipos.ne']
      linarith
    linarith
  · rw [le_entranceUpper_iff_anchored h.anchor hN]
    intro i hi
    exact ((abs_sub_mul_le_iff_bounds (Finset.mem_Icc.mp hi).1).mp
      (h.frozen_feasible i hi)).2

/-- On the side `s = -1` the lower endpoint is frozen up to `N = n + T - 1`. -/
theorem lower_eq_frozen (h : EntranceLocalEvent y E n T) (hs : entranceSide y E n = -1) :
    entranceLower y E (n + T - 1) = entranceFrozenSlope y E n := by
  have hN := h.one_le_last
  apply le_antisymm
  · rw [entranceLower_le_iff_anchored h.anchor hN]
    intro i hi
    exact ((abs_sub_mul_le_iff_bounds (Finset.mem_Icc.mp hi).1).mp
      (h.frozen_feasible i hi)).1
  · obtain ⟨i, hi, hia⟩ := h.facts.attained
    rw [hs] at hia
    have hi' := Finset.mem_Icc.mp hi
    have hipos : (0 : ℝ) < i := by exact_mod_cast hi'.1
    have hle := sample_le_entranceLower (E := E) h.anchor
      (Finset.mem_Icc.mpr ⟨hi'.1, hi'.2.trans h.cut_le_last⟩)
    have : (y i - E) / i = entranceFrozenSlope y E n := by
      rw [div_eq_iff hipos.ne']
      linarith
    linarith

/-- The final cone `[a_N, b_N]` contains the frozen slope. -/
theorem frozen_mem_cone (h : EntranceLocalEvent y E n T) :
    entranceLower y E (n + T - 1) ≤ entranceFrozenSlope y E n ∧
      entranceFrozenSlope y E n ≤ entranceUpper y E (n + T - 1) :=
  (mem_entranceCone_iff h.anchor h.one_le_last).mpr h.frozen_feasible

/-- The local overshoot is the native overshoot of the frozen line at `J = n + T`. -/
theorem overshoot_eq (h : EntranceLocalEvent y E n T) :
    entranceOvershoot y E n = entranceSide y E n *
      (y (n + T) - entranceFrozenSlope y E n * ((n + T : ℕ) : ℝ)) - E := by
  have hres := h.facts.residual_shift T
  unfold entranceOvershoot
  rw [h.crossing]
  change entranceLocal y E n T - entranceWidth y E n = _
  linarith

theorem overshoot_pos (h : EntranceLocalEvent y E n T) : 0 < entranceOvershoot y E n := by
  unfold entranceOvershoot
  rw [h.crossing]
  change 0 < entranceLocal y E n T - entranceWidth y E n
  linarith [h.width_lt_local]

end EntranceLocalEvent

end

end SwingRepair
