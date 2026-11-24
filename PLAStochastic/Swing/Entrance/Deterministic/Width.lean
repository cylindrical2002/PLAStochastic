import PLAStochastic.Swing.Entrance.Deterministic.Crossing

/-!
# The final cone width is the late-constraint width (E17)–(E19)

On the local event, with `N = n + T - 1` the last accepted index, the rescaled final width
`N (b_N - a_N)` is the minimum over `1 ≤ i ≤ N` of `(N / i) (E - s (y_i - β i))`, because the
frozen endpoint is unchanged.  The early constraints `i < n` exceed `N d_E / (n - 1)`, whereas
the constraint at `n` is at most `N d_E / n`; so the width is exactly the late-constraint
width `C^late = min_{n ≤ i ≤ N} (N / i) (E - s (y_i - β i))` (E17)–(E18).  For `i = n + k` the
late term is `(N / i) (D - Q_k)`, whence the deterministic form of (E19):
`0 ≤ N (b_N - a_N) - U ≤ (N - n) d_E / n` with `U = D - max_{k < T} Q_k` the local undershoot.
-/

namespace SwingRepair

noncomputable section

variable {y : ℕ → ℝ} {E : ℝ}

/-- The late-constraint width `C^late = min_{n ≤ i ≤ N} (N / i) (E - s (y_i - β i))` of the
constraints from the cut `n` to the last accepted index `N`. -/
def entranceLateWidth (y : ℕ → ℝ) (E : ℝ) (n N : ℕ) : ℝ :=
  if h : (Finset.Icc n N).Nonempty then
    (Finset.Icc n N).inf' h (fun i => (N : ℝ) / i *
      (E - entranceSide y E n * (y i - entranceFrozenSlope y E n * i)))
  else 0

namespace EntranceLocalEvent

variable {n T : ℕ}

/-- Every constraint of the final prefix bounds the final rescaled width. -/
theorem width_le_term (h : EntranceLocalEvent y E n T) :
    ∀ i ∈ Finset.Icc 1 (n + T - 1), entranceWidth y E (n + T - 1) ≤
      ((n + T - 1 : ℕ) : ℝ) / i *
        (E - entranceSide y E n * (y i - entranceFrozenSlope y E n * i)) := by
  intro i hi
  have hi' : (0 : ℝ) < i := by exact_mod_cast (Finset.mem_Icc.mp hi).1
  have hN : (0 : ℝ) ≤ ((n + T - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  rcases entranceSide_eq_one_or (y := y) (E := E) n with hs | hs
  · have hb := h.upper_eq_frozen hs
    have hlo := sample_le_entranceLower (E := E) h.anchor hi
    rw [entranceWidth, hb, hs]
    have : ((n + T - 1 : ℕ) : ℝ) / i * (E - 1 * (y i - entranceFrozenSlope y E n * i)) =
        ((n + T - 1 : ℕ) : ℝ) * (entranceFrozenSlope y E n - (y i - E) / i) := by
      field_simp
      ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (by linarith) hN
  · have ha := h.lower_eq_frozen hs
    have hup := entranceUpper_le_sample (E := E) h.anchor hi
    rw [entranceWidth, ha, hs]
    have : ((n + T - 1 : ℕ) : ℝ) / i * (E - -1 * (y i - entranceFrozenSlope y E n * i)) =
        ((n + T - 1 : ℕ) : ℝ) * ((y i + E) / i - entranceFrozenSlope y E n) := by
      field_simp
      ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (by linarith) hN

/-- The final rescaled width is attained by one constraint. -/
theorem width_eq_term (h : EntranceLocalEvent y E n T) :
    ∃ i ∈ Finset.Icc 1 (n + T - 1), entranceWidth y E (n + T - 1) =
      ((n + T - 1 : ℕ) : ℝ) / i *
        (E - entranceSide y E n * (y i - entranceFrozenSlope y E n * i)) := by
  rcases entranceSide_eq_one_or (y := y) (E := E) n with hs | hs
  · obtain ⟨i, hi, hia⟩ := exists_entranceLower_eq_anchored (E := E) h.anchor h.one_le_last
    have hi' : (0 : ℝ) < i := by exact_mod_cast (Finset.mem_Icc.mp hi).1
    refine ⟨i, hi, ?_⟩
    rw [entranceWidth, h.upper_eq_frozen hs, hia, hs]
    field_simp
    ring
  · obtain ⟨i, hi, hia⟩ := exists_entranceUpper_eq_anchored (E := E) h.anchor h.one_le_last
    have hi' : (0 : ℝ) < i := by exact_mod_cast (Finset.mem_Icc.mp hi).1
    refine ⟨i, hi, ?_⟩
    rw [entranceWidth, h.lower_eq_frozen hs, hia, hs]
    field_simp
    ring

theorem width_nonneg_last (h : EntranceLocalEvent y E n T) :
    0 ≤ entranceWidth y E (n + T - 1) := by
  have hc := h.frozen_mem_cone
  rw [entranceWidth]
  exact mul_nonneg (Nat.cast_nonneg _) (by linarith [hc.1, hc.2])

/-- The late term at `i = n + k` is `(N / i) (D - Q_k)`. -/
theorem term_shift (h : EntranceLocalEvent y E n T) (k : ℕ) :
    E - entranceSide y E n * (y (n + k) - entranceFrozenSlope y E n * ((n + k : ℕ) : ℝ)) =
      entranceWidth y E n - entranceLocal y E n k := by
  have := h.facts.residual_shift k
  linarith

/-- (E17)–(E18): the final rescaled width equals the late-constraint width exactly. -/
theorem width_eq_late (h : EntranceLocalEvent y E n T) :
    entranceWidth y E (n + T - 1) = entranceLateWidth y E n (n + T - 1) := by
  have hne : (Finset.Icc n (n + T - 1)).Nonempty := Finset.nonempty_Icc.mpr h.cut_le_last
  rw [entranceLateWidth, dif_pos hne]
  apply le_antisymm
  · apply Finset.le_inf'
    intro i hi
    have hi' := Finset.mem_Icc.mp hi
    exact h.width_le_term i (Finset.mem_Icc.mpr ⟨le_trans (by have := h.facts.two_le; omega) hi'.1,
      hi'.2⟩)
  · obtain ⟨i, hi, hia⟩ := h.width_eq_term
    by_cases hin : n ≤ i
    · rw [hia]
      exact Finset.inf'_le _ (Finset.mem_Icc.mpr ⟨hin, (Finset.mem_Icc.mp hi).2⟩)
    · exfalso
      have hi1 := Finset.mem_Icc.mp hi
      have hipos : (0 : ℝ) < i := by exact_mod_cast hi1.1
      have hearly := h.facts.early i (Finset.mem_Icc.mpr ⟨hi1.1, by omega⟩)
      have hn := h.width_le_term n (Finset.mem_Icc.mpr ⟨by have := h.facts.two_le; omega,
        h.cut_le_last⟩)
      have hres := h.facts.residual
      have hD := h.facts.width_le
      have hd := h.facts.level_pos
      have hW0 := h.width_nonneg_last
      set N : ℝ := ((n + T - 1 : ℕ) : ℝ) with hNdef
      set W := entranceWidth y E (n + T - 1)
      set g := E - entranceSide y E n * (y i - entranceFrozenSlope y E n * i)
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := h.facts.two_le; omega)
      have hNpos : (0 : ℝ) < N := by
        rw [hNdef]
        exact_mod_cast (show 0 < n + T - 1 by have := h.one_le_last; omega)
      -- `W i = N g` and `W n ≤ N D ≤ N d`
      have h1 : W * i = N * g := by
        rw [hia]
        field_simp
      have h2 : W * n ≤ N * entranceCutLevel E := by
        have : N / n * (E - entranceSide y E n * (y n - entranceFrozenSlope y E n * n)) =
            N / n * entranceWidth y E n := by rw [hres]; ring
        rw [this] at hn
        have h3 : W * n ≤ N * entranceWidth y E n := by
          have := mul_le_mul_of_nonneg_right hn hnpos.le
          rwa [show N / n * entranceWidth y E n * n = N * entranceWidth y E n by
            field_simp] at this
        nlinarith
      -- `d i < (n - 1) g`, hence `N d i < (n - 1) W i`, contradicting `W n ≤ N d`
      have h4 : N * entranceCutLevel E * i < ((n : ℝ) - 1) * (W * i) := by
        rw [h1]
        nlinarith
      nlinarith

/-- The local undershoot is attained by some `k < T`. -/
theorem undershoot_spec (h : EntranceLocalEvent y E n T) :
    ∃ k < T, entranceUndershoot y E n = entranceWidth y E n - entranceLocal y E n k ∧
      ∀ j < T, entranceLocal y E n j ≤ entranceLocal y E n k := by
  have hT := h.one_le_crossing
  have hne : (Finset.range T).Nonempty := Finset.nonempty_range_iff.mpr (by omega)
  obtain ⟨k, hk, hka⟩ := Finset.exists_mem_eq_sup' hne (entranceLocal y E n)
  refine ⟨k, Finset.mem_range.mp hk, ?_, fun j hj => ?_⟩
  · unfold entranceUndershoot
    rw [h.crossing]
    change (if hT : 0 < T then entranceWidth y E n - (Finset.range T).sup'
      (Finset.nonempty_range_iff.mpr hT.ne') (entranceLocal y E n) else 0) = _
    rw [dif_pos (by omega), hka]
  · rw [← hka]
    exact Finset.le_sup' (entranceLocal y E n) (Finset.mem_range.mpr hj)

/-- (E19), lower half: the undershoot does not exceed the final width. -/
theorem undershoot_le_width (h : EntranceLocalEvent y E n T) :
    entranceUndershoot y E n ≤ entranceWidth y E (n + T - 1) := by
  obtain ⟨k, hkT, hU, hmax⟩ := h.undershoot_spec
  rw [h.width_eq_late, entranceLateWidth,
    dif_pos (Finset.nonempty_Icc.mpr h.cut_le_last)]
  apply Finset.le_inf'
  intro i hi
  have hi' := Finset.mem_Icc.mp hi
  obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
  have hjT : j < T := by omega
  rw [h.term_shift j, hU]
  have hQj := hmax j hjT
  have hQD := h.local_le_width hjT
  have hipos : (0 : ℝ) < ((n + j : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < n + j by have := h.facts.two_le; omega)
  have hratio : 1 ≤ ((n + T - 1 : ℕ) : ℝ) / ((n + j : ℕ) : ℝ) := by
    rw [le_div_iff₀ hipos, one_mul]
    exact_mod_cast hi'.2
  have hnn : 0 ≤ entranceWidth y E n - entranceLocal y E n j := by linarith
  calc entranceWidth y E n - entranceLocal y E n k
      ≤ entranceWidth y E n - entranceLocal y E n j := by linarith
    _ = 1 * (entranceWidth y E n - entranceLocal y E n j) := (one_mul _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hratio hnn

/-- (E19), upper half: `N (b_N - a_N) - U ≤ (N - n) d_E / n`. -/
theorem width_sub_undershoot_le (h : EntranceLocalEvent y E n T) :
    entranceWidth y E (n + T - 1) - entranceUndershoot y E n ≤
      (((n + T - 1 : ℕ) : ℝ) - n) * entranceCutLevel E / n := by
  obtain ⟨k, hkT, hU, hmax⟩ := h.undershoot_spec
  have hle := h.width_le_term (n + k) (Finset.mem_Icc.mpr
    ⟨by have := h.facts.two_le; omega, by omega⟩)
  rw [h.term_shift k, ← hU] at hle
  have hU0 : 0 ≤ entranceUndershoot y E n := by
    rw [hU]
    linarith [h.local_le_width hkT]
  have hUD : entranceUndershoot y E n ≤ entranceCutLevel E := by
    rw [hU]
    have := hmax 0 (by have := h.one_le_crossing; omega)
    rw [entranceLocal_zero] at this
    linarith [h.facts.width_le]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := h.facts.two_le; omega)
  have hnk : (n : ℝ) ≤ ((n + k : ℕ) : ℝ) := by exact_mod_cast (show n ≤ n + k by omega)
  have hNn : (n : ℝ) ≤ ((n + T - 1 : ℕ) : ℝ) := by exact_mod_cast h.cut_le_last
  set N : ℝ := ((n + T - 1 : ℕ) : ℝ)
  set U := entranceUndershoot y E n
  have h1 : N / ((n + k : ℕ) : ℝ) * U ≤ N / n * U :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by linarith) hnpos hnk) hU0
  have h2 : N / n * U - U = (N - n) * U / n := by
    field_simp
  have h3 : (N - n) * U / n ≤ (N - n) * entranceCutLevel E / n :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hUD (by linarith)) hnpos.le
  linarith

end EntranceLocalEvent

end

end SwingRepair
