import PLAStochastic.Swing.Entrance.Deterministic.Width
import PLAStochastic.Swing.Entrance.Deterministic.Bridge

/-!
# The SSE selection rule and the margin formula along the path (E21)–(E22), (E26)–(E27)

With `N = n + T - 1` the last accepted index, the native slope `m_N` is the least-squares
slope `LS = ∑ i y_i / ∑ i²` clipped to `[a_N, b_N]`, and
`s (LS - β) = ∑_{i ≤ N} i (s y_i - s β i) / ∑_{i ≤ N} i²`.  Since `β` is the frozen endpoint, a
nonnegative area sum selects `β`, and an area sum at most `-(W / N) ∑ i²` with
`W = N (b_N - a_N)` selects the active endpoint `β - s W / N` (E22).

At the first rejected index `J = N + 1 = n + T` the reflected residual of the frozen line is
`E + O` with `O` the local overshoot, so `s (y_J - N m_N) = E + O + s β + N s (β - m_N)` with
`s (β - m_N) ≥ 0` (E26).  When `s β > -E` the residual is positive and the margin is
`E - |y_J - N m_N| = -O - s β - N s (β - m_N)` (E27); at an endpoint the last term is `0` for
the frozen endpoint and `W` for the active one.
-/

namespace SwingRepair

noncomputable section

variable {y : ℕ → ℝ} {E : ℝ}

theorem nativeClippedSlope_eq_upper_of_le {L U C : ℝ} (hLU : L ≤ U) (hC : U ≤ C) :
    nativeClippedSlope L U C = U := by
  unfold nativeClippedSlope
  rw [min_eq_right hC, max_eq_right hLU]

theorem sum_Icc_sq_pos {N : ℕ} (hN : 1 ≤ N) : 0 < ∑ i ∈ Finset.Icc 1 N, (i : ℝ) ^ 2 := by
  apply Finset.sum_pos
  · intro i hi
    have : (0 : ℝ) < i := by exact_mod_cast (Finset.mem_Icc.mp hi).1
    positivity
  · exact Finset.nonempty_Icc.mpr hN

/-- (E21): the signed least-squares displacement from `β` is the signed area over `∑ i²`. -/
theorem sign_mul_leastSquares_sub (y : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) (s β : ℝ) :
    s * ((∑ i ∈ Finset.Icc 1 N, (i : ℝ) * y i) / (∑ i ∈ Finset.Icc 1 N, (i : ℝ) ^ 2) - β) =
      (∑ i ∈ Finset.Icc 1 N, (i : ℝ) * (s * y i - s * β * i)) /
        ∑ i ∈ Finset.Icc 1 N, (i : ℝ) ^ 2 := by
  have hS := sum_Icc_sq_pos hN
  have hsum : ∑ i ∈ Finset.Icc 1 N, (i : ℝ) * (s * y i - s * β * i) =
      s * ∑ i ∈ Finset.Icc 1 N, (i : ℝ) * y i - s * β * ∑ i ∈ Finset.Icc 1 N, (i : ℝ) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum]
  field_simp

namespace EntranceLocalEvent

variable {n T : ℕ}

/-- The native slope of the final prefix lies in the final cone. -/
theorem slope_mem_cone (h : EntranceLocalEvent y E n T) :
    entranceLower y E (n + T - 1) ≤ entrancePathSlope y E (n + T - 1) ∧
      entrancePathSlope y E (n + T - 1) ≤ entranceUpper y E (n + T - 1) := by
  have hc := h.frozen_mem_cone
  rw [entrancePathSlope_eq h.anchor h.one_le_last]
  exact nativeClippedSlope_mem (hc.1.trans hc.2)

/-- `s (β - m_N) ≥ 0`: the native slope lies on the active side of the frozen endpoint. -/
theorem sign_mul_frozen_sub_slope_nonneg (h : EntranceLocalEvent y E n T) :
    0 ≤ entranceSide y E n * (entranceFrozenSlope y E n - entrancePathSlope y E (n + T - 1)) := by
  have hm := h.slope_mem_cone
  rcases entranceSide_eq_one_or (y := y) (E := E) n with hs | hs
  · rw [hs, ← h.upper_eq_frozen hs]
    linarith [hm.2]
  · rw [hs, ← h.lower_eq_frozen hs]
    linarith [hm.1]

/-- (E22), frozen branch: a nonnegative signed area selects the frozen endpoint. -/
theorem slope_eq_frozen_of_area_nonneg (h : EntranceLocalEvent y E n T)
    (hA : 0 ≤ ∑ i ∈ Finset.Icc 1 (n + T - 1),
      (i : ℝ) * (entranceSide y E n * y i - entranceSide y E n * entranceFrozenSlope y E n * i)) :
    entrancePathSlope y E (n + T - 1) = entranceFrozenSlope y E n := by
  have hN := h.one_le_last
  have hc := h.frozen_mem_cone
  have hid := sign_mul_leastSquares_sub y hN (entranceSide y E n) (entranceFrozenSlope y E n)
  have hpos : 0 ≤ entranceSide y E n * ((∑ i ∈ Finset.Icc 1 (n + T - 1), (i : ℝ) * y i) /
      (∑ i ∈ Finset.Icc 1 (n + T - 1), (i : ℝ) ^ 2) - entranceFrozenSlope y E n) := by
    rw [hid]
    exact div_nonneg hA (sum_Icc_sq_pos hN).le
  rw [entrancePathSlope_eq h.anchor hN]
  rcases entranceSide_eq_one_or (y := y) (E := E) n with hs | hs
  · rw [hs, one_mul] at hpos
    rw [← h.upper_eq_frozen hs] at hpos ⊢
    rw [h.upper_eq_frozen hs] at hc
    exact nativeClippedSlope_eq_upper_of_le (by rw [h.upper_eq_frozen hs]; exact hc.1)
      (by linarith)
  · rw [hs] at hpos
    rw [← h.lower_eq_frozen hs] at hpos ⊢
    exact nativeClippedSlope_eq_lower_of_le (by linarith)

/-- (E22), active branch: a signed area at most `-(W / N) ∑ i²` selects the active endpoint
`β - s W / N`, with `W = N (b_N - a_N)`. -/
theorem slope_eq_active_of_area_le (h : EntranceLocalEvent y E n T)
    (hA : ∑ i ∈ Finset.Icc 1 (n + T - 1),
      (i : ℝ) * (entranceSide y E n * y i - entranceSide y E n * entranceFrozenSlope y E n * i) ≤
        -(entranceWidth y E (n + T - 1) / ((n + T - 1 : ℕ) : ℝ)) *
          ∑ i ∈ Finset.Icc 1 (n + T - 1), (i : ℝ) ^ 2) :
    entrancePathSlope y E (n + T - 1) = entranceFrozenSlope y E n -
      entranceSide y E n * (entranceWidth y E (n + T - 1) / ((n + T - 1 : ℕ) : ℝ)) := by
  have hN := h.one_le_last
  have hc := h.frozen_mem_cone
  have hS := sum_Icc_sq_pos hN
  have hNpos : (0 : ℝ) < ((n + T - 1 : ℕ) : ℝ) := by exact_mod_cast hN
  have hid := sign_mul_leastSquares_sub y hN (entranceSide y E n) (entranceFrozenSlope y E n)
  have hgap : entranceWidth y E (n + T - 1) / ((n + T - 1 : ℕ) : ℝ) =
      entranceUpper y E (n + T - 1) - entranceLower y E (n + T - 1) := by
    rw [entranceWidth]
    field_simp
  have hle : entranceSide y E n * ((∑ i ∈ Finset.Icc 1 (n + T - 1), (i : ℝ) * y i) /
      (∑ i ∈ Finset.Icc 1 (n + T - 1), (i : ℝ) ^ 2) - entranceFrozenSlope y E n) ≤
        -(entranceUpper y E (n + T - 1) - entranceLower y E (n + T - 1)) := by
    rw [hid, ← hgap, div_le_iff₀ hS]
    exact hA
  rw [entrancePathSlope_eq h.anchor hN, hgap]
  rcases entranceSide_eq_one_or (y := y) (E := E) n with hs | hs
  · have hb := h.upper_eq_frozen hs
    rw [hs, one_mul] at hle
    rw [hs, one_mul]
    rw [← hb] at hle ⊢
    rw [show entranceUpper y E (n + T - 1) -
        (entranceUpper y E (n + T - 1) - entranceLower y E (n + T - 1)) =
          entranceLower y E (n + T - 1) by ring]
    exact nativeClippedSlope_eq_lower_of_le (by linarith)
  · rw [hs] at hle ⊢
    rw [← h.lower_eq_frozen hs] at hle ⊢
    rw [show entranceLower y E (n + T - 1) -
        -1 * (entranceUpper y E (n + T - 1) - entranceLower y E (n + T - 1)) =
          entranceUpper y E (n + T - 1) by ring]
    exact nativeClippedSlope_eq_upper_of_le (by linarith [hc.1, hc.2]) (by linarith)

/-- (E21), window part: on the accepted prefix `|y_i - β i| ≤ E`, so the area terms added
between the cut `n` and `N` are at most `(N - n) N E` in absolute value. -/
theorem area_sub_cut_area_le (h : EntranceLocalEvent y E n T) :
    |∑ i ∈ Finset.Icc 1 (n + T - 1), (i : ℝ) *
        (entranceSide y E n * y i - entranceSide y E n * entranceFrozenSlope y E n * i) -
      ∑ i ∈ Finset.Icc 1 n, (i : ℝ) *
        (entranceSide y E n * y i - entranceSide y E n * entranceFrozenSlope y E n * i)| ≤
      (((n + T - 1 : ℕ) : ℝ) - n) * ((n + T - 1 : ℕ) : ℝ) * E := by
  set f : ℕ → ℝ := fun i => (i : ℝ) *
    (entranceSide y E n * y i - entranceSide y E n * entranceFrozenSlope y E n * i) with hf
  have hIcc : ∀ m, Finset.Icc 1 m = Finset.Ioc 0 m := by
    intro m
    ext i
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hIcc, hIcc, ← Finset.sum_Ioc_consecutive f (Nat.zero_le n) h.cut_le_last,
    add_sub_cancel_left]
  have hterm : ∀ i ∈ Finset.Ioc n (n + T - 1), |f i| ≤ ((n + T - 1 : ℕ) : ℝ) * E := by
    intro i hi
    have hi' := Finset.mem_Ioc.mp hi
    have hfe := h.frozen_feasible i (Finset.mem_Icc.mpr ⟨by have := h.facts.two_le; omega, hi'.2⟩)
    have hs : |entranceSide y E n| = 1 := by
      rcases entranceSide_eq_one_or (y := y) (E := E) n with hs | hs <;> rw [hs] <;> norm_num
    have hiN : (i : ℝ) ≤ ((n + T - 1 : ℕ) : ℝ) := by exact_mod_cast hi'.2
    have hfi : f i = (i : ℝ) * entranceSide y E n * (y i - entranceFrozenSlope y E n * i) := by
      rw [hf]
      ring
    rw [hfi, abs_mul, abs_mul, hs, mul_one, abs_of_nonneg (Nat.cast_nonneg i)]
    exact mul_le_mul hiN hfe (abs_nonneg _) (Nat.cast_nonneg _)
  calc |∑ i ∈ Finset.Ioc n (n + T - 1), f i|
      ≤ ∑ i ∈ Finset.Ioc n (n + T - 1), |f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ (Finset.Ioc n (n + T - 1)).card • (((n + T - 1 : ℕ) : ℝ) * E) :=
      Finset.sum_le_card_nsmul _ _ _ hterm
    _ = (((n + T - 1 : ℕ) : ℝ) - n) * ((n + T - 1 : ℕ) : ℝ) * E := by
      rw [Nat.card_Ioc, nsmul_eq_mul, Nat.cast_sub h.cut_le_last]
      ring

/-- (E26): the signed rejected residual of the native line. -/
theorem sign_mul_residual (h : EntranceLocalEvent y E n T) :
    entranceSide y E n * (y (n + T - 1 + 1) -
        entrancePathSlope y E (n + T - 1) * ((n + T - 1 : ℕ) : ℝ)) =
      E + entranceOvershoot y E n + entranceSide y E n * entranceFrozenSlope y E n +
        ((n + T - 1 : ℕ) : ℝ) * (entranceSide y E n *
          (entranceFrozenSlope y E n - entrancePathSlope y E (n + T - 1))) := by
  have hO := h.overshoot_eq
  have hJ : n + T - 1 + 1 = n + T := by have := h.one_le_crossing; omega
  have hcast : ((n + T : ℕ) : ℝ) = ((n + T - 1 : ℕ) : ℝ) + 1 := by
    rw [← hJ]
    push_cast
    ring
  rw [hJ]
  rw [hcast] at hO
  linear_combination -hO

/-- (E27): with `s β > -E` the margin is `-O - s β - N s (β - m_N)`. -/
theorem margin_eq (h : EntranceLocalEvent y E n T)
    (hβ : -E < entranceSide y E n * entranceFrozenSlope y E n) :
    E - |y (n + T - 1 + 1) - entrancePathSlope y E (n + T - 1) * ((n + T - 1 : ℕ) : ℝ)| =
      -entranceOvershoot y E n - entranceSide y E n * entranceFrozenSlope y E n -
        ((n + T - 1 : ℕ) : ℝ) * (entranceSide y E n *
          (entranceFrozenSlope y E n - entrancePathSlope y E (n + T - 1))) := by
  have hres := h.sign_mul_residual
  have hO := h.overshoot_pos
  have hnn := mul_nonneg (Nat.cast_nonneg (n + T - 1)) h.sign_mul_frozen_sub_slope_nonneg
  set r := y (n + T - 1 + 1) - entrancePathSlope y E (n + T - 1) * ((n + T - 1 : ℕ) : ℝ)
  have hpos : 0 < entranceSide y E n * r := by linarith
  have habs : |r| = entranceSide y E n * r := by
    rcases entranceSide_eq_one_or (y := y) (E := E) n with hs | hs
    · rw [hs, one_mul] at hpos ⊢
      exact abs_of_pos hpos
    · rw [hs] at hpos ⊢
      rw [abs_of_neg (by linarith)]
      ring
  rw [habs, hres]
  ring

/-- At the active endpoint `m_N = β - s W / N` the last margin term is the width `W`. -/
theorem active_term_eq (h : EntranceLocalEvent y E n T) :
    ((n + T - 1 : ℕ) : ℝ) * (entranceSide y E n * (entranceFrozenSlope y E n -
      (entranceFrozenSlope y E n - entranceSide y E n *
        (entranceWidth y E (n + T - 1) / ((n + T - 1 : ℕ) : ℝ))))) =
      entranceWidth y E (n + T - 1) := by
  have hNpos : (0 : ℝ) < ((n + T - 1 : ℕ) : ℝ) := by exact_mod_cast h.one_le_last
  have hs2 : entranceSide y E n * entranceSide y E n = 1 := by
    rcases entranceSide_eq_one_or (y := y) (E := E) n with hs | hs <;> rw [hs] <;> norm_num
  field_simp
  linear_combination (entranceWidth y E (n + T - 1)) * hs2

end EntranceLocalEvent

end

end SwingRepair
