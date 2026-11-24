import PLAStochastic.Swing.Entrance.Deterministic.Native
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # The first-restart margin in the two selection cases

On the truncated good event of the cut with the window conditions `T ≤ q_E` and
`|Q_j| ≤ E/2` (`j ≤ q_E`), the first-restart margin is determined by the local pair `(U, O)`
after the cut and the sign of the reflected grid area `I_E^-` at the cut, up to deterministic
errors that vanish as `E → ∞`:

* if `I_E^- > ε_E` the native SSE selects the frozen endpoint and `|R_{1,E} + O| ≤ M/E`;
* if `I_E^- < -ε'_E` it selects the active endpoint and `|R_{1,E} + U + O| ≤ M/E + w_E`.

Here `ε_E = E^{-5} q_E (M E² + q_E) E` bounds the area added after the cut (E21),
`w_E = q_E d_E / (δ E²)` bounds the difference between the native width and the local
undershoot (G9), and `ε'_E` adds the threshold `(U♮/N) ∑ i²` of the active selection (E22).
-/

open Filter
open scoped Topology

namespace SwingRepair

noncomputable section

variable {Ω : Type*} {X : ℕ → Ω → ℝ} {E : ℝ} {ω : Ω} {n T : ℕ}

/-- The bound `E^{-5} q_E (M E² + q_E) E` on the area added after the cut. -/
def entranceAreaError (E M : ℝ) : ℝ :=
  E⁻¹ ^ 5 * ((entranceWindow E : ℝ) * (M * E ^ 2 + entranceWindow E) * E)

/-- The bound `q_E d_E / (δ E²)` on `U♮ - U`. -/
def entranceWidthError (E δ : ℝ) : ℝ :=
  (entranceWindow E : ℝ) * entranceCutLevel E / (δ * E ^ 2)

/-- The area threshold of the active selection. -/
def entranceActiveThreshold (E δ M : ℝ) : ℝ :=
  entranceAreaError E M + E⁻¹ ^ 5 *
    ((entranceCutLevel E + entranceWidthError E δ) * (M * E ^ 2 + entranceWindow E) ^ 2)

theorem sum_Icc_sq_le_cube (N : ℕ) : ∑ i ∈ Finset.Icc 1 N, (i : ℝ) ^ 2 ≤ (N : ℝ) ^ 3 := by
  calc ∑ i ∈ Finset.Icc 1 N, (i : ℝ) ^ 2 ≤ ∑ _i ∈ Finset.Icc 1 N, (N : ℝ) ^ 2 := by
        refine Finset.sum_le_sum fun i hi => ?_
        have : (i : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hi).2
        have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
        nlinarith
    _ = (N : ℝ) ^ 3 := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        simp only [add_tsub_cancel_right]
        ring

/-- **The two selection cases of the first-restart margin.** -/
theorem nativeFirstMargin_selection_cases {δ M : ℝ} (hE : 1 ≤ E) (hME : M < E) (hδ : 0 < δ)
    (hgood : entranceGood (entrancePath X ω) E δ M) (hcut : entranceCut (entrancePath X ω) E = n)
    (hT : entranceCrossing (entrancePath X ω) E n = T) (hTq : T ≤ entranceWindow E)
    (hQ : ∀ j ≤ entranceWindow E, |entranceLocal (entrancePath X ω) E n j| ≤ E / 2) :
    (entranceAreaError E M < entranceGridArea (entrancePath X ω) E n →
      |nativeFirstMargin X E ω - -entranceOvershoot (entrancePath X ω) E n| ≤ M / E) ∧
    (entranceGridArea (entrancePath X ω) E n < -entranceActiveThreshold E δ M →
      |nativeFirstMargin X E ω -
          -(entranceUndershoot (entrancePath X ω) E n + entranceOvershoot (entrancePath X ω) E n)| ≤
        M / E + entranceWidthError E δ) := by
  set y := entrancePath X ω with hy
  have h := entranceLocalEvent_of_good (entrancePath_zero X ω) hE hgood hcut hT hTq hQ
  have hβ := abs_entranceFrozenSlope_lt_of_good hE hME hgood hcut
  obtain ⟨hn_lo, hn_hi, hEβ, -, hD_hi⟩ := entranceGood_at hgood hcut
  have hEpos : (0 : ℝ) < E := by linarith
  have hE5 : (0 : ℝ) < E⁻¹ ^ 5 := by positivity
  set N := nativeFirstDuration X E ω with hNdef
  set q : ℝ := (entranceWindow E : ℝ) with hq
  have hJ := h.rejected_index
  have hT1 := h.one_le_crossing
  have hNT : (N : ℝ) + 1 = n + T := by exact_mod_cast hJ
  have hTq' : (T : ℝ) ≤ q := by rw [hq]; exact_mod_cast hTq
  have hT1' : (1 : ℝ) ≤ T := by exact_mod_cast hT1
  have hNn : (N : ℝ) - n ≤ q := by linarith
  have hNn0 : (0 : ℝ) ≤ (N : ℝ) - n := by linarith
  have hNle : (N : ℝ) ≤ M * E ^ 2 + q := by linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  -- the side and the frozen slope
  have hs : |entranceSide y E n| = 1 := by
    rcases entranceSide_eq_one_or (y := y) (E := E) n with h1 | h1 <;> rw [h1] <;> norm_num
  have hβM : |entranceFrozenSlope y E n| ≤ M / E := by
    rw [abs_mul, abs_of_pos hEpos] at hEβ
    rw [le_div_iff₀ hEpos]
    linarith
  have hsβ : |entranceSide y E n * entranceFrozenSlope y E n| ≤ M / E := by
    rw [abs_mul, hs, one_mul]; exact hβM
  -- the area added after the cut
  have harea := h.area_sub_gridArea_le
  have harea' : |E⁻¹ ^ 5 * ∑ i ∈ Finset.Icc 1 N, (i : ℝ) *
      (entranceSide y E n * y i - entranceSide y E n * entranceFrozenSlope y E n * i) -
        entranceGridArea y E n| ≤ entranceAreaError E M := by
    refine harea.trans ?_
    unfold entranceAreaError
    gcongr
  -- the native quantities
  have hO := h.entranceRejectOvershoot_eq
  have hside := h.entranceRejectSide_eq
  have hfrozen := h.entranceRejectFrozen_eq
  constructor
  · intro hA
    have hS : 0 ≤ ∑ i ∈ Finset.Icc 1 N, (i : ℝ) *
        (entranceSide y E n * y i - entranceSide y E n * entranceFrozenSlope y E n * i) := by
      have h1 := (abs_le.mp harea').1
      have h2 : 0 < E⁻¹ ^ 5 * ∑ i ∈ Finset.Icc 1 N, (i : ℝ) *
          (entranceSide y E n * y i - entranceSide y E n * entranceFrozenSlope y E n * i) := by
        linarith
      exact (pos_of_mul_pos_right h2 hE5.le).le
    obtain ⟨-, hR⟩ := h.nativeFirstMargin_eq_of_area_nonneg hβ hS
    rw [hR, hO, hside, hfrozen]
    calc |-entranceOvershoot y E n - entranceSide y E n * entranceFrozenSlope y E n -
          -entranceOvershoot y E n| = |entranceSide y E n * entranceFrozenSlope y E n| := by
          rw [show -entranceOvershoot y E n - entranceSide y E n * entranceFrozenSlope y E n -
            -entranceOvershoot y E n = -(entranceSide y E n * entranceFrozenSlope y E n) by ring,
            abs_neg]
      _ ≤ M / E := hsβ
  · intro hA
    -- bounds on the native width
    obtain ⟨hW0, hW1⟩ := h.entranceRejectWidth_sub_undershoot
    obtain ⟨k, hkT, hU, -⟩ := h.undershoot_spec
    have hUle : entranceUndershoot y E n ≤ entranceWidth y E n := by
      obtain ⟨k', hk'T, hU', hmax⟩ := h.undershoot_spec
      have h0 : entranceLocal y E n 0 = 0 := by simp [entranceLocal]
      have := hmax 0 (by omega)
      rw [h0] at this
      linarith
    have hU0 : 0 ≤ entranceUndershoot y E n := by
      rw [hU]
      have := h.local_le_width hkT
      linarith
    have hn_pos : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hn_lo
    have hwidth : ((N : ℝ) - n) * entranceCutLevel E / n ≤ entranceWidthError E δ := by
      unfold entranceWidthError
      have hd := entranceCutLevel_pos hEpos
      rw [div_le_div_iff₀ hn_pos (by positivity)]
      have : ((N : ℝ) - n) * entranceCutLevel E * (δ * E ^ 2) ≤
          q * entranceCutLevel E * (δ * E ^ 2) := by gcongr
      have : q * entranceCutLevel E * (δ * E ^ 2) ≤ q * entranceCutLevel E * n := by gcongr
      linarith
    have hWle : entranceRejectWidth X E ω ≤ entranceCutLevel E + entranceWidthError E δ := by
      linarith
    have hW0' : 0 ≤ entranceRejectWidth X E ω := by linarith
    have hNpos : (1 : ℝ) ≤ N := by
      have := h.facts.two_le
      have : (2 : ℝ) ≤ n := by exact_mod_cast this
      linarith
    have hthr : entranceRejectWidth X E ω / N * ∑ i ∈ Finset.Icc 1 N, (i : ℝ) ^ 2 ≤
        (entranceCutLevel E + entranceWidthError E δ) * (M * E ^ 2 + q) ^ 2 := by
      have hsq := sum_Icc_sq_le_cube N
      have hNp : (0 : ℝ) < N := by linarith
      calc entranceRejectWidth X E ω / N * ∑ i ∈ Finset.Icc 1 N, (i : ℝ) ^ 2
          ≤ entranceRejectWidth X E ω / N * (N : ℝ) ^ 3 := by gcongr
        _ = entranceRejectWidth X E ω * (N : ℝ) ^ 2 := by field_simp
        _ ≤ (entranceCutLevel E + entranceWidthError E δ) * (M * E ^ 2 + q) ^ 2 := by
          gcongr; linarith
    have hS : ∑ i ∈ Finset.Icc 1 N, (i : ℝ) *
        (entranceSide y E n * y i - entranceSide y E n * entranceFrozenSlope y E n * i) ≤
        -(entranceRejectWidth X E ω / N) * ∑ i ∈ Finset.Icc 1 N, (i : ℝ) ^ 2 := by
      have h1 := (abs_le.mp harea').2
      have h2 : E⁻¹ ^ 5 * ∑ i ∈ Finset.Icc 1 N, (i : ℝ) *
          (entranceSide y E n * y i - entranceSide y E n * entranceFrozenSlope y E n * i) ≤
          E⁻¹ ^ 5 * (-(entranceRejectWidth X E ω / N) * ∑ i ∈ Finset.Icc 1 N, (i : ℝ) ^ 2) := by
        have h3 : E⁻¹ ^ 5 * (entranceRejectWidth X E ω / N * ∑ i ∈ Finset.Icc 1 N, (i : ℝ) ^ 2) ≤
            E⁻¹ ^ 5 * ((entranceCutLevel E + entranceWidthError E δ) * (M * E ^ 2 + q) ^ 2) :=
          mul_le_mul_of_nonneg_left hthr hE5.le
        unfold entranceActiveThreshold at hA
        rw [← hq] at hA
        nlinarith
      exact le_of_mul_le_mul_left h2 hE5
    obtain ⟨-, hR⟩ := h.nativeFirstMargin_eq_of_area_le hβ hS
    rw [hR, hO, hside, hfrozen]
    have heq : -entranceOvershoot y E n - entranceSide y E n * entranceFrozenSlope y E n -
        entranceRejectWidth X E ω - -(entranceUndershoot y E n + entranceOvershoot y E n) =
        -(entranceSide y E n * entranceFrozenSlope y E n) -
          (entranceRejectWidth X E ω - entranceUndershoot y E n) := by ring
    rw [heq]
    calc |-(entranceSide y E n * entranceFrozenSlope y E n) -
          (entranceRejectWidth X E ω - entranceUndershoot y E n)|
        ≤ |entranceSide y E n * entranceFrozenSlope y E n| +
            |entranceRejectWidth X E ω - entranceUndershoot y E n| := by
          refine (abs_sub _ _).trans ?_
          rw [abs_neg]
      _ ≤ M / E + entranceWidthError E δ := by
          rw [abs_of_nonneg hW0]
          linarith

/-! ### The errors vanish -/

theorem entranceWindow_le_rpow {E : ℝ} (hE : 0 ≤ E) :
    (entranceWindow E : ℝ) ≤ E ^ (3 / 4 : ℝ) :=
  Nat.floor_le (Real.rpow_nonneg hE _)

theorem entranceWindow_le_self {E : ℝ} (hE : 1 ≤ E) : (entranceWindow E : ℝ) ≤ E :=
  (entranceWindow_le_rpow (by linarith)).trans
    ((Real.rpow_le_rpow_of_exponent_le hE (by norm_num : (3 / 4 : ℝ) ≤ 1)).trans_eq
      (Real.rpow_one E))

theorem entranceWindow_mul_cutLevel_le {E : ℝ} (hE : 0 < E) :
    (entranceWindow E : ℝ) * entranceCutLevel E ≤ E := by
  calc (entranceWindow E : ℝ) * entranceCutLevel E ≤ E ^ (3 / 4 : ℝ) * E ^ (1 / 4 : ℝ) := by
        unfold entranceCutLevel
        gcongr
        exact entranceWindow_le_rpow hE.le
    _ = E := by rw [← Real.rpow_add hE]; norm_num

theorem tendsto_entranceCutLevel_div :
    Tendsto (fun E : ℝ => entranceCutLevel E / E) atTop (𝓝 0) := by
  refine (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 4)).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with E hE
  unfold entranceCutLevel
  rw [eq_div_iff hE.ne', ← Real.rpow_add_one hE.ne']
  norm_num

theorem abs_window_add_le {E M : ℝ} (hE : 1 ≤ E) :
    |M * E ^ 2 + entranceWindow E| ≤ (|M| + 1) * E ^ 2 := by
  have hq := entranceWindow_le_self hE
  have hq0 : (0 : ℝ) ≤ entranceWindow E := Nat.cast_nonneg _
  have hE2 : E ≤ E ^ 2 := by nlinarith
  calc |M * E ^ 2 + entranceWindow E| ≤ |M * E ^ 2| + |(entranceWindow E : ℝ)| := abs_add_le _ _
    _ = |M| * E ^ 2 + entranceWindow E := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ E ^ 2), abs_of_nonneg hq0]
    _ ≤ (|M| + 1) * E ^ 2 := by nlinarith

theorem tendsto_entranceWidthError {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun E => entranceWidthError E δ) atTop (𝓝 0) := by
  have hlim : Tendsto (fun E : ℝ => δ⁻¹ * E⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul δ⁻¹
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_gt_atTop 0] with E hE
    unfold entranceWidthError
    have := entranceCutLevel_pos hE
    positivity
  · filter_upwards [eventually_gt_atTop 0] with E hE
    unfold entranceWidthError
    rw [div_le_iff₀ (by positivity)]
    calc (entranceWindow E : ℝ) * entranceCutLevel E ≤ E := entranceWindow_mul_cutLevel_le hE
      _ = δ⁻¹ * E⁻¹ * (δ * E ^ 2) := by field_simp

theorem tendsto_entranceAreaError (M : ℝ) :
    Tendsto (fun E => entranceAreaError E M) atTop (𝓝 0) := by
  have hlim : Tendsto (fun E : ℝ => (|M| + 1) * E⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul (|M| + 1)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with E hE
  have hEpos : (0 : ℝ) < E := by linarith
  have hq := entranceWindow_le_self hE
  have hq0 : (0 : ℝ) ≤ entranceWindow E := Nat.cast_nonneg _
  have hA := abs_window_add_le (M := M) hE
  unfold entranceAreaError
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < E⁻¹ ^ 5), abs_mul, abs_mul,
    abs_of_nonneg hq0, abs_of_pos hEpos]
  calc E⁻¹ ^ 5 * ((entranceWindow E : ℝ) * |M * E ^ 2 + entranceWindow E| * E)
      ≤ E⁻¹ ^ 5 * (E * ((|M| + 1) * E ^ 2) * E) := by gcongr
    _ = (|M| + 1) * E⁻¹ := by field_simp

theorem tendsto_entranceActiveThreshold {δ : ℝ} (hδ : 0 < δ) (M : ℝ) :
    Tendsto (fun E => entranceActiveThreshold E δ M) atTop (𝓝 0) := by
  have hrest : Tendsto (fun E : ℝ => (|M| + 1) ^ 2 *
      (entranceCutLevel E / E + entranceWidthError E δ * E⁻¹)) atTop (𝓝 0) := by
    have := (tendsto_entranceCutLevel_div.add
      ((tendsto_entranceWidthError hδ).mul tendsto_inv_atTop_zero)).const_mul ((|M| + 1) ^ 2)
    simpa using this
  have hsecond : Tendsto (fun E : ℝ => E⁻¹ ^ 5 *
      ((entranceCutLevel E + entranceWidthError E δ) * (M * E ^ 2 + entranceWindow E) ^ 2))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hrest
    filter_upwards [eventually_ge_atTop 1] with E hE
    have hEpos : (0 : ℝ) < E := by linarith
    have hd := entranceCutLevel_pos hEpos
    have hw : 0 ≤ entranceWidthError E δ := by unfold entranceWidthError; positivity
    have hA := abs_window_add_le (M := M) hE
    have hsq : (M * E ^ 2 + entranceWindow E) ^ 2 ≤ ((|M| + 1) * E ^ 2) ^ 2 := by
      rw [← sq_abs]
      gcongr
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc E⁻¹ ^ 5 * ((entranceCutLevel E + entranceWidthError E δ) *
          (M * E ^ 2 + entranceWindow E) ^ 2)
        ≤ E⁻¹ ^ 5 * ((entranceCutLevel E + entranceWidthError E δ) * ((|M| + 1) * E ^ 2) ^ 2) := by
          gcongr
      _ = (|M| + 1) ^ 2 * (entranceCutLevel E / E + entranceWidthError E δ * E⁻¹) := by
          field_simp
  have := (tendsto_entranceAreaError M).add hsecond
  rw [add_zero] at this
  exact this

end

end SwingRepair
