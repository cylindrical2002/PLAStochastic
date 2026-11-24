import PLAStochastic.Swing.Entrance.Defs

/-!
# Scales of the cut level and the window

With `d_E = E^{1/4}` (`entranceCutLevel`) and `q_E = ⌊E^{3/4}⌋` (`entranceWindow`):

* `q_E / E → 0`, which makes a drift of size `M/E` invisible on the window and makes the
  Kolmogorov bound `16 q_E / E²` vanish;
* `(d_E + 1) / √q_E → 0`, the ballot rate (it is `O(E^{-1/8})`);
* `d_E → ∞`.
-/

namespace SwingRepair

open Filter Topology

theorem entranceWindow_le {E : ℝ} (hE : 0 ≤ E) : (entranceWindow E : ℝ) ≤ E ^ (3 / 4 : ℝ) :=
  Nat.floor_le (Real.rpow_nonneg hE _)

theorem entranceWindow_ge {E : ℝ} (hE : 1 ≤ E) : E ^ (3 / 4 : ℝ) / 2 ≤ (entranceWindow E : ℝ) := by
  have h1 : 1 ≤ E ^ (3 / 4 : ℝ) := Real.one_le_rpow hE (by norm_num)
  have h2 := Nat.lt_floor_add_one (E ^ (3 / 4 : ℝ))
  have h3 : (1 : ℝ) ≤ entranceWindow E := by
    have : 1 ≤ ⌊E ^ (3 / 4 : ℝ)⌋₊ := Nat.le_floor (by exact_mod_cast h1)
    exact_mod_cast this
  unfold entranceWindow at h3 ⊢
  linarith

theorem entranceWindow_pos {E : ℝ} (hE : 1 ≤ E) : 0 < entranceWindow E := by
  have h := entranceWindow_ge hE
  have h1 : 0 < E ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have : (0 : ℝ) < entranceWindow E := by linarith
  exact_mod_cast this

theorem tendsto_rpow_neg_quarter : Tendsto (fun E : ℝ => E ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) :=
  tendsto_rpow_neg_atTop (by norm_num)

/-- `q_E / E → 0`. -/
theorem tendsto_entranceWindow_div : Tendsto (fun E => (entranceWindow E : ℝ) / E) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds tendsto_rpow_neg_quarter
    ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with E hE
    positivity
  · filter_upwards [eventually_gt_atTop 0] with E hE
    calc (entranceWindow E : ℝ) / E ≤ E ^ (3 / 4 : ℝ) / E :=
          div_le_div_of_nonneg_right (entranceWindow_le hE.le) hE.le
      _ = E ^ (-(1 / 4 : ℝ)) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hE]
        norm_num

/-- The window error of a drift of size `M/E`: `2 (M/E) q_E K + q_E (M/E)² → 0`. -/
theorem tendsto_entranceDriftError (M K : ℝ) :
    Tendsto (fun E => 2 * (M / E) * entranceWindow E * K + entranceWindow E * (M / E) ^ 2)
      atTop (𝓝 0) := by
  have h1 := tendsto_entranceWindow_div
  have h2 := tendsto_inv_atTop_zero (𝕜 := ℝ)
  have h : Tendsto (fun E => 2 * M * K * ((entranceWindow E : ℝ) / E) +
      M ^ 2 * (((entranceWindow E : ℝ) / E) * E⁻¹)) atTop (𝓝 (2 * M * K * 0 + M ^ 2 * (0 * 0))) :=
    (h1.const_mul _).add ((h1.mul h2).const_mul _)
  simp only [mul_zero, add_zero] at h
  refine h.congr' ?_
  filter_upwards with E
  ring

/-- The ballot rate `(d_E + 1) / √q_E → 0`. -/
theorem tendsto_entranceBallotRate :
    Tendsto (fun E => (entranceCutLevel E + 1) * (Real.sqrt (entranceWindow E))⁻¹) atTop (𝓝 0) := by
  have hsq : Tendsto (fun E => (entranceCutLevel E + 1) ^ 2 / (entranceWindow E : ℝ)) atTop
      (𝓝 0) := by
    have h8 : Tendsto (fun E : ℝ => 8 * E ^ (-(1 / 4 : ℝ))) atTop (𝓝 (8 * 0)) :=
      tendsto_rpow_neg_quarter.const_mul 8
    rw [mul_zero] at h8
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h8 ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with E hE
      positivity
    · filter_upwards [eventually_ge_atTop 1] with E hE
      have hE0 : 0 < E := by linarith
      have hd1 : 1 ≤ entranceCutLevel E := Real.one_le_rpow hE (by norm_num)
      have hd2 : entranceCutLevel E ^ 2 = E ^ (1 / 2 : ℝ) := by
        unfold entranceCutLevel
        rw [← Real.rpow_natCast, ← Real.rpow_mul hE0.le]
        norm_num
      have hq := entranceWindow_ge hE
      have hq0 : 0 < E ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hE0 _
      have hnum : (entranceCutLevel E + 1) ^ 2 ≤ 4 * E ^ (1 / 2 : ℝ) := by
        nlinarith
      calc (entranceCutLevel E + 1) ^ 2 / (entranceWindow E : ℝ)
          ≤ 4 * E ^ (1 / 2 : ℝ) / (E ^ (3 / 4 : ℝ) / 2) :=
            div_le_div₀ (by positivity) hnum (by positivity) hq
        _ = 8 * (E ^ (1 / 2 : ℝ) / E ^ (3 / 4 : ℝ)) := by field_simp; ring
        _ = 8 * E ^ (-(1 / 4 : ℝ)) := by
          rw [← Real.rpow_sub hE0]
          norm_num
  have hs := (Real.continuous_sqrt.tendsto 0).comp hsq
  rw [Real.sqrt_zero] at hs
  refine hs.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with E hE
  have hd : 0 ≤ entranceCutLevel E + 1 := by
    have := Real.rpow_nonneg (show (0 : ℝ) ≤ E by linarith) (1 / 4 : ℝ)
    unfold entranceCutLevel
    linarith
  simp only [Function.comp_apply]
  rw [Real.sqrt_div' _ (Nat.cast_nonneg _), Real.sqrt_sq hd, div_eq_mul_inv]

/-- `d_E → ∞`. -/
theorem tendsto_entranceCutLevel : Tendsto entranceCutLevel atTop atTop :=
  tendsto_rpow_atTop (by norm_num)

end SwingRepair
