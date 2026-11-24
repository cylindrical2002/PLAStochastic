import PLAStochastic.Swing.Entrance.Deterministic.Cone

/-!
# The adaptive cut: exactly one endpoint is refreshed

At the cut `τ = inf {n ≥ 1 : n (b_n - a_n) ≤ d_E}` with `E ≥ 1`, the index satisfies `τ ≥ 2`
because `1 · (b_1 - a_1) = 2E > d_E`.  Exactly one endpoint is attained by the current sample:
both would give width `2E`, neither would make the previous width at most `d_E`.  In the
coordinates reflected by the side `s`, with frozen endpoint `β` and width `D = τ (b_τ - a_τ)`,
this gives the signed facts collected in `EntranceCutFacts`:

* `s (y_τ - β τ) = E - D`;
* some `i ≤ τ` has `s (y_i - β i) = -E` (the frozen endpoint is attained);
* `|y_i - β i| ≤ E` for `i ≤ τ` (the frozen endpoint is feasible);
* `d_E i < (τ - 1) (E - s (y_i - β i))` for `i < τ` (the early constraints are wide).
-/

namespace SwingRepair

noncomputable section

variable {y : ℕ → ℝ} {E : ℝ}

theorem entranceCutLevel_pos (hE : 0 < E) : 0 < entranceCutLevel E :=
  Real.rpow_pos_of_pos hE _

theorem entranceCutLevel_le (hE : 1 ≤ E) : entranceCutLevel E ≤ E := by
  unfold entranceCutLevel
  calc E ^ (1 / 4 : ℝ) ≤ E ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hE (by norm_num)
    _ = E := Real.rpow_one E

/-- The defining properties of a finite cut. -/
theorem entranceCut_spec {n : ℕ} (h : entranceCut y E = n) :
    1 ≤ n ∧ entranceWidth y E n ≤ entranceCutLevel E ∧
      ∀ k, 1 ≤ k → k < n → entranceCutLevel E < entranceWidth y E k := by
  classical
  unfold entranceCut at h
  split_ifs at h with hex
  · have hn : Nat.find hex = n := by exact_mod_cast h
    subst hn
    refine ⟨(Nat.find_spec hex).1, (Nat.find_spec hex).2, fun k hk hkn => ?_⟩
    have := Nat.find_min hex hkn
    push Not at this
    exact this hk
  · exact absurd h (by simp)

theorem entranceCut_two_le (hy0 : y 0 = 0) (hE : 1 ≤ E) {n : ℕ} (h : entranceCut y E = n) :
    2 ≤ n := by
  obtain ⟨h1, hle, -⟩ := entranceCut_spec h
  by_contra hlt
  have : n = 1 := by omega
  subst this
  rw [entranceWidth_one_anchored hy0] at hle
  have := entranceCutLevel_le hE
  linarith

/-- The signed facts at the cut, in the coordinates reflected by the side. -/
structure EntranceCutFacts (y : ℕ → ℝ) (E : ℝ) (n : ℕ) : Prop where
  two_le : 2 ≤ n
  width_nonneg : 0 ≤ entranceWidth y E n
  width_le : entranceWidth y E n ≤ entranceCutLevel E
  level_le : entranceCutLevel E ≤ E
  level_pos : 0 < entranceCutLevel E
  residual : entranceSide y E n * (y n - entranceFrozenSlope y E n * n) =
    E - entranceWidth y E n
  attained : ∃ i ∈ Finset.Icc 1 n,
    entranceSide y E n * (y i - entranceFrozenSlope y E n * i) = -E
  feasible : ∀ i ∈ Finset.Icc 1 n, |y i - entranceFrozenSlope y E n * i| ≤ E
  early : ∀ i ∈ Finset.Icc 1 (n - 1), entranceCutLevel E * i <
    ((n : ℝ) - 1) * (E - entranceSide y E n * (y i - entranceFrozenSlope y E n * i))

/-- Exactly one endpoint is refreshed at the cut; the signed facts follow. -/
theorem entranceCutFacts_of_cut (hy0 : y 0 = 0) (hE : 1 ≤ E) {n : ℕ}
    (hcut : entranceCut y E = n) (hD : 0 ≤ entranceWidth y E n) :
    EntranceCutFacts y E n := by
  obtain ⟨hn1, hle, hmin⟩ := entranceCut_spec hcut
  have hn2 := entranceCut_two_le hy0 hE hcut
  have hdE := entranceCutLevel_le hE
  have hdpos := entranceCutLevel_pos (show (0 : ℝ) < E by linarith)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hprev := hmin (n - 1) (by omega) (by omega)
  rw [entranceWidth, hcast] at hprev
  have hab : entranceLower y E n ≤ entranceUpper y E n := by
    have : 0 ≤ (n : ℝ) * (entranceUpper y E n - entranceLower y E n) := hD
    by_contra hlt
    push Not at hlt
    nlinarith
  have hnm1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    linarith
  have hfeas : ∀ m, entranceLower y E n ≤ m → m ≤ entranceUpper y E n →
      ∀ i ∈ Finset.Icc 1 n, |y i - m * i| ≤ E := fun m h₁ h₂ =>
    (mem_entranceCone_iff hy0 hn1).mp ⟨h₁, h₂⟩
  by_cases hr : entranceRefreshesLower y E n
  · -- the lower endpoint is refreshed: `s = 1`, `β = b_n = b_{n-1}`
    have hs := entranceSide_of_refresh hr
    have hβ := entranceFrozenSlope_of_refresh hr
    have ha : entranceLower y E n = (y n - E) / n := (entranceRefreshesLower_iff hy0 n).mp hr
    have hbn : entranceUpper y E n ≠ (y n + E) / n := by
      intro hb
      have h2 : entranceWidth y E n = 2 * E := by
        rw [entranceWidth, ha, hb]
        exact width_of_both_refreshed hn1
      linarith
    have hbprev := entranceUpper_eq_prev hy0 hn2 hbn
    refine ⟨hn2, hD, hle, hdE, hdpos, ?_, ?_, ?_, ?_⟩ <;> simp only [hs, hβ]
    · rw [entranceWidth, ha]
      field_simp
      ring
    · obtain ⟨i, hi, hia⟩ := exists_entranceUpper_eq_anchored (E := E) hy0 hn1
      refine ⟨i, hi, ?_⟩
      have hi' : (0 : ℝ) < i := by exact_mod_cast (Finset.mem_Icc.mp hi).1
      rw [hia]
      field_simp
      ring
    · exact hfeas _ hab le_rfl
    · intro i hi
      have hi1 := Finset.mem_Icc.mp hi
      have hi' : (0 : ℝ) < i := by exact_mod_cast hi1.1
      have hlo := sample_le_entranceLower (E := E) hy0 hi
      rw [← hbprev] at hprev
      have h1 : entranceCutLevel E < ((n : ℝ) - 1) *
          (entranceUpper y E n - (y i - E) / i) := by
        nlinarith
      have h2 : ((n : ℝ) - 1) * (entranceUpper y E n - (y i - E) / i) * i =
          ((n : ℝ) - 1) * (E - 1 * (y i - entranceUpper y E n * i)) := by
        field_simp
        ring
      nlinarith
  · -- the lower endpoint is not refreshed: `s = -1`, `β = a_n = a_{n-1}`, `b_n` is refreshed
    have hs := entranceSide_of_not_refresh hr
    have hβ := entranceFrozenSlope_of_not_refresh hr
    have ha' : entranceLower y E n ≠ (y n - E) / n := fun h =>
      hr ((entranceRefreshesLower_iff hy0 n).mpr h)
    have haprev := entranceLower_eq_prev hy0 hn2 ha'
    have hb : entranceUpper y E n = (y n + E) / n := by
      by_contra hb
      have hbprev := entranceUpper_eq_prev hy0 hn2 hb
      rw [← hbprev, ← haprev] at hprev
      have : ((n : ℝ) - 1) * (entranceUpper y E n - entranceLower y E n) ≤
          entranceWidth y E n := by
        rw [entranceWidth]
        nlinarith
      linarith
    refine ⟨hn2, hD, hle, hdE, hdpos, ?_, ?_, ?_, ?_⟩ <;> simp only [hs, hβ]
    · rw [entranceWidth, hb]
      field_simp
      ring
    · obtain ⟨i, hi, hia⟩ := exists_entranceLower_eq_anchored (E := E) hy0 hn1
      refine ⟨i, hi, ?_⟩
      have hi' : (0 : ℝ) < i := by exact_mod_cast (Finset.mem_Icc.mp hi).1
      rw [hia]
      field_simp
      ring
    · exact hfeas _ le_rfl hab
    · intro i hi
      have hi1 := Finset.mem_Icc.mp hi
      have hi' : (0 : ℝ) < i := by exact_mod_cast hi1.1
      have hup := entranceUpper_le_sample (E := E) hy0 hi
      rw [← haprev] at hprev
      have h1 : entranceCutLevel E < ((n : ℝ) - 1) *
          ((y i + E) / i - entranceLower y E n) := by
        nlinarith
      have h2 : ((n : ℝ) - 1) * ((y i + E) / i - entranceLower y E n) * i =
          ((n : ℝ) - 1) * (E - -1 * (y i - entranceLower y E n * i)) := by
        field_simp
        ring
      nlinarith

end

end SwingRepair
