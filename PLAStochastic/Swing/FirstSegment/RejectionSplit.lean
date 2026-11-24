import PLAStochastic.Swing.FirstSegment.LowerRejectionReflection

/-! # Every actual first rejection is an upper or a lower rejection

The charging estimates are proved separately on the upper layer and, through
the reflection of `NativeFirstReflection`, on the lower layer.  This file
proves that the two layers really exhaust the first rejection, so no third
kind of rejection is left uncovered.
-/
noncomputable section
open Classical
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Ω : Type*}

theorem Finset.Icc_one_succ_insert (n : ℕ) :
    Finset.Icc 1 (n+2) = insert (n+2) (Finset.Icc 1 (n+1)) := by
  ext j
  simp only [Finset.mem_Icc, Finset.mem_insert]
  omega

/-- Feasibility of the extended prefix splits into the old cone and the new sample. -/
theorem feasibleSlope_Icc_succ_iff (y : ℕ → ℝ) (q E m : ℝ) (n : ℕ) :
    feasibleSlope (Finset.Icc 1 (n+2)) (fun j => (j : ℝ)) y 0 q E m ↔
      feasibleSlope (Finset.Icc 1 (n+1)) (fun j => (j : ℝ)) y 0 q E m ∧
        |y (n+2)-(q+m*(((n+2 : ℕ) : ℝ)-0))| ≤ E := by
  rw [Finset.Icc_one_succ_insert]
  constructor
  · intro h
    exact ⟨fun j hj => h j (Finset.mem_insert_of_mem hj), h (n+2) (Finset.mem_insert_self _ _)⟩
  · rintro ⟨h₁, h₂⟩ j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact h₂
    · exact h₁ j hj

/-- The actual dichotomy: the fresh increment either exceeds the upper rejection
threshold or falls below the lower one. -/
theorem nativeFirst_rejection_upper_or_lower (Z : ℕ → Ω → ℝ) {E : ℝ} (hE : 0 ≤ E) (n : ℕ)
    {ω : Ω}
    (hfit : nativePrefixFeasible (fun j => (j : ℝ)) (fun j => cumulativeSamples Z j ω)
      E 0 (n+1) (cumulativeSamples Z 0 ω))
    (hrej : ¬ nativePrefixFeasible (fun j => (j : ℝ)) (fun j => cumulativeSamples Z j ω)
      E 0 (n+2) (cumulativeSamples Z 0 ω)) :
    ω ∈ nativeFirstUpperRejectionEvent Z E n ∪ nativeFirstLowerRejectionEvent Z E n := by
  set y : ℕ → ℝ := fun j => cumulativeSamples Z j ω with hydef
  set q : ℝ := cumulativeSamples Z 0 ω with hqdef
  have hne : (Finset.Icc 1 (n+1)).Nonempty := Finset.nonempty_Icc.mpr (by omega : (1 : ℕ) ≤ n+1)
  have ht : ∀ i ∈ Finset.Icc 1 (n+1), (0 : ℝ) < (i : ℝ) := by
    intro i hi
    have := (Finset.mem_Icc.mp hi).1
    exact_mod_cast (by omega : 0 < i)
  have hfit' : ∃ m, feasibleSlope (Finset.Icc 1 (n+1)) (fun j => (j : ℝ)) y 0 q E m := by
    simpa only [nativePrefixFeasible, Nat.cast_zero, Nat.zero_add] using hfit
  set u : ℝ := nativeConeUpper (Finset.Icc 1 (n+1)) hne (fun j => (j : ℝ)) y 0 q E with hudef
  set l : ℝ := nativeConeLower (Finset.Icc 1 (n+1)) hne (fun j => (j : ℝ)) y 0 q E with hldef
  have hlu : l ≤ u :=
    (nativeCone_nonempty_iff (Finset.Icc 1 (n+1)) hne (fun j => (j : ℝ)) y 0 q E ht).mp hfit'
  set sl : ℝ := slopeLower (((n+2 : ℕ) : ℝ)) (y (n+2)) 0 q E with hsldef
  set su : ℝ := slopeUpper (((n+2 : ℕ) : ℝ)) (y (n+2)) 0 q E with hsudef
  have hpos : (0 : ℝ) < ((n+2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n+2)
  have hslsu : sl ≤ su := by
    rw [hsldef, hsudef, slopeLower, slopeUpper, div_le_div_iff_of_pos_right (by linarith)]
    linarith
  -- if neither threshold is violated the extended prefix would still be feasible
  have hdicho : u < sl ∨ su < l := by
    rcases lt_or_ge u sl with h | h₁
    · exact Or.inl h
    rcases lt_or_ge su l with h | h₂
    · exact Or.inr h
    exfalso
    have hm : feasibleSlope (Finset.Icc 1 (n+1)) (fun j => (j : ℝ)) y 0 q E (max l sl) := by
      apply (nativeCone_mem_iff (Finset.Icc 1 (n+1)) hne (fun j => (j : ℝ)) y 0 q E _ ht).mp
      exact ⟨le_max_left _ _, max_le hlu h₁⟩
    have hnew : |y (n+2)-(q+max l sl*(((n+2 : ℕ) : ℝ)-0))| ≤ E := by
      have hb := (sample_error_iff_bounds (sampleTime := ((n+2 : ℕ) : ℝ)) (sampleValue := y (n+2))
        (anchorTime := 0) (anchorValue := q) (ε := E) (m := max l sl) hpos).mpr
        ⟨le_max_right _ _, max_le h₂ hslsu⟩
      simpa only [sub_zero] using hb
    have hfull : feasibleSlope (Finset.Icc 1 (n+2)) (fun j => (j : ℝ)) y 0 q E (max l sl) :=
      (feasibleSlope_Icc_succ_iff y q E (max l sl) n).mpr ⟨hm, hnew⟩
    exact hrej ⟨max l sl, by simpa only [Nat.cast_zero, Nat.zero_add] using hfull⟩
  have hstate : nativeFirstPrefixState (cumulativeSamples Z) E n ω =
      (u, q+((n+2 : ℕ) : ℝ)*u+E-y (n+1),
        if nativePrefixFeasible (fun j => (j : ℝ)) y E 0 (n+1) q then true else false) := rfl
  have hflag : (nativeFirstPrefixState (cumulativeSamples Z) E n ω).2.2 = true := by
    rw [hstate]; simp only [if_pos hfit]
  have hstep : y (n+2) = y (n+1)+Z (n+1) ω := by
    simpa only [hydef, Nat.add_assoc] using cumulativeSamples_succ Z (n+1) ω
  rcases hdicho with hup | hlow
  · left
    refine ⟨hflag, ?_⟩
    rw [hstate]
    dsimp only
    rw [hsldef, slopeLower, lt_div_iff₀ (by linarith : (0 : ℝ) < ((n+2 : ℕ) : ℝ)-0)] at hup
    rw [hstep] at hup
    nlinarith
  · right
    refine ⟨hflag, ?_⟩
    have hlow' : su < nativeFirstConeLower (cumulativeSamples Z) E n ω := hlow
    rw [hsudef, slopeUpper, div_lt_iff₀ (by linarith : (0 : ℝ) < ((n+2 : ℕ) : ℝ)-0)] at hlow'
    rw [hstep] at hlow'
    change Z (n+1) ω < cumulativeSamples Z 0 ω+((n+2 : ℕ) : ℝ)*
      nativeFirstConeLower (cumulativeSamples Z) E n ω-E-cumulativeSamples Z (n+1) ω
    nlinarith

/-- Geometry at an actual lower rejection, obtained from the reflected upper spec. -/
theorem nativeFirstLowerRejectionEvent_spec (Z : ℕ → Ω → ℝ) (E : ℝ) (n : ℕ) {ω : Ω}
    (hω : ω ∈ nativeFirstLowerRejectionEvent Z E n) :
    nativePrefixFeasible (fun j => (j : ℝ)) (fun j => cumulativeSamples Z j ω) E 0 (n+1) 0 ∧
    ¬ nativePrefixFeasible (fun j => (j : ℝ)) (fun j => cumulativeSamples Z j ω) E 0 (n+2) 0 ∧
    feasibleSlope (Finset.Icc 1 (n+1)) (fun j => (j : ℝ)) (fun j => cumulativeSamples Z j ω) 0 0 E
      (nativeFirstConeLower (cumulativeSamples Z) E n ω) ∧
    nativeFirstLowerThreshold (cumulativeSamples Z) E n ω ≤
      nativeFirstConeLower (cumulativeSamples Z) E n ω := by
  have hmem := hω
  rw [nativeFirstLowerRejectionEvent_eq_neg] at hmem
  have hs := nativeFirstUpperRejectionEvent_spec (negIncrements Z) E n hmem
  have hy : (fun j => cumulativeSamples (negIncrements Z) j ω) =
      (fun j => -(cumulativeSamples Z j ω)) := funext fun j => cumulativeSamples_neg Z j ω
  have hstate := nativeFirstPrefixState_neg Z E n ω
  have hfeas : ∀ j, nativePrefixFeasible (fun i => (i : ℝ))
      (fun i => cumulativeSamples (negIncrements Z) i ω) E 0 j 0 ↔
      nativePrefixFeasible (fun i => (i : ℝ)) (fun i => cumulativeSamples Z i ω) E 0 j 0 := by
    intro j
    rw [hy]
    simpa using nativePrefixFeasible_neg (fun i => (i : ℝ)) (fun i => cumulativeSamples Z i ω) E 0 j 0
  refine ⟨(hfeas (n+1)).mp hs.1, fun h => hs.2.1 ((hfeas (n+2)).mpr h), ?_, ?_⟩
  · have hfs := hs.2.2.1
    rw [hstate] at hfs
    dsimp only at hfs
    rw [hy] at hfs
    have := (feasibleSlope_neg (Finset.Icc 1 (n+1)) (fun j => (j : ℝ))
      (fun j => cumulativeSamples Z j ω) 0 0 E
      (nativeFirstConeLower (cumulativeSamples Z) E n ω)).mp (by simpa using hfs)
    exact this
  · have hle := hs.2.2.2
    rw [hstate] at hle
    dsimp only at hle
    linarith

end SwingRepair
