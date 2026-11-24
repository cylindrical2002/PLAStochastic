import PLAStochastic.Swing.Restart.Chain.State

/-! # Maximality, selected slope, and margins of a finite actual restart -/
noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Set
open scoped ENNReal NNReal
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {Ω : Type*}

theorem nativeRestartLengthNat_cast_of_finite (X : ℕ → Ω → ℝ) (E x : ℝ) (ω : Ω)
    (hf : nativeRestartLength X E x ω ≠ ⊤) :
    (nativeRestartLengthNat X E x ω : WithTop ℕ) = nativeRestartLength X E x ω := by
  change (((nativeRestartLength X E x ω).untopD 0 : ℕ) : WithTop ℕ) = _
  cases heq : nativeRestartLength X E x ω using WithTop.recTopCoe with
  | top => exact (hf heq).elim
  | coe n => rfl

theorem nativeRestartLengthNat_pos_of_finite (X : ℕ → Ω → ℝ) {E : ℝ}
    (hE : 0 ≤ E) (x : ℝ) (ω : Ω) (hf : nativeRestartLength X E x ω ≠ ⊤) :
    0 < nativeRestartLengthNat X E x ω := by
  have hh := one_le_nativePrefixLength (nativeCarriedSamples X (fun _ => x))
    (fun _ => 0) hE ω
  change (1 : WithTop ℕ) ≤ nativeRestartLength X E x ω at hh
  rw [← nativeRestartLengthNat_cast_of_finite X E x ω hf] at hh
  exact WithTop.coe_le_coe.mp hh

theorem nativeRestartLengthNat_spec (X : ℕ → Ω → ℝ) (E x : ℝ) (ω : Ω)
    (hf : nativeRestartLength X E x ω ≠ ⊤) :
    nativePrefixFeasible (fun i => (i : ℝ))
        (fun i => nativeCarriedSamples X (fun _ => x) i ω) E 0 (nativeRestartLengthNat X E x ω) 0 ∧
      ¬ nativePrefixFeasible (fun i => (i : ℝ))
        (fun i => nativeCarriedSamples X (fun _ => x) i ω) E 0
          (nativeRestartLengthNat X E x ω+1) 0 := by
  have heq := nativeRestartLengthNat_cast_of_finite X E x ω hf
  constructor
  · exact (le_nativePrefixLength_iff _ _ _ _ _).mp heq.le
  · intro hbad
    have hh := (le_nativePrefixLength_iff (nativeCarriedSamples X (fun _ => x))
      (fun _ => 0) E ω (nativeRestartLengthNat X E x ω+1)).mpr hbad
    change ((nativeRestartLengthNat X E x ω+1 : ℕ) : WithTop ℕ) ≤ nativeRestartLength X E x ω at hh
    rw [← heq] at hh
    have hn : nativeRestartLengthNat X E x ω+1 ≤ nativeRestartLengthNat X E x ω :=
      WithTop.coe_le_coe.mp hh
    omega

theorem nativeRestartSlope_feasible (X : ℕ → Ω → ℝ) {E : ℝ} (hE : 0 ≤ E)
    (x : ℝ) (ω : Ω) (hf : nativeRestartLength X E x ω ≠ ⊤) :
    feasibleSlope (Finset.Icc 1 (nativeRestartLengthNat X E x ω))
      (fun i => (i : ℝ)) (fun i => nativeCarriedSamples X (fun _ => x) i ω) 0 0 E
      (nativeRestartSlope X E x ω) := by
  have hN := nativeRestartLengthNat_pos_of_finite X hE x ω hf
  rw [nativeRestartSlope, nativeRestartSlopeAt, dif_pos hN]
  apply nativeSelectedSlope_feasible
  · intro i hi
    have := (Finset.mem_Icc.mp hi).1
    exact_mod_cast (show 0 < i by omega)
  · simpa only [nativePrefixFeasible, Nat.cast_zero, Nat.zero_add] using
      (nativeRestartLengthNat_spec X E x ω hf).1

theorem nativeRestart_last_accepted_residual (X : ℕ → Ω → ℝ) {E : ℝ} (hE : 0 ≤ E)
    (x : ℝ) (ω : Ω) (hf : nativeRestartLength X E x ω ≠ ⊤) :
    |x+cumulativeSamples X (nativeRestartLengthNat X E x ω-1) ω-
      nativeRestartSlope X E x ω*(nativeRestartLengthNat X E x ω : ℝ)| ≤ E := by
  have hN := nativeRestartLengthNat_pos_of_finite X hE x ω hf
  have hh := nativeRestartSlope_feasible X hE x ω hf _
    (Finset.mem_Icc.mpr ⟨hN, le_rfl⟩)
  simpa only [nativeCarriedSamples, if_neg (by omega : nativeRestartLengthNat X E x ω ≠ 0),
    sub_zero, zero_add] using hh

theorem nativeRestart_rejected_residual (X : ℕ → Ω → ℝ) {E : ℝ} (hE : 0 ≤ E)
    (x : ℝ) (ω : Ω) (hf : nativeRestartLength X E x ω ≠ ⊤) :
    E < |nativeRestartNext X E x ω-nativeRestartSlope X E x ω| := by
  have hfit := nativeRestartSlope_feasible X hE x ω hf
  apply lt_of_not_ge
  intro hbad
  apply (nativeRestartLengthNat_spec X E x ω hf).2
  refine ⟨nativeRestartSlope X E x ω, fun i hi => ?_⟩
  by_cases heq : i = nativeRestartLengthNat X E x ω+1
  · subst i
    simp only [nativeCarriedSamples_succ, Nat.cast_add, Nat.cast_one, Nat.cast_zero,
      sub_zero, zero_add]
    dsimp [nativeRestartNext] at hbad
    have heq : x + cumulativeSamples X (nativeRestartLengthNat X E x ω) ω -
        nativeRestartSlope X E x ω * ((nativeRestartLengthNat X E x ω : ℝ) + 1) =
        x + cumulativeSamples X (nativeRestartLengthNat X E x ω) ω -
          nativeRestartSlope X E x ω * (nativeRestartLengthNat X E x ω : ℝ) -
            nativeRestartSlope X E x ω := by ring
    rwa [heq]
  · simpa only [Nat.cast_zero] using hfit i (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hi).1,
      by have := (Finset.mem_Icc.mp hi).2; omega⟩)

/-- The positive margin is bounded by the actual selected old slope. -/
theorem nativeRestart_margin_pos_le_slope (X : ℕ → Ω → ℝ) {E : ℝ} (hE : 0 ≤ E)
    (x : ℝ) (ω : Ω) (hf : nativeRestartLength X E x ω ≠ ⊤) :
    max (E-|nativeRestartNext X E x ω|) 0 ≤ |nativeRestartSlope X E x ω| := by
  apply max_le _ (abs_nonneg _)
  have hh := nativeRestart_rejected_residual X hE x ω hf
  have ht := abs_sub (nativeRestartNext X E x ω) (nativeRestartSlope X E x ω)
  linarith

/-- The negative margin is bounded by the selected rejection increment itself. -/
theorem nativeRestart_margin_neg_le_increment (X : ℕ → Ω → ℝ) {E : ℝ} (hE : 0 ≤ E)
    (x : ℝ) (ω : Ω) (hf : nativeRestartLength X E x ω ≠ ⊤) :
    max (|nativeRestartNext X E x ω|-E) 0 ≤
      |X (nativeRestartLengthNat X E x ω-1) ω| := by
  apply max_le _ (abs_nonneg _)
  have hN := nativeRestartLengthNat_pos_of_finite X hE x ω hf
  have hh := nativeRestart_last_accepted_residual X hE x ω hf
  have heq : nativeRestartNext X E x ω =
      (x+cumulativeSamples X (nativeRestartLengthNat X E x ω-1) ω-
        nativeRestartSlope X E x ω*(nativeRestartLengthNat X E x ω : ℝ))+
          X (nativeRestartLengthNat X E x ω-1) ω := by
    dsimp [nativeRestartNext]
    have hW : cumulativeSamples X (nativeRestartLengthNat X E x ω) ω =
        cumulativeSamples X (nativeRestartLengthNat X E x ω-1) ω+
          X (nativeRestartLengthNat X E x ω-1) ω := by
      simpa only [Nat.sub_add_cancel hN] using
        cumulativeSamples_succ X (nativeRestartLengthNat X E x ω-1) ω
    rw [hW]
    ring
  have ht := abs_add_le (x+cumulativeSamples X (nativeRestartLengthNat X E x ω-1) ω-
    nativeRestartSlope X E x ω*(nativeRestartLengthNat X E x ω : ℝ))
      (X (nativeRestartLengthNat X E x ω-1) ω)
  rw [heq]
  linarith

end SwingRepair
