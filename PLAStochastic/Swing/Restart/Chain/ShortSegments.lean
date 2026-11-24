import PLAStochastic.Swing.Restart.Chain.State

/-! # The short segments used in the restart kernel's common component -/
noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Set
open scoped ENNReal NNReal
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {Ω : Type*}

theorem nativeRestart_two_feasible_iff (X : ℕ → Ω → ℝ) (E x : ℝ) (ω : Ω) :
    nativePrefixFeasible (fun i => (i : ℝ))
      (fun i => nativeCarriedSamples X (fun _ => x) i ω) E 0 2 0 ↔
      |X 0 ω - x| ≤ 3 * E := by
  constructor
  · rintro ⟨m, hm⟩
    have h₁ := hm 1 (by decide)
    have h₂ := hm 2 (by decide)
    simp [nativeCarriedSamples, cumulativeSamples] at h₁ h₂
    rw [abs_le] at h₁ h₂ ⊢
    constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]
  · intro h
    refine ⟨(2*x+X 0 ω)/3, fun i hi => ?_⟩
    have hi' := Finset.mem_Icc.mp hi
    have cases : i = 1 ∨ i = 2 := by omega
    rcases cases with rfl | rfl <;>
      simp [nativeCarriedSamples, cumulativeSamples] <;>
      rw [abs_le] <;>
      constructor <;> linarith [(abs_le.mp h).1, (abs_le.mp h).2]

theorem nativeRestartLength_eq_one_iff (X : ℕ → Ω → ℝ) {E : ℝ}
    (hE : 0 ≤ E) (x : ℝ) (ω : Ω) :
    nativeRestartLength X E x ω = 1 ↔ 3*E < |X 0 ω-x| := by
  have hone := one_le_nativePrefixLength (nativeCarriedSamples X (fun _ => x))
    (fun _ => 0) hE ω
  have htwo := le_nativePrefixLength_iff (nativeCarriedSamples X (fun _ => x))
    (fun _ => 0) E ω 2
  rw [nativeRestart_two_feasible_iff] at htwo
  change (1 : WithTop ℕ) ≤ nativeRestartLength X E x ω at hone
  change (2 : WithTop ℕ) ≤ nativeRestartLength X E x ω ↔ _ at htwo
  have heq : nativeRestartLength X E x ω = 1 ↔
      ¬ (2 : WithTop ℕ) ≤ nativeRestartLength X E x ω := by
    cases hn : nativeRestartLength X E x ω using WithTop.recTopCoe with
    | top => simp
    | coe n =>
      rw [hn] at hone
      have hn1 : 1 ≤ n := WithTop.coe_le_coe.mp hone
      change (n : WithTop ℕ) = ((1 : ℕ) : WithTop ℕ) ↔
        ¬ ((2 : ℕ) : WithTop ℕ) ≤ (n : WithTop ℕ)
      constructor
      · intro h
        have hn : n = 1 := WithTop.coe_inj.mp h
        subst n
        decide
      · intro h
        have hn2 : ¬ 2 ≤ n := fun hn2 => h (WithTop.coe_le_coe.mpr hn2)
        have hn : n = 1 := by omega
        exact congrArg (fun k : ℕ => (k : WithTop ℕ)) hn
  rw [heq, htwo, not_le]

theorem nativeRestartLengthNat_eq_one_iff (X : ℕ → Ω → ℝ) {E : ℝ}
    (hE : 0 ≤ E) (x : ℝ) (ω : Ω) :
    nativeRestartLengthNat X E x ω = 1 ↔ 3*E < |X 0 ω-x| := by
  rw [← nativeRestartLength_eq_one_iff X hE x ω]
  change (nativeRestartLength X E x ω).untopD 0 = 1 ↔ _
  cases nativeRestartLength X E x ω using WithTop.recTopCoe with
  | top => simp
  | coe n => simp

theorem nativeRestartSlopeAt_one (X : ℕ → Ω → ℝ) {E : ℝ} (hE : 0 ≤ E)
    (x : ℝ) (ω : Ω) : nativeRestartSlopeAt X E x 1 ω = x := by
  simp [nativeRestartSlopeAt, nativeSelectedSlope, nativeConeLower, nativeConeUpper,
    nativeLeastSquares, nativeSSECross, nativeSSETimeSquare, nativeCarriedSamples,
    cumulativeSamples, slopeLower, slopeUpper, nativeClippedSlope,
    min_eq_left (show x ≤ x+E by linarith), max_eq_right (show x-E ≤ x by linarith)]

theorem nativeRestartNext_eq_first_increment (X : ℕ → Ω → ℝ) {E : ℝ}
    (hE : 0 ≤ E) (x : ℝ) (ω : Ω) (h : 3*E < |X 0 ω-x|) :
    nativeRestartNext X E x ω = X 0 ω := by
  have hN := (nativeRestartLengthNat_eq_one_iff X hE x ω).mpr h
  simp [nativeRestartNext, nativeRestartSlope, hN, nativeRestartSlopeAt_one X hE,
    cumulativeSamples]

variable [MeasurableSpace Ω]

/-- The short-segment component follows from the actual update, including its selected slope. -/
theorem nativeRestartKernel_one_step_lower {X : ℕ → Ω → ℝ} {μ : Measure Ω}
    [SFinite μ] (hX : ∀ k, Measurable (X k))
    (hG : μ.map (X 0) = gaussianReal 0 1) {E : ℝ} (hE : 0 ≤ E)
    (x : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    gaussianReal 0 1 (A ∩ {y | 3*E < |y-x|}) ≤ nativeRestartKernel X μ E x A := by
  have hs : MeasurableSet (A ∩ {y : ℝ | 3*E < |y-x|}) :=
    hA.inter (measurableSet_lt measurable_const ((measurable_id.sub_const x).abs))
  rw [← hG, Measure.map_apply (hX 0) hs, nativeRestartKernel_apply hX E x hA]
  apply measure_mono
  intro ω hω
  change nativeRestartNext X E x ω ∈ A
  rw [nativeRestartNext_eq_first_increment X hE x ω hω.2]
  exact hω.1

end SwingRepair
