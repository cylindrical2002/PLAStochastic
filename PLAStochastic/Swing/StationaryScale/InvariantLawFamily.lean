import PLAStochastic.Swing.StationaryScale.RestartInvariantLaw

/-! # The actual finite-budget stationary family

`nativeRestart_stationary` gives, for every positive budget, existence and
uniqueness of an invariant probability law of the actual constrained-SSE
restart kernel.  Theorem 4.3 needs that law as a *function* of the budget, so
that a budget filter can be pushed through the weak limit.  This file performs
exactly that step and nothing else: it names the law, proves it is a
probability measure, proves it is invariant, and records that it is the unique
invariant probability.  No new probabilistic content is introduced.

The definition is total.  Outside the regime in which an invariant probability
exists it returns the Dirac mass at `0`, so `IsProbabilityMeasure` holds
unconditionally and downstream statements never carry a positivity side
condition just to know the family consists of probability measures.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-- The invariant-probability predicate for the native restart kernel. -/
def NativeStationaryExists (X : ℕ → Ω → ℝ) (μ : Measure Ω) (E : ℝ) : Prop :=
  ∃ π : Measure ℝ, IsProbabilityMeasure π ∧
    (nativeRestartKernel X μ E).Invariant π

/-- `π_E`: the stationary law of the actual restart chain at budget `E`. -/
def nativeStationaryLaw (X : ℕ → Ω → ℝ) (μ : Measure Ω) (E : ℝ) : Measure ℝ :=
  if h : NativeStationaryExists X μ E then h.choose else Measure.dirac 0

theorem nativeStationaryLaw_isProbabilityMeasure (X : ℕ → Ω → ℝ) (μ : Measure Ω)
    (E : ℝ) : IsProbabilityMeasure (nativeStationaryLaw X μ E) := by
  unfold nativeStationaryLaw
  by_cases h : NativeStationaryExists X μ E
  · rw [dif_pos h]
    exact h.choose_spec.1
  · rw [dif_neg h]
    infer_instance

theorem nativeStationaryLaw_invariant_of_exists
    {E : ℝ} (h : NativeStationaryExists X μ E) :
    (nativeRestartKernel X μ E).Invariant (nativeStationaryLaw X μ E) := by
  unfold nativeStationaryLaw
  rw [dif_pos h]
  exact h.choose_spec.2

/-- Existence is a theorem, not a hypothesis: it is the invariant-law part of
Theorem 4.1 for the actual restart kernel. -/
theorem nativeStationaryExists
    (hX : ∀ k, Measurable (X k)) (hi : iIndepFun X μ)
    (hG : ∀ k, μ.map (X k) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E) :
    NativeStationaryExists X μ E := by
  obtain ⟨π, _α, hπP, _, _, hπinv, _⟩ := nativeRestart_stationary hX hi hG hE
  exact ⟨π, hπP, hπinv⟩

/-- `π_E` is invariant for the actual restart kernel at every positive budget. -/
theorem nativeStationaryLaw_invariant
    (hX : ∀ k, Measurable (X k)) (hi : iIndepFun X μ)
    (hG : ∀ k, μ.map (X k) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E) :
    (nativeRestartKernel X μ E).Invariant (nativeStationaryLaw X μ E) :=
  nativeStationaryLaw_invariant_of_exists (nativeStationaryExists hX hi hG hE)

/-- `π_E` is *the* invariant probability: uniqueness is inherited from the
two-step Doeblin minorization of Theorem 4.1. -/
theorem nativeStationaryLaw_unique
    (hX : ∀ k, Measurable (X k)) (hi : iIndepFun X μ)
    (hG : ∀ k, μ.map (X k) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E)
    {ν : Measure ℝ} (hν : IsProbabilityMeasure ν)
    (hinv : (nativeRestartKernel X μ E).Invariant ν) :
    ν = nativeStationaryLaw X μ E := by
  obtain ⟨π, _α, hπP, _, _, hπinv, huniq, _⟩ := nativeRestart_stationary hX hi hG hE
  have hπEq : nativeStationaryLaw X μ E = π :=
    huniq _ (nativeStationaryLaw_isProbabilityMeasure X μ E)
      (nativeStationaryLaw_invariant hX hi hG hE)
  rw [hπEq]
  exact huniq ν hν hinv

/-- The budget-indexed family used by Theorem 4.3. -/
theorem nativeStationaryLaw_family_invariant
    (hX : ∀ k, Measurable (X k)) (hi : iIndepFun X μ)
    (hG : ∀ k, μ.map (X k) = gaussianReal 0 1)
    {ι : Type*} {budget : ι → ℝ} (hbudget : ∀ i, 0 < budget i) :
    ∀ i, (nativeRestartKernel X μ (budget i)).Invariant
      (nativeStationaryLaw X μ (budget i)) :=
  fun i => nativeStationaryLaw_invariant hX hi hG (hbudget i)

end SwingRepair
