import PLAStochastic.ForMathlib.Probability.Process.IIDRestart.AeFiniteStoppingTime
import PLAStochastic.Swing.Repair.Stream
import Mathlib.Probability.Process.HittingTime

/-!
# The actual first rejection is a stopping time

The zero-based increments are X 0, X 1, ... and Y n is the sum of X k for k < n.
The rejection process at index n tests the repair's actual half-budget prefix cone
through sample n + 1. Its first hitting index K is therefore the last observed
increment index. The paper's rejected sample / cycle span is J = K + 1.

No finiteness assumption enters the construction: never rejecting gives infinity.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace SwingRepair

/-- A finite family of closed real intervals meets iff every lower bound is below every upper. -/
theorem finite_intervals_nonempty_iff {ι : Type*} (s : Finset ι) (L U : ι → ℝ) :
    (∃ m, ∀ i ∈ s, L i ≤ m ∧ m ≤ U i) ↔
      ∀ i ∈ s, ∀ j ∈ s, L i ≤ U j := by
  constructor
  · rintro ⟨m, hm⟩ i hi j hj
    exact (hm i hi).1.trans (hm j hj).2
  · intro h
    by_cases hs : s.Nonempty
    · refine ⟨s.sup' hs L, fun i hi => ⟨Finset.le_sup' L hi, ?_⟩⟩
      exact Finset.sup'_le hs L (fun j hj => h j hj i hi)
    · refine ⟨0, ?_⟩
      intro i hi
      exact (hs ⟨i, hi⟩).elim

/-- This exact finite feasibility criterion avoids projecting over arbitrary real slopes. -/
theorem prefixCone_nonempty_iff_pairwise_bounds (t y : ℕ → ℝ) (s e : ℕ) (ε : ℝ) :
    (prefixCone t y s e ε).Nonempty ↔
      ∀ i ∈ Finset.Icc (s + 1) e, ∀ j ∈ Finset.Icc (s + 1) e,
        slopeLower (t i) (y i) (t s) (y s) (ε / 2) ≤
          slopeUpper (t j) (y j) (t s) (y s) (ε / 2) :=
  finite_intervals_nonempty_iff _ _ _

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {X : ℕ → Ω → ℝ}

/-- The actual cumulative samples, with Y 0 = 0. -/
def cumulativeSamples (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, X k ω

omit mΩ in
@[simp] theorem cumulativeSamples_zero (X : ℕ → Ω → ℝ) (ω : Ω) :
    cumulativeSamples X 0 ω = 0 := by simp [cumulativeSamples]

omit mΩ in
theorem cumulativeSamples_succ (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    cumulativeSamples X (n + 1) ω = cumulativeSamples X n ω + X n ω := by
  simp [cumulativeSamples, Finset.sum_range_succ]

/-- Earlier increments are measurable in the natural information through n. -/
theorem increment_measurable_at (hX : ∀ k, Measurable (X k)) {k n : ℕ} (hkn : k ≤ n) :
    Measurable[incrementFiltration X hX n] (X k) := by
  apply measurable_iff_comap_le.mpr
  change MeasurableSpace.comap (X k) inferInstance ≤
    ⨆ j ≤ n, MeasurableSpace.comap (X j) inferInstance
  exact le_iSup_of_le k (le_iSup_of_le hkn le_rfl)

/-- Sample j only uses increment indices strictly below j. -/
theorem cumulativeSamples_measurable_at (hX : ∀ k, Measurable (X k))
    {j n : ℕ} (hjn : j ≤ n + 1) :
    Measurable[incrementFiltration X hX n] (cumulativeSamples X j) := by
  apply Finset.measurable_sum
  intro k hk
  apply increment_measurable_at hX
  have := Finset.mem_range.mp hk
  omega

/-- Feasibility of the actual prefix through sample n + 1 is measurable at increment index n. -/
theorem repairPrefix_measurableSet (hX : ∀ k, Measurable (X k)) (n : ℕ) (ε : ℝ) :
    MeasurableSet[incrementFiltration X hX n]
      {ω | (prefixCone (fun j => (j : ℝ)) (fun j => cumulativeSamples X j ω)
        0 (n + 1) ε).Nonempty} := by
  have heq : {ω | (prefixCone (fun j => (j : ℝ)) (fun j => cumulativeSamples X j ω)
      0 (n + 1) ε).Nonempty} =
      ⋂ i ∈ Finset.Icc 1 (n + 1), ⋂ j ∈ Finset.Icc 1 (n + 1),
        {ω | slopeLower (i : ℝ) (cumulativeSamples X i ω) 0 0 (ε / 2) ≤
          slopeUpper (j : ℝ) (cumulativeSamples X j ω) 0 0 (ε / 2)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, prefixCone_nonempty_iff_pairwise_bounds,
      Nat.zero_add, Nat.cast_zero, cumulativeSamples_zero]
  rw [heq]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun hi =>
    MeasurableSet.iInter fun j => MeasurableSet.iInter fun hj => ?_
  have hmi := cumulativeSamples_measurable_at hX (Finset.mem_Icc.mp hi).2
  have hmj := cumulativeSamples_measurable_at hX (Finset.mem_Icc.mp hj).2
  exact measurableSet_le
    (((hmi.sub measurable_const).sub measurable_const).div_const _)
    (((hmj.sub measurable_const).add measurable_const).div_const _)

/-- The actual cone-empty predicate at the last observed increment index. -/
def repairRejected (X : ℕ → Ω → ℝ) (ε : ℝ) (n : ℕ) (ω : Ω) : Prop :=
  ¬ (prefixCone (fun j => (j : ℝ)) (fun j => cumulativeSamples X j ω)
    0 (n + 1) ε).Nonempty

/-- First rejection, retaining infinity on paths that never reject. -/
def firstRepairReject (X : ℕ → Ω → ℝ) (ε : ℝ) : Ω → WithTop ℕ :=
  hittingAfter (repairRejected X ε) {True} 0

/-- The actual first cone rejection is a stopping time for the increment filtration. -/
theorem firstRepairReject_isStoppingTime (hX : ∀ k, Measurable (X k)) (ε : ℝ) :
    IsStoppingTime (incrementFiltration X hX) (firstRepairReject X ε) := by
  apply Adapted.isStoppingTime_hittingAfter
  · intro n
    exact (@measurableSet_setOfPred Ω (incrementFiltration X hX n)
      (repairRejected X ε n)).mp (repairPrefix_measurableSet hX n ε).compl
  · exact measurableSet_singleton True

omit mΩ in
/-- The defining first-hit property uses precisely the actual repair cone. -/
theorem firstRepairReject_le_iff (X : ℕ → Ω → ℝ) (ε : ℝ) (ω : Ω) (n : ℕ) :
    firstRepairReject X ε ω ≤ n ↔ ∃ j ≤ n, repairRejected X ε j ω := by
  simpa [firstRepairReject] using
    (hittingAfter_le_iff (u := repairRejected X ε) (s := {True}) (n := 0) (i := n) (ω := ω))

omit mΩ in
/-- Infinity means that every actual half-budget prefix stays feasible. -/
theorem firstRepairReject_eq_top_iff (X : ℕ → Ω → ℝ) (ε : ℝ) (ω : Ω) :
    firstRepairReject X ε ω = ⊤ ↔ ∀ n, ¬ repairRejected X ε n ω := by
  simp [firstRepairReject, hittingAfter_eq_top_iff]

omit mΩ in
/-- The first observed sample cannot reject at a nonnegative tolerance. -/
theorem firstRepairReject_pos (X : ℕ → Ω → ℝ) {ε : ℝ} (hε : 0 ≤ ε) (ω : Ω) :
    0 < firstRepairReject X ε ω := by
  apply lt_of_not_ge
  intro hle
  obtain ⟨j, hj, hrej⟩ := (firstRepairReject_le_iff X ε ω 0).mp hle
  have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
  subst j
  apply hrej
  exact prefixCone_next_nonempty (fun i j hij => by exact_mod_cast hij) hε 0

omit mΩ in
/-- Three consecutive feasible sample residuals bound the difference of the two increments. -/
theorem repairPrefix_increment_difference_bound (X : ℕ → Ω → ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) (ω : Ω) (s : ℕ)
    (hcone : (prefixCone (fun j => (j : ℝ)) (fun j => cumulativeSamples X j ω)
      0 (s + 2) ε).Nonempty) :
    |X (s + 1) ω - X s ω| ≤ 2 * ε := by
  obtain ⟨m, hm⟩ := hcone
  have ht : StrictMono (fun j : ℕ => (j : ℝ)) := fun i j hij => by
    dsimp
    exact_mod_cast hij
  have h₀ := prefix_line_error ht hε hm (Nat.zero_le s) (show s ≤ s + 2 by omega)
  have h₁ := prefix_line_error ht hε hm (Nat.zero_le (s + 1))
    (show s + 1 ≤ s + 2 by omega)
  have h₂ := prefix_line_error ht hε hm (Nat.zero_le (s + 2)) le_rfl
  have hsum₂ : cumulativeSamples X (s + 2) ω =
      cumulativeSamples X s ω + X s ω + X (s + 1) ω := by
    rw [show s + 2 = (s + 1) + 1 by omega, cumulativeSamples_succ, cumulativeSamples_succ]
  rw [hsum₂] at h₂
  rw [cumulativeSamples_succ] at h₁
  simp only [line, Nat.cast_zero, cumulativeSamples_zero, zero_add, sub_zero,
    Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at h₀ h₁ h₂
  obtain ⟨h₀l, h₀u⟩ := abs_le.mp h₀
  obtain ⟨h₁l, h₁u⟩ := abs_le.mp h₁
  obtain ⟨h₂l, h₂u⟩ := abs_le.mp h₂
  apply abs_le.mpr
  constructor <;> nlinarith

omit mΩ in
/-- A two-increment escape forces actual rejection by the end of that pair. -/
theorem firstRepairReject_le_of_increment_difference (X : ℕ → Ω → ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) (ω : Ω) (s : ℕ)
    (hescape : 2 * ε < |X (s + 1) ω - X s ω|) :
    firstRepairReject X ε ω ≤ (s + 1 : ℕ) := by
  apply (firstRepairReject_le_iff X ε ω (s + 1)).mpr
  refine ⟨s + 1, le_rfl, ?_⟩
  intro hcone
  exact (not_le_of_gt hescape) (repairPrefix_increment_difference_bound X hε ω s hcone)

variable {μ : Measure Ω}

/-- The actual repair's future block has the original joint law when its first rejection is a.s. finite. -/
theorem firstRepairReject_block_identDistrib [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ) (ε : ℝ)
    (isFiniteK : ∀ᵐ ω ∂μ, firstRepairReject X ε ω ≠ ⊤) (r : ℕ) :
    IdentDistrib (fun ω (j : Fin r) => X ((firstRepairReject X ε ω).untopD 0 + 1 + j.val) ω)
      (fun ω (j : Fin r) => X j.val ω) μ μ :=
  stoppedBlock_identDistrib_aeFinite hX hi hid (firstRepairReject_isStoppingTime hX ε) isFiniteK r

/-- The actual repair's future block is independent of the original first-rejection sigma-algebra. -/
theorem firstRepairReject_block_indep [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ) (ε : ℝ)
    (isFiniteK : ∀ᵐ ω ∂μ, firstRepairReject X ε ω ≠ ⊤) (r : ℕ) :
    Indep (MeasurableSpace.comap
      (fun ω (j : Fin r) => X ((firstRepairReject X ε ω).untopD 0 + 1 + j.val) ω) inferInstance)
      (firstRepairReject_isStoppingTime hX ε).measurableSpace μ :=
  stoppedBlock_indep_stopped_aeFinite hX hi hid (firstRepairReject_isStoppingTime hX ε) isFiniteK r

end SwingRepair
