import PLAStochastic.Swing.Repair.CycleRegeneration
import PLAStochastic.ForMathlib.Analysis.SpecificLimits.RenewalCountInversion

/-!
# Actual repair output counts and cycle boundaries

The scan invariant below counts emitted chord/bridge pairs along the actual
recursive `scanRepair`. The final specialization derives its cycle-boundary
acceptance test from the real first-rejection predicate and shifted input sums.
-/

noncomputable section

open Finset

namespace SwingRepair

/-- Earlier prefix constraints are a subset of later prefix constraints. -/
theorem prefixCone_antitone_end (t y : ℕ → ℝ) (ε : ℝ) (s : ℕ) :
    Antitone (fun e => prefixCone t y s e ε) := by
  intro e f hef m hm j hj
  exact hm j (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1,
    (Finset.mem_Icc.mp hj).2.trans hef⟩)

/-- An index between successive cycle boundaries has exactly that completed count. -/
theorem completedCount_eq_of_cycle_bounds {L : ℕ → ℕ} (hpos : ∀ n, 0 < L n)
    {k N : ℕ} (hlo : cycleSum L k ≤ N) (hhi : N < cycleSum L (k + 1)) :
    completedCount L N = k := by
  apply le_antisymm _ (le_completedCount hpos hlo)
  by_contra h
  have hk : k + 1 ≤ completedCount L N := by omega
  exact (not_le_of_gt hhi) ((le_completedCount_iff hpos (k + 1) N).mp hk)

/-- The actual scan emits exactly two segments at each crossed cycle boundary;
only its final EOF segment can remain unpaired. -/
theorem scanRepair_length_cycle_bounds (t y : ℕ → ℝ) (ε : ℝ)
    {L : ℕ → ℕ} (hpos : ∀ n, 0 < L n)
    (hcone : ∀ k e, cycleSum L k ≤ e →
      ((prefixCone t y (cycleSum L k) e ε).Nonempty ↔ e < cycleSum L (k + 1)))
    (remaining : ℕ) : ∀ k previous,
      cycleSum L k ≤ previous → previous < cycleSum L (k + 1) →
      2 * completedCount L (previous + remaining) ≤
        (scanRepair t y ε (cycleSum L k) previous remaining).length + 2 * k ∧
      (scanRepair t y ε (cycleSum L k) previous remaining).length + 2 * k ≤
        2 * completedCount L (previous + remaining) + 1 := by
  classical
  induction remaining with
  | zero =>
    intro k p hlo hhi
    have hC := completedCount_eq_of_cycle_bounds hpos hlo hhi
    simp only [Nat.add_zero, hC, scanRepair]
    split_ifs
    · simp only [List.length_singleton]
      omega
    · simp only [List.length_nil, Nat.zero_add]
      omega
  | succ n ih =>
    intro k p hlo hhi
    have hend : p + (n + 1) = (p + 1) + n := by omega
    by_cases haccept : (prefixCone t y (cycleSum L k) (p + 1) ε).Nonempty
    · have hnext := (hcone k (p + 1) (by omega)).mp haccept
      simpa only [scanRepair, if_pos haccept, hend] using ih k (p + 1) (by omega) hnext
    · have hnext : p + 1 = cycleSum L (k + 1) := by
        have hn := (hcone k (p + 1) (by omega)).not.mp haccept
        omega
      have hh : p + 1 < cycleSum L (k + 1 + 1) := by
        rw [hnext]
        exact cycleSum_strictMono hpos (Nat.lt_succ_self _)
      have h := ih (k + 1) (p + 1) (by omega) hh
      rw [← hnext] at h
      simp only [scanRepair, if_neg haccept, List.length_cons, hend]
      omega

/-- The cycle-boundary invariant counts the actual full finite repair stream. -/
theorem repairStream_length_cycle_bounds (t y : ℕ → ℝ) (ε : ℝ)
    {L : ℕ → ℕ} (hpos : ∀ n, 0 < L n)
    (hcone : ∀ k e, cycleSum L k ≤ e →
      ((prefixCone t y (cycleSum L k) e ε).Nonempty ↔ e < cycleSum L (k + 1))) (N : ℕ) :
    2 * completedCount L N ≤ (repairStream t y ε (N + 1)).length ∧
      (repairStream t y ε (N + 1)).length ≤ 2 * completedCount L N + 1 := by
  have h := scanRepair_length_cycle_bounds t y ε hpos hcone N 0 0 (by simp)
    (by simpa using hpos 0)
  simpa only [repairStream, cycleSum_zero, Nat.zero_add, Nat.mul_zero, Nat.add_zero] using h

/-- At a fixed input, once the cone is empty it remains empty at all later prefixes. -/
theorem repairRejected_mono (X : ℕ → Ω → ℝ) (ε : ℝ) (ω : Ω) :
    Monotone (fun n => repairRejected X ε n ω) := by
  intro n m hnm hn hm
  exact hn (hm.mono (prefixCone_antitone_end _ _ ε 0 (Nat.add_le_add_right hnm 1)))

/-- First rejection by an index is equivalent to rejection at that index itself. -/
theorem firstRepairReject_le_iff_rejected (X : ℕ → Ω → ℝ) (ε : ℝ) (ω : Ω) (n : ℕ) :
    firstRepairReject X ε ω ≤ n ↔ repairRejected X ε n ω := by
  rw [firstRepairReject_le_iff]
  exact ⟨fun ⟨j, hj, hrej⟩ => repairRejected_mono X ε ω hj hrej,
    fun hrej => ⟨n, le_rfl, hrej⟩⟩

/-- Every prefix strictly before the finite rejection sample is accepted, and all later ones reject. -/
theorem prefixCone_iff_lt_firstRepairSpan (X : ℕ → Ω → ℝ) (ε : ℝ) (ω : Ω)
    (hfinite : firstRepairReject X ε ω ≠ ⊤) (j : ℕ) :
    (prefixCone (fun n => (n : ℝ)) (fun n => cumulativeSamples X n ω) 0 j ε).Nonempty ↔
      j < firstRepairSpan X ε ω := by
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hfinite
  have hs := firstRepairSpan_eq_of_reject X ε ω r hr.symm
  rw [hs]
  cases j with
  | zero => simp [prefixCone_self_nonempty]
  | succ j =>
    have h := firstRepairReject_le_iff_rejected X ε ω j
    rw [← hr] at h
    have h' : r ≤ j ↔ repairRejected X ε j ω :=
      (show ((r : WithTop ℕ) ≤ (j : WithTop ℕ)) ↔ r ≤ j from WithTop.coe_le_coe).symm.trans h
    simpa only [repairRejected, not_not, not_le, Nat.add_lt_add_iff_right] using (not_congr h').symm

/-- Cumulative values of a concrete zero-based increment sequence. -/
def sequenceSamples (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  cumulativeSamples (fun j (z : ℕ → ℝ) => z j) n x

@[simp] theorem sequenceSamples_zero (x : ℕ → ℝ) : sequenceSamples x 0 = 0 := rfl

theorem sequenceSamples_succ (x : ℕ → ℝ) (n : ℕ) :
    sequenceSamples x (n + 1) = sequenceSamples x n + x n :=
  cumulativeSamples_succ _ _ _

/-- Restarting the increments translates all subsequent cumulative samples by the true anchor. -/
theorem sequenceSamples_shift (x : ℕ → ℝ) (s j : ℕ) :
    sequenceSamples x (s + j) = sequenceSamples x s +
      sequenceSamples (fun n => x (s + n)) j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [← Nat.add_assoc, sequenceSamples_succ, sequenceSamples_succ, ih]
    ring

/-- Translating time indices and subtracting the true anchor leaves every cone exactly unchanged. -/
theorem prefixCone_sequence_shift (x : ℕ → ℝ) (s j : ℕ) (ε : ℝ) :
    prefixCone (fun n => (n : ℝ)) (sequenceSamples x) s (s + j) ε =
      prefixCone (fun n => (n : ℝ)) (sequenceSamples (fun n => x (s + n))) 0 j ε := by
  ext m
  constructor
  · intro hm k hk
    have hk' := Finset.mem_Icc.mp hk
    have hi : s + k ∈ Finset.Icc (s + 1) (s + j) := Finset.mem_Icc.mpr (by omega)
    have h := hm (s + k) hi
    simpa only [slopeLower, slopeUpper, sequenceSamples_shift x s k, sequenceSamples_zero,
      Nat.cast_add, Nat.cast_zero, add_sub_cancel_left, add_sub_cancel_right, sub_zero] using h
  · intro hm i hi
    have hi' := Finset.mem_Icc.mp hi
    let k := i - s
    have hik : i = s + k := by dsimp [k]; omega
    have hk : k ∈ Finset.Icc (0 + 1) j := Finset.mem_Icc.mpr (by dsimp [k]; omega)
    have h := hm k hk
    rw [hik]
    simpa only [slopeLower, slopeUpper, sequenceSamples_shift x s k, sequenceSamples_zero,
      Nat.cast_add, Nat.cast_zero, add_sub_cancel_left, add_sub_cancel_right, sub_zero] using h

/-- Iterated actual restarts are exactly shifts by the sum of the consumed cycle spans. -/
theorem repairCycleInput_eq_shift (ε : ℝ) (x : ℕ → ℝ) (n : ℕ) :
    repairCycleInput ε n x =
      fun j => x (cycleSum (fun i => repairCycleSpan ε i x) n + j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [repairCycleInput_succ]
    funext j
    change repairCycleInput ε n x (repairCycleSpan ε n x + j) =
      x (cycleSum (fun i => repairCycleSpan ε i x) (n + 1) + j)
    rw [congrFun ih (repairCycleSpan ε n x + j), cycleSum_succ]
    simp only [Nat.add_assoc]

/-- For the actual input, each cycle's first rejection is precisely its next global boundary. -/
theorem repairCycle_prefixCone_iff (ε : ℝ) (x : ℕ → ℝ)
    (hfinite : ∀ n, firstRepairReject (fun j (z : ℕ → ℝ) => z j) ε
      (repairCycleInput ε n x) ≠ ⊤) (k e : ℕ)
    (he : cycleSum (fun i => repairCycleSpan ε i x) k ≤ e) :
    (prefixCone (fun n => (n : ℝ)) (sequenceSamples x)
      (cycleSum (fun i => repairCycleSpan ε i x) k) e ε).Nonempty ↔
      e < cycleSum (fun i => repairCycleSpan ε i x) (k + 1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le he
  rw [prefixCone_sequence_shift, cycleSum_succ]
  have h := prefixCone_iff_lt_firstRepairSpan (fun j (z : ℕ → ℝ) => z j) ε
    (repairCycleInput ε k x) (hfinite k) j
  change (prefixCone (fun n => (n : ℝ)) (sequenceSamples (repairCycleInput ε k x))
    0 j ε).Nonempty ↔ j < repairCycleSpan ε k x at h
  rw [repairCycleInput_eq_shift] at h
  simpa only [Nat.add_lt_add_iff_left] using h

/-- The actual finite repair output, not a surrogate count, differs from twice the
number of fully consumed actual cycles only by its optional EOF segment. -/
theorem repairStream_length_actual_cycle_bounds (ε : ℝ) (x : ℕ → ℝ)
    (hfinite : ∀ n, firstRepairReject (fun j (z : ℕ → ℝ) => z j) ε
      (repairCycleInput ε n x) ≠ ⊤) (N : ℕ) :
    2 * completedCount (fun i => repairCycleSpan ε i x) N ≤
        (repairStream (fun n => (n : ℝ)) (sequenceSamples x) ε (N + 1)).length ∧
      (repairStream (fun n => (n : ℝ)) (sequenceSamples x) ε (N + 1)).length ≤
        2 * completedCount (fun i => repairCycleSpan ε i x) N + 1 :=
  repairStream_length_cycle_bounds (fun n => (n : ℝ)) (sequenceSamples x) ε
    (fun n => repairCycleSpan_pos ε n x) (repairCycle_prefixCone_iff ε x hfinite) N

/-- A positive average of the actual cycle spans gives the actual repair output rate. -/
theorem repairStream_rate_of_cycle_average (ε : ℝ) (x : ℕ → ℝ)
    (hfinite : ∀ n, firstRepairReject (fun j (z : ℕ → ℝ) => z j) ε
      (repairCycleInput ε n x) ≠ ⊤) {m : ℝ} (hm : 0 < m)
    (havg : Filter.Tendsto
      (fun n : ℕ => (cycleSum (fun i => repairCycleSpan ε i x) n : ℝ) / (n : ℝ))
      Filter.atTop (nhds m)) :
    Filter.Tendsto
      (fun N : ℕ => ((repairStream (fun n => (n : ℝ)) (sequenceSamples x) ε
        (N + 1)).length : ℝ) / (N : ℝ)) Filter.atTop (nhds (2 / m)) :=
  tendsto_segmentCount_div (fun n => repairCycleSpan_pos ε n x) hm havg
    (repairStream_length_actual_cycle_bounds ε x hfinite)

end SwingRepair
