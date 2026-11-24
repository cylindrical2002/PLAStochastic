import PLAStochastic.Swing.Repair.GeometricRejectionTail
import PLAStochastic.ForMathlib.Probability.Process.IIDRestart.FutureSequence
import PLAStochastic.ForMathlib.Probability.Process.IIDRestart.RegenerativeSplit

/-!
# Actual recursive repair cycles

The state is the actual remaining increment sequence. One step reads the actual
first rejected sample and removes exactly that many increments. Iteration thus
defines the successive repair cycles; their iid laws are proved from the original
Gaussian sequence and the stopping-time split, rather than supplied as hypotheses.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace SwingRepair

/-- Read the actual first-cycle span from a concrete increment sequence. -/
def repairSequenceSpan (ε : ℝ) (x : ℕ → ℝ) : ℕ :=
  firstRepairSpan (fun n (x : ℕ → ℝ) => x n) ε x

/-- Remove exactly the increments consumed by the actual first repair cycle. -/
def repairSequenceRestart (ε : ℝ) (x : ℕ → ℝ) (j : ℕ) : ℝ :=
  x (repairSequenceSpan ε x + j)

/-- The actual remaining increment sequence at the beginning of cycle n. -/
def repairCycleInput (ε : ℝ) (n : ℕ) (x : ℕ → ℝ) : ℕ → ℝ :=
  (repairSequenceRestart ε)^[n] x

/-- The successive actual repair-cycle spans. -/
def repairCycleSpan (ε : ℝ) (n : ℕ) (x : ℕ → ℝ) : ℕ :=
  repairSequenceSpan ε (repairCycleInput ε n x)

theorem repairSequenceSpan_measurable (ε : ℝ) : Measurable (repairSequenceSpan ε) :=
  firstRepairSpan_measurable (fun n => measurable_pi_apply n) ε

theorem repairSequenceRestart_measurable (ε : ℝ) : Measurable (repairSequenceRestart ε) := by
  apply measurable_pi_lambda
  intro j
  exact countableSelection_measurable (fun n => measurable_pi_apply n)
    ((repairSequenceSpan_measurable ε).add_const j)

theorem repairCycleInput_measurable (ε : ℝ) (n : ℕ) : Measurable (repairCycleInput ε n) :=
  (repairSequenceRestart_measurable ε).iterate n

theorem repairCycleSpan_measurable (ε : ℝ) (n : ℕ) : Measurable (repairCycleSpan ε n) :=
  (repairSequenceSpan_measurable ε).comp (repairCycleInput_measurable ε n)

theorem repairCycleSpan_pos (ε : ℝ) (n : ℕ) (x : ℕ → ℝ) : 0 < repairCycleSpan ε n x :=
  Nat.zero_lt_succ _

@[simp] theorem repairCycleInput_zero (ε : ℝ) (x : ℕ → ℝ) : repairCycleInput ε 0 x = x := rfl

theorem repairCycleInput_succ (ε : ℝ) (n : ℕ) (x : ℕ → ℝ) :
    repairCycleInput ε (n + 1) x = repairSequenceRestart ε (repairCycleInput ε n x) :=
  Function.iterate_succ_apply' _ _ _

@[simp] theorem repairCycleSpan_zero (ε : ℝ) (x : ℕ → ℝ) :
    repairCycleSpan ε 0 x = repairSequenceSpan ε x := rfl

theorem firstRepairReject_sequence {Ω : Type*} (X : ℕ → Ω → ℝ) (ε : ℝ) (ω : Ω) :
    firstRepairReject (fun n (x : ℕ → ℝ) => x n) ε (fun n => X n ω) =
      firstRepairReject X ε ω := rfl

theorem repairSequenceSpan_sequence {Ω : Type*} (X : ℕ → Ω → ℝ) (ε : ℝ) (ω : Ω) :
    repairSequenceSpan ε (fun n => X n ω) = firstRepairSpan X ε ω := rfl

/-- The increments actually remaining at cycle n, as a process on the original sample space. -/
def repairCycleIncrements {Ω : Type*} (X : ℕ → Ω → ℝ) (ε : ℝ) (n j : ℕ) (ω : Ω) : ℝ :=
  repairCycleInput ε n (fun k => X k ω) j

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : ℕ → Ω → ℝ}

theorem repairCycleIncrements_measurable (hX : ∀ n, Measurable (X n)) (ε : ℝ) (n j : ℕ) :
    Measurable (repairCycleIncrements X ε n j) :=
  (measurable_pi_apply j).comp
    ((repairCycleInput_measurable ε n).comp (measurable_pi_lambda _ hX))

/-- Each actual cycle's rejection is a stopping time in that cycle's natural increment filtration. -/
theorem repairCycleReject_isStoppingTime (hX : ∀ n, Measurable (X n)) (ε : ℝ) (n : ℕ) :
    IsStoppingTime
      (incrementFiltration (repairCycleIncrements X ε n) (repairCycleIncrements_measurable hX ε n))
      (fun ω => firstRepairReject (fun j (x : ℕ → ℝ) => x j) ε
        (repairCycleInput ε n (fun j => X j ω))) :=
  firstRepairReject_isStoppingTime (repairCycleIncrements_measurable hX ε n) ε

/-- The actual first-cycle deletion preserves the full Gaussian increment-sequence law. -/
theorem repairSequenceRestart_identDistrib_gaussian (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {ε : ℝ} (hε : 0 ≤ ε) :
    IdentDistrib (fun ω => repairSequenceRestart ε (fun j => X j ω))
      (fun ω (j : ℕ) => X j ω) μ μ :=
  stoppedSequence_identDistrib hX hi (gaussianIncrements_identDistrib hX hG)
    (firstRepairReject_isStoppingTime hX ε) (firstRepairReject_ae_finite_gaussian hX hi hG hε)

/-- The actual first span and the entire actual remainder sequence are independent. -/
theorem repairSequenceSplit_indep_gaussian (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {ε : ℝ} (hε : 0 ≤ ε) :
    IndepFun (fun ω => repairSequenceSpan ε (fun j => X j ω))
      (fun ω => repairSequenceRestart ε (fun j => X j ω)) μ := by
  let hτ := firstRepairReject_isStoppingTime hX ε
  have hspan : Measurable[hτ.measurableSpace] (firstRepairSpan X ε) :=
    (hτ.measurable.untopD 0).add_const 1
  exact indep_of_indep_of_le_left
    (stoppedSequence_indep_stopped hX hi (gaussianIncrements_identDistrib hX hG) hτ
      (firstRepairReject_ae_finite_gaussian hX hi hG hε)).symm hspan.comap_le

/-- Each actual recursively generated remainder still has the original sequence law. -/
theorem repairCycleInput_identDistrib_gaussian (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) :
    IdentDistrib (fun ω => repairCycleInput ε n (fun j => X j ω))
      (fun ω (j : ℕ) => X j ω) μ μ :=
  regenerativeState_identDistrib (repairSequenceRestart_measurable ε)
    (measurable_pi_lambda _ hX) (repairSequenceRestart_identDistrib_gaussian hX hi hG hε) n

/-- The actual recursively defined cycle spans are identically distributed with the first span. -/
theorem repairCycleSpan_identDistrib_gaussian (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) :
    IdentDistrib (fun ω => repairCycleSpan ε n (fun j => X j ω)) (firstRepairSpan X ε) μ μ :=
  regenerativeFactor_identDistrib (repairSequenceSpan_measurable ε)
    (repairSequenceRestart_measurable ε) (measurable_pi_lambda _ hX)
    (repairSequenceRestart_identDistrib_gaussian hX hi hG hε) n

/-- Genuine mutual independence of the actual recursively defined Gaussian repair cycles. -/
theorem repairCycleSpans_iIndepFun_gaussian (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {ε : ℝ} (hε : 0 ≤ ε) :
    iIndepFun (fun n ω => repairCycleSpan ε n (fun j => X j ω)) μ :=
  regenerativeFactors_iIndepFun (repairSequenceSpan_measurable ε)
    (repairSequenceRestart_measurable ε) (measurable_pi_lambda _ hX)
    (repairSequenceRestart_identDistrib_gaussian hX hi hG hε)
    (repairSequenceSplit_indep_gaussian hX hi hG hε)

/-- Almost surely every recursively generated actual cycle rejects in finite time. -/
theorem repairCycleRejects_ae_finite_gaussian (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {ε : ℝ} (hε : 0 ≤ ε) :
    ∀ᵐ ω ∂μ, ∀ n, firstRepairReject (fun j (x : ℕ → ℝ) => x j) ε
      (repairCycleInput ε n (fun j => X j ω)) ≠ ⊤ := by
  rw [ae_all_iff]
  intro n
  have hm := (firstRepairReject_isStoppingTime (fun j => measurable_pi_apply j) ε).measurable'
  have hset : MeasurableSet {x : ℕ → ℝ |
      firstRepairReject (fun j (x : ℕ → ℝ) => x j) ε x ≠ ⊤} :=
    (measurableSet_eq_fun hm measurable_const).compl
  exact (repairCycleInput_identDistrib_gaussian hX hi hG hε n).symm.ae_snd hset
    (firstRepairReject_ae_finite_gaussian hX hi hG hε)

end SwingRepair
