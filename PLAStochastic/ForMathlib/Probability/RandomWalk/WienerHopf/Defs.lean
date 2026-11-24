import PLAStochastic.ForMathlib.Probability.Process.IIDRegeneration
import Mathlib.Probability.Moments.ComplexMGF

/-!
# Ladder epochs of an iid real random walk: definitions

The canonical model of an iid real random walk with step law `ρ` is the path space `ℕ → ℝ`
with the product law `pathLaw ρ = ⊗ₙ ρ`; the walk is `partialSum n ω = ω 0 + ⋯ + ω (n - 1)`.

* `firstEntry A ω` is the first time `n ≥ 1` with `partialSum n ω ∈ A`, or `⊤`.
* `ascLadderEpoch = firstEntry (Ioi 0)` is the strict ascending ladder epoch `τ₊`;
  `descLadderEpoch = firstEntry (Iic 0)` is the weak descending ladder epoch `τ₋`.
* `entryValue A ω = partialSum (firstEntry A ω) ω` is the ladder height (when finite).
* `entryTransform ρ A s z = E[s^τ e^{z S_τ}; τ < ∞]` for `τ = firstEntry A`;
  `ascTransform` and `descTransform` are `χ₊` and `χ₋`.
* `stepTransform ρ z = ∫ e^{z y} dρ(y)` is the complex moment generating function of `ρ`.
* `entryCoeff`, `survivalCoeff`, `ladderTimeCoeff` are the coefficients
  `E[e^{z S_n}; τ = n]`, `E[e^{z S_n}; n < τ]` and `E[e^{z S_n}; S_n - S_j ∈ A ∀ j < n]`
  of the generating functions in the Wiener–Hopf factorization.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Complex
open scoped ENNReal

namespace PGM.WienerHopf

/-- The canonical law of an iid sequence with marginal `ρ`. -/
def pathLaw (ρ : Measure ℝ) : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun _ : ℕ => ρ

instance (ρ : Measure ℝ) [IsProbabilityMeasure ρ] : IsProbabilityMeasure (pathLaw ρ) := by
  unfold pathLaw; infer_instance

/-- The random walk `S n = ω 0 + ⋯ + ω (n - 1)`. -/
def partialSum (n : ℕ) (ω : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, ω i

/-- The path seen from time `k`. -/
def shift (k : ℕ) (ω : ℕ → ℝ) : ℕ → ℝ :=
  fun j => ω (k + j)

@[simp] theorem partialSum_zero (ω : ℕ → ℝ) : partialSum 0 ω = 0 := by
  simp [partialSum]

theorem partialSum_succ (n : ℕ) (ω : ℕ → ℝ) :
    partialSum (n + 1) ω = partialSum n ω + ω n := by
  simp [partialSum, Finset.sum_range_succ]

@[simp] theorem shift_apply (k : ℕ) (ω : ℕ → ℝ) (j : ℕ) : shift k ω j = ω (k + j) := rfl

/-- The walk after time `k` is the walk of the shifted path. -/
theorem partialSum_add (k m : ℕ) (ω : ℕ → ℝ) :
    partialSum (k + m) ω = partialSum k ω + partialSum m (shift k ω) := by
  simp [partialSum, Finset.sum_range_add]

@[fun_prop]
theorem measurable_partialSum (n : ℕ) : Measurable (partialSum n) := by
  unfold partialSum
  exact Finset.measurable_sum _ fun i _ => measurable_pi_apply i

@[fun_prop]
theorem measurable_shift (k : ℕ) : Measurable (shift k) :=
  measurable_pi_lambda _ fun j => measurable_pi_apply (k + j)

/-- `partialSum n ω` only depends on `ω 0, …, ω (n - 1)`. -/
theorem partialSum_congr {n : ℕ} {ω ω' : ℕ → ℝ} (h : ∀ i < n, ω i = ω' i) :
    partialSum n ω = partialSum n ω' :=
  Finset.sum_congr rfl fun i hi => h i (Finset.mem_range.mp hi)

/-! ### First entrance times -/

open Classical in
/-- The first time `n ≥ 1` at which the walk is in `A` (`⊤` if it never is). -/
def firstEntry (A : Set ℝ) (ω : ℕ → ℝ) : ℕ∞ :=
  if h : ∃ n, 0 < n ∧ partialSum n ω ∈ A then ((Nat.find h : ℕ) : ℕ∞) else ⊤

/-- The strict ascending ladder epoch `τ₊ = inf {n ≥ 1 : S n > 0}`. -/
abbrev ascLadderEpoch : (ℕ → ℝ) → ℕ∞ := firstEntry (Ioi 0)

/-- The weak descending ladder epoch `τ₋ = inf {n ≥ 1 : S n ≤ 0}`. -/
abbrev descLadderEpoch : (ℕ → ℝ) → ℕ∞ := firstEntry (Iic 0)

/-- The position at the first entrance time (the ladder height, when the time is finite). -/
def entryValue (A : Set ℝ) (ω : ℕ → ℝ) : ℝ :=
  partialSum (firstEntry A ω).toNat ω

variable {A : Set ℝ} {ω : ℕ → ℝ} {n : ℕ}

theorem firstEntry_eq_coe_iff :
    firstEntry A ω = n ↔ 0 < n ∧ partialSum n ω ∈ A ∧
      ∀ j, 0 < j → j < n → partialSum j ω ∉ A := by
  classical
  unfold firstEntry
  split_ifs with h
  · rw [Nat.cast_inj, Nat.find_eq_iff]
    constructor
    · rintro ⟨⟨hn, hA⟩, hlt⟩
      exact ⟨hn, hA, fun j hj hjn hjA => hlt j hjn ⟨hj, hjA⟩⟩
    · rintro ⟨hn, hA, hlt⟩
      exact ⟨⟨hn, hA⟩, fun j hjn ⟨hj, hjA⟩ => hlt j hj hjn hjA⟩
  · simp only [ENat.top_ne_natCast, false_iff]
    rintro ⟨hn, hA, -⟩
    exact h ⟨n, hn, hA⟩

theorem coe_lt_firstEntry_iff :
    (n : ℕ∞) < firstEntry A ω ↔ ∀ j, 0 < j → j ≤ n → partialSum j ω ∉ A := by
  classical
  unfold firstEntry
  split_ifs with h
  · rw [Nat.cast_lt, Nat.lt_find_iff]
    constructor
    · intro hlt j hj hjn hjA
      exact hlt j hjn ⟨hj, hjA⟩
    · rintro hlt j hjn ⟨hj, hjA⟩
      exact hlt j hj hjn hjA
  · simp only [ENat.natCast_lt_top, true_iff]
    intro j hj _ hjA
    exact h ⟨j, hj, hjA⟩

theorem firstEntry_ne_zero : firstEntry A ω ≠ 0 := by
  intro h
  have h' : firstEntry A ω = ((0 : ℕ) : ℕ∞) := by simpa using h
  exact (lt_irrefl 0) (firstEntry_eq_coe_iff.mp h').1

theorem firstEntry_lt_top_iff : firstEntry A ω < ⊤ ↔ ∃ n : ℕ, firstEntry A ω = n := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp h.ne
    exact ⟨n, hn.symm⟩
  · rintro ⟨n, hn⟩
    rw [hn]
    exact ENat.natCast_lt_top n

theorem entryValue_of_eq (h : firstEntry A ω = n) : entryValue A ω = partialSum n ω := by
  simp [entryValue, h]

/-- At a finite entrance time the walk is in `A`. -/
theorem entryValue_mem (h : firstEntry A ω < ⊤) : entryValue A ω ∈ A := by
  obtain ⟨n, hn⟩ := firstEntry_lt_top_iff.mp h
  rw [entryValue_of_eq hn]
  exact (firstEntry_eq_coe_iff.mp hn).2.1

theorem setOf_firstEntry_eq (A : Set ℝ) (n : ℕ) :
    {ω | firstEntry A ω = n} = {ω | 0 < n ∧ partialSum n ω ∈ A ∧
      ∀ j, 0 < j → j < n → partialSum j ω ∉ A} := by
  ext ω
  exact firstEntry_eq_coe_iff

theorem setOf_coe_lt_firstEntry (A : Set ℝ) (n : ℕ) :
    {ω | (n : ℕ∞) < firstEntry A ω} = {ω | ∀ j, 0 < j → j ≤ n → partialSum j ω ∉ A} := by
  ext ω
  exact coe_lt_firstEntry_iff

theorem measurableSet_firstEntry_eq (hA : MeasurableSet A) (n : ℕ) :
    MeasurableSet {ω | firstEntry A ω = n} := by
  rw [setOf_firstEntry_eq]
  refine measurableSet_setOfPred.2 (Measurable.and measurable_const
    (Measurable.and (hA.mem.comp (measurable_partialSum n)) ?_))
  exact Measurable.forall fun j => Measurable.imp measurable_const
    (Measurable.imp measurable_const (hA.mem.comp (measurable_partialSum j)).not)

theorem measurableSet_coe_lt_firstEntry (hA : MeasurableSet A) (n : ℕ) :
    MeasurableSet {ω | (n : ℕ∞) < firstEntry A ω} := by
  rw [setOf_coe_lt_firstEntry]
  refine measurableSet_setOfPred.2 ?_
  exact Measurable.forall fun j => Measurable.imp measurable_const
    (Measurable.imp measurable_const (hA.mem.comp (measurable_partialSum j)).not)

theorem measurable_firstEntry (hA : MeasurableSet A) : Measurable (firstEntry A) :=
  ENat.measurable_iff.2 fun n => measurableSet_firstEntry_eq hA n

theorem measurableSet_firstEntry_lt_top (hA : MeasurableSet A) :
    MeasurableSet {ω | firstEntry A ω < ⊤} :=
  measurable_firstEntry hA (MeasurableSet.of_discrete (s := Iio ⊤))

theorem measurable_partialSum_prod : Measurable fun p : (ℕ → ℝ) × ℕ => partialSum p.2 p.1 :=
  measurable_from_prod_countable_left fun n => measurable_partialSum n

theorem measurable_entryValue (hA : MeasurableSet A) : Measurable (entryValue A) :=
  measurable_partialSum_prod.comp
    (measurable_id.prodMk ((Measurable.of_discrete (f := ENat.toNat)).comp
      (measurable_firstEntry hA)))

/-- Whether the first entrance happens at time `n` only depends on `ω 0, …, ω (n - 1)`. -/
theorem firstEntry_eq_congr {ω ω' : ℕ → ℝ} (h : ∀ i < n, ω i = ω' i) :
    firstEntry A ω = n ↔ firstEntry A ω' = n := by
  have hS : ∀ j ≤ n, partialSum j ω = partialSum j ω' := fun j hj =>
    partialSum_congr fun i hi => h i (lt_of_lt_of_le hi hj)
  rw [firstEntry_eq_coe_iff, firstEntry_eq_coe_iff, hS n le_rfl]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  exact forall_congr' fun j => imp_congr_right fun _ => imp_congr_right fun hjn => by
    rw [hS j hjn.le]

/-- Whether the first entrance happens after time `n` only depends on `ω 0, …, ω (n - 1)`. -/
theorem coe_lt_firstEntry_congr {ω ω' : ℕ → ℝ} (h : ∀ i < n, ω i = ω' i) :
    (n : ℕ∞) < firstEntry A ω ↔ (n : ℕ∞) < firstEntry A ω' := by
  have hS : ∀ j ≤ n, partialSum j ω = partialSum j ω' := fun j hj =>
    partialSum_congr fun i hi => h i (lt_of_lt_of_le hi hj)
  rw [coe_lt_firstEntry_iff, coe_lt_firstEntry_iff]
  exact forall_congr' fun j => imp_congr_right fun _ => imp_congr_right fun hjn => by
    rw [hS j hjn]

/-! ### Transforms and coefficients -/

/-- The joint transform `E[s^τ e^{z S_τ}; τ < ∞]` of the first entrance time `τ` into `A`
and the position there. -/
def entryTransform (ρ : Measure ℝ) (A : Set ℝ) (s z : ℂ) : ℂ :=
  ∫ ω in {ω | firstEntry A ω < ⊤},
    s ^ (firstEntry A ω).toNat * cexp (z * entryValue A ω) ∂pathLaw ρ

/-- `χ₊(s, z) = E[s^{τ₊} e^{z H₊}; τ₊ < ∞]` for the strict ascending ladder. -/
abbrev ascTransform (ρ : Measure ℝ) (s z : ℂ) : ℂ := entryTransform ρ (Ioi 0) s z

/-- `χ₋(s, z) = E[s^{τ₋} e^{z H₋}; τ₋ < ∞]` for the weak descending ladder. -/
abbrev descTransform (ρ : Measure ℝ) (s z : ℂ) : ℂ := entryTransform ρ (Iic 0) s z

/-- The complex moment generating function `φ(z) = ∫ e^{z y} dρ(y)` of the step law. -/
def stepTransform (ρ : Measure ℝ) (z : ℂ) : ℂ :=
  ∫ y, cexp (z * y) ∂ρ

theorem stepTransform_eq_complexMGF (ρ : Measure ℝ) (z : ℂ) :
    stepTransform ρ z = complexMGF id ρ z := rfl

/-- `E[e^{z S_n}; τ = n]` for the first entrance time `τ` into `A`. -/
def entryCoeff (ρ : Measure ℝ) (A : Set ℝ) (z : ℂ) (n : ℕ) : ℂ :=
  ∫ ω in {ω | firstEntry A ω = n}, cexp (z * partialSum n ω) ∂pathLaw ρ

/-- `E[e^{z S_n}; n < τ]` for the first entrance time `τ` into `A`. -/
def survivalCoeff (ρ : Measure ℝ) (A : Set ℝ) (z : ℂ) (n : ℕ) : ℂ :=
  ∫ ω in {ω | (n : ℕ∞) < firstEntry A ω}, cexp (z * partialSum n ω) ∂pathLaw ρ

/-- `n` is an `A`-ladder time: `S n - S j ∈ A` for every `j < n`. -/
def IsLadderTime (A : Set ℝ) (n : ℕ) (ω : ℕ → ℝ) : Prop :=
  ∀ j < n, partialSum n ω - partialSum j ω ∈ A

/-- `E[e^{z S_n}; n is an A-ladder time]`. -/
def ladderTimeCoeff (ρ : Measure ℝ) (A : Set ℝ) (z : ℂ) (n : ℕ) : ℂ :=
  ∫ ω in {ω | IsLadderTime A n ω}, cexp (z * partialSum n ω) ∂pathLaw ρ

theorem measurableSet_isLadderTime (hA : MeasurableSet A) (n : ℕ) :
    MeasurableSet {ω | IsLadderTime A n ω} := by
  refine measurableSet_setOfPred.2 (Measurable.forall fun j => Measurable.imp measurable_const ?_)
  exact hA.mem.comp ((measurable_partialSum n).sub (measurable_partialSum j))

theorem isLadderTime_congr {ω ω' : ℕ → ℝ} (h : ∀ i < n, ω i = ω' i) :
    IsLadderTime A n ω ↔ IsLadderTime A n ω' := by
  have hS : ∀ j ≤ n, partialSum j ω = partialSum j ω' := fun j hj =>
    partialSum_congr fun i hi => h i (lt_of_lt_of_le hi hj)
  unfold IsLadderTime
  exact forall_congr' fun j => imp_congr_right fun hjn => by rw [hS n le_rfl, hS j hjn.le]

end PGM.WienerHopf
