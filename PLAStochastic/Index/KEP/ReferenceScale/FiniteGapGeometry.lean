import PLAStochastic.Index.KEP.ReferenceScale.RarePathGeometry
import Mathlib.Data.Fintype.Fin

/-!
# Finite coordinates of the original stopped gap path

Zero padding preserves every original prefix up to the complete finite
length. The real stopped event is measurable and forces one of the actual
finite partial-sum deviations; no surrogate stopping event is substituted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory Finset Set

def kepFiniteGapSequence {n : ℕ} (x : Fin n → ℝ) : ℕ → ℝ :=
  fun t => if ht : t < n then x ⟨t, ht⟩ else 0

def kepFinitePrefix (n m : ℕ) : Finset (Fin n) := univ.filter (fun i => i.val < m)

theorem measurable_kepFiniteGapSequence (n : ℕ) : Measurable (kepFiniteGapSequence (n := n)) := by
  apply measurable_pi_lambda
  intro t
  by_cases ht : t < n
  · simpa only [kepFiniteGapSequence, dif_pos ht] using
      (measurable_pi_apply (⟨t, ht⟩ : Fin n))
  · simpa only [kepFiniteGapSequence, dif_neg ht] using
      (measurable_const : Measurable (fun _ : Fin n → ℝ => (0 : ℝ)))

theorem kepFinitePrefix_card {n m : ℕ} (hm : m ≤ n) : (kepFinitePrefix n m).card = m := by
  rw [kepFinitePrefix, Fin.card_filter_val_lt, min_eq_right hm]

theorem kepFiniteGapSequence_gapKeys {n m : ℕ} (x : Fin n → ℝ) (hm : m ≤ n) :
    gapKeys (kepFiniteGapSequence x) m = ∑ i ∈ kepFinitePrefix n m, x i := by
  unfold gapKeys
  apply sum_bij (fun t ht => (⟨t, (mem_range.mp ht).trans_le hm⟩ : Fin n))
  · intro t ht
    exact mem_filter.mpr ⟨mem_univ _, mem_range.mp ht⟩
  · intro t _ s _ hts
    exact congrArg Fin.val hts
  · intro i hi
    have him : i.val < m := (mem_filter.mp hi).2
    exact ⟨i.val, mem_range.mpr him, Fin.ext rfl⟩
  · intro t ht
    rw [kepFiniteGapSequence, dif_pos ((mem_range.mp ht).trans_le hm)]

theorem kepFiniteGapSequence_total {n : ℕ} (x : Fin n → ℝ) :
    gapKeys (kepFiniteGapSequence x) n = ∑ i, x i := by
  rw [kepFiniteGapSequence_gapKeys x le_rfl]
  have hp : kepFinitePrefix n n = Finset.univ := by
    ext i
    simp only [kepFinitePrefix, mem_filter, Finset.mem_univ, true_and]
    exact iff_true_intro i.isLt
  rw [hp]

theorem kepFiniteGapSequence_smul {n : ℕ} (c : ℝ) (x : Fin n → ℝ) :
    kepFiniteGapSequence (c • x) = fun t => c * kepFiniteGapSequence x t := by
  funext t
  by_cases ht : t < n
  · simp only [kepFiniteGapSequence, dif_pos ht, Pi.smul_apply, smul_eq_mul]
  · simp only [kepFiniteGapSequence, dif_neg ht, mul_zero]

def kepFiniteStoppedEvent (eps : ℝ) (n : ℕ) : Set (Fin n → ℝ) :=
  {x | gapSegLen eps (kepFiniteGapSequence x) ≤ (n : ℕ∞)}

theorem measurableSet_kepFiniteStoppedEvent (eps : ℝ) (n : ℕ) :
    MeasurableSet (kepFiniteStoppedEvent eps n) := by
  have hh := ((measurableSet_lt_gapSegLen eps n).preimage (measurable_kepFiniteGapSequence n)).compl
  convert hh using 1
  ext x
  simp only [kepFiniteStoppedEvent, mem_compl_iff, Set.mem_preimage, mem_ofPred_eq, not_lt]

theorem kepFiniteStoppedEvent_subset_deviations (eps : ℝ) (n : ℕ) :
    kepFiniteStoppedEvent eps n ⊆ ⋃ m ∈ range (n + 1),
      {x : Fin n → ℝ | eps ≤ |(∑ i ∈ kepFinitePrefix n m, x i) - m|} := by
  intro x hx
  obtain ⟨m, hm, hd⟩ := kep_stopped_prefix_forces_deviation hx
  rw [kepFiniteGapSequence_gapKeys x hm] at hd
  exact mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨mem_range.mpr (by omega), hd.le⟩⟩

end

end PGM
