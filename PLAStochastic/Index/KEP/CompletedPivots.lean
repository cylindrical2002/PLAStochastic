import PLAStochastic.Index.KEP.PivotStopping
import PLAStochastic.ForMathlib.Probability.Process.IIDRegeneration

/-!
# Completed endpoint pivots, with infinity preserved

The completion test uses the original hierarchy on a zero-tail truncation.
Its first successful prefix is an extended natural stopping rank. Causality
identifies every finite completion with the original pivot, without assuming
that unobserved future segments are finite.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open Classical MeasureTheory Set

def completedPivotTest (eps : ℝ) (z : ℕ → ℝ × ℕ) (ell j r : ℕ) : Prop :=
  layerPivot eps (truncPairs z r) ell j ≤ r

def completedPivot (eps : ℝ) (z : ℕ → ℝ × ℕ) (ell j : ℕ) : ℕ∞ :=
  if h : ∃ r, completedPivotTest eps z ell j r then (Nat.find h : ℕ∞) else ⊤

theorem completedPivotTest_mono {eps : ℝ} {z : ℕ → ℝ × ℕ} {ell j r s : ℕ}
    (hrs : r ≤ s) (hr : completedPivotTest eps z ell j r) :
    completedPivotTest eps z ell j s := by
  have hkey : ∀ i ≤ r, pairKeys (truncPairs z r) i = pairKeys (truncPairs z s) i :=
    fun i hi => (pairKeys_truncPairs z r i hi).trans
      (pairKeys_truncPairs z s i (hi.trans hrs)).symm
  have he := layerPivot_eq_of_le (truncPairs_snd z r) (truncPairs_snd z s)
    (allLayersFinite_truncPairs eps z r) hkey ell j hr
  change layerPivot eps (truncPairs z s) ell j ≤ s
  rw [he]
  exact hr.trans hrs

theorem completedPivot_le_iff (eps : ℝ) (z : ℕ → ℝ × ℕ) (ell j r : ℕ) :
    completedPivot eps z ell j ≤ r ↔ completedPivotTest eps z ell j r := by
  unfold completedPivot
  split_ifs with h
  · rw [Nat.cast_le]
    exact ⟨fun hr => completedPivotTest_mono hr (Nat.find_spec h),
      fun hr => Nat.find_min' h hr⟩
  · constructor
    · intro hr
      exact False.elim (ENat.natCast_ne_top r (top_le_iff.mp hr))
    · intro hr
      exact False.elim (h ⟨r, hr⟩)

theorem completedPivot_lt_iff (eps : ℝ) (z : ℕ → ℝ × ℕ) (ell j r : ℕ) :
    (r : ℕ∞) < completedPivot eps z ell j ↔
      r < layerPivot eps (truncPairs z r) ell j := by
  rw [← not_le, completedPivot_le_iff]
  exact not_le

theorem completedPivot_finite_value {eps : ℝ} {z : ℕ → ℝ × ℕ} {ell j r : ℕ}
    (hr : completedPivot eps z ell j = r) :
    layerPivot eps (truncPairs z r) ell j = r := by
  have htest := (completedPivot_le_iff eps z ell j r).mp hr.le
  set k := layerPivot eps (truncPairs z r) ell j
  have hkey : ∀ i ≤ k, pairKeys (truncPairs z r) i = pairKeys (truncPairs z k) i :=
    fun i hi => (pairKeys_truncPairs z r i (hi.trans htest)).trans
      (pairKeys_truncPairs z k i hi).symm
  have he := layerPivot_eq_of_le (truncPairs_snd z r) (truncPairs_snd z k)
    (allLayersFinite_truncPairs eps z r) hkey ell j le_rfl
  have hk : completedPivot eps z ell j ≤ k :=
    (completedPivot_le_iff eps z ell j k).mpr he.le
  rw [hr, Nat.cast_le] at hk
  exact le_antisymm htest hk

theorem completedPivot_eq_original_of_finite {eps : ℝ} {z : ℕ → ℝ × ℕ}
    (hz : ∀ i, (z i).2 = 1) {ell j r : ℕ}
    (hr : completedPivot eps z ell j = r) :
    layerPivot eps z ell j = r := by
  have hv := completedPivot_finite_value hr
  have he := layerPivot_eq_of_le (truncPairs_snd z r) hz
    (allLayersFinite_truncPairs eps z r) (pairKeys_truncPairs z r) ell j hv.le
  exact he.trans hv

theorem completedPivot_eq_of_allLayersFinite {eps : ℝ} {z : ℕ → ℝ × ℕ}
    (hz : ∀ i, (z i).2 = 1) (hfin : AllLayersFinite eps z) (ell j : ℕ) :
    completedPivot eps z ell j = layerPivot eps z ell j := by
  set r := layerPivot eps z ell j
  have hr : completedPivotTest eps z ell j r := by
    have he := layerPivot_eq_of_le hz (truncPairs_snd z r) hfin
      (fun i hi => (pairKeys_truncPairs z r i hi).symm) ell j le_rfl
    exact he.le
  have hle := (completedPivot_le_iff eps z ell j r).mpr hr
  have hne : completedPivot eps z ell j ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top r) hle
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hne
  have he := completedPivot_eq_original_of_finite hz hs.symm
  exact hs.symm.trans (congrArg (fun k : ℕ => (k : ℕ∞)) he.symm)

theorem completedPivot_eq_of_prefix {eps : ℝ} {z z' : ℕ → ℝ × ℕ}
    {ell j r : ℕ} (hgap : ∀ i < r, (z i).1 = (z' i).1)
    (hr : completedPivot eps z ell j = r) :
    completedPivot eps z' ell j = r := by
  have htr (s : ℕ) (hs : s ≤ r) : truncPairs z s = truncPairs z' s := by
    funext i
    by_cases hi : i < s
    · simp only [truncPairs, if_pos hi]
      rw [hgap i (hi.trans_le hs)]
    · simp only [truncPairs, if_neg hi]
  have hle : completedPivot eps z' ell j ≤ r := by
    rw [completedPivot_le_iff, completedPivotTest, ← htr r le_rfl]
    exact (completedPivot_le_iff eps z ell j r).mp hr.le
  apply le_antisymm hle
  by_contra h
  have hlt : completedPivot eps z' ell j < r := lt_of_not_ge h
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp
    (ne_top_of_lt (hlt.trans_le le_top))
  have hsr : s < r := by
    rw [← hs] at hlt
    exact ENat.natCast_lt_natCast.mp hlt
  have htest := (completedPivot_le_iff eps z' ell j s).mp hs.symm.le
  rw [completedPivotTest, ← htr s hsr.le] at htest
  have hzs := (completedPivot_le_iff eps z ell j s).mpr htest
  rw [hr, Nat.cast_le] at hzs
  omega

end

end PGM
