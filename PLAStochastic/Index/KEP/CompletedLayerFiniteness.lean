import PLAStochastic.Index.KEP.CompletedPivotRestart

/-!
# Finite completed ranks imply finiteness of the original parent segments

Completed ranks increase strictly whenever the later rank is finite.
If every completed pivot of a layer is finite, an infinite segment in the
preceding original layer would repeat its next pivot, contradicting this
strict increase. Thus the conclusion concerns the original hierarchy.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

theorem completedPivot_strict_lt_of_finite {eps : ℝ} (heps : 0 ≤ eps)
    {z : ℕ → ℝ × ℕ} (ell : ℕ) {i j r : ℕ} (hij : i < j)
    (hr : completedPivot eps z ell j = r) :
    completedPivot eps z ell i < completedPivot eps z ell j := by
  have hi : completedPivot eps z ell i ≤ r :=
    (completedPivot_mono_key ell hij.le).trans hr.le
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp
    (ne_top_of_le_ne_top (ENat.natCast_ne_top r) hi)
  have hs' : completedPivot eps z ell i = (s : ℕ∞) := hs.symm
  have hsr : s ≤ r := by
    rw [hs'] at hi
    exact ENat.natCast_le_natCast.mp hi
  have hwi : completedPivot eps (truncPairs z r) ell i = s := by
    apply completedPivot_eq_of_prefix (z := z) _ hs'
    intro k hk
    simp only [truncPairs, if_pos (hk.trans_le hsr)]
  have hwr : completedPivot eps (truncPairs z r) ell j = r := by
    apply completedPivot_eq_of_prefix (z := z) _ hr
    intro k hk
    simp only [truncPairs, if_pos hk]
  have hpi := completedPivot_eq_original_of_finite (truncPairs_snd z r) hwi
  have hpj := completedPivot_eq_original_of_finite (truncPairs_snd z r) hwr
  have hlt := layerPivot_strictMono heps (truncPairs_snd z r)
    (allLayersFinite_truncPairs eps z r) ell hij
  rw [hpi, hpj] at hlt
  rw [hs', hr]
  exact ENat.natCast_lt_natCast.mpr hlt

theorem layerPivot_strictMono_of_completed_finite {eps : ℝ} (heps : 0 ≤ eps)
    {z : ℕ → ℝ × ℕ} (hz : ∀ i, (z i).2 = 1) (ell : ℕ)
    (hfin : ∀ i, completedPivot eps z ell i ≠ ⊤) :
    StrictMono (layerPivot eps z ell) := by
  intro i j hij
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp (hfin j)
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp (hfin i)
  have hr' : completedPivot eps z ell j = (r : ℕ∞) := hr.symm
  have hs' : completedPivot eps z ell i = (s : ℕ∞) := hs.symm
  have hlt := completedPivot_strict_lt_of_finite heps ell hij hr'
  rw [hr', hs', ENat.natCast_lt_natCast] at hlt
  rw [completedPivot_eq_original_of_finite hz hs',
    completedPivot_eq_original_of_finite hz hr']
  exact hlt

theorem allSegmentsFinite_of_completedPivot_finite {eps : ℝ} (heps : 0 ≤ eps)
    {z : ℕ → ℝ × ℕ} (hz : ∀ i, (z i).2 = 1) (ell : ℕ)
    (hfin : ∀ i, completedPivot eps z (ell + 1) i ≠ ⊤) :
    AllSegmentsFinite eps (pairLayer eps ell z) := by
  have hstrict := layerPivot_strictMono_of_completed_finite heps hz (ell + 1) hfin
  intro i htop
  have hlt := hstrict (Nat.lt_succ_self i)
  rw [layerPivot_succ, layerPivot_succ, blockStart_succ, htop,
    ENat.toNat_top, Nat.add_zero] at hlt
  exact (lt_irrefl _ hlt)

end

end PGM
