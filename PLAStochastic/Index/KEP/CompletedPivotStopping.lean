import PLAStochastic.Index.KEP.CompletedPivots

/-!
# Natural stopping rules for completed endpoint pivots

Prefix causality gives an extended stopping rank even when future layers have
infinite segments. Finiteness of only the lower layers identifies this rank
with the original algorithm; no higher-layer finiteness is assumed.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open Classical MeasureTheory Set

theorem measurable_truncPairs (r : ℕ) :
    Measurable (fun z : ℕ → ℝ × ℕ => truncPairs z r) := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases hi : i < r
  · simp only [truncPairs, if_pos hi]
    exact (measurable_fst.comp (measurable_pi_apply i)).prodMk measurable_const
  · simp only [truncPairs, if_neg hi]
    exact measurable_const

theorem isStoppingRule_completedPivot_of_prefix {E : Type*} [MeasurableSpace E]
    {z : (ℕ → E) → ℕ → ℝ × ℕ} (hz : Measurable z) (eps : ℝ) (ell j : ℕ)
    (hp : ∀ r g g', (∀ i < r, g i = g' i) →
      ∀ i < r, (z g i).1 = (z g' i).1) :
    IsStoppingRule (fun g => completedPivot eps (z g) ell j) := by
  intro r
  have hm : Measurable (fun g => layerPivot eps (truncPairs (z g) r) ell j) :=
    (measurable_layerPivot eps ell j).comp ((measurable_truncPairs r).comp hz)
  have he : {g | (r : ℕ∞) < completedPivot eps (z g) ell j} =
      {g | r < layerPivot eps (truncPairs (z g) r) ell j} := by
    ext g
    exact completedPivot_lt_iff eps (z g) ell j r
  rw [he]
  apply measurableSet_comap_seqPrefix_of_agree
    (measurableSet_lt measurable_const hm)
  intro g g' hagree hgr
  have ht : truncPairs (z g) r = truncPairs (z g') r := by
    funext i
    by_cases hi : i < r
    · simp only [truncPairs, if_pos hi]
      rw [hp r g g' hagree i hi]
    · simp only [truncPairs, if_neg hi]
  change r < layerPivot eps (truncPairs (z g') r) ell j
  rw [← ht]
  exact hgr

theorem layerPivot_eq_of_le_of_lower_layers_finite {eps : ℝ}
    {z z' : ℕ → ℝ × ℕ} (hz : ∀ i, (z i).2 = 1) (hz' : ∀ i, (z' i).2 = 1)
    {r : ℕ} (hkey : ∀ i ≤ r, pairKeys z i = pairKeys z' i) :
    ∀ ell, (∀ k < ell, AllSegmentsFinite eps (pairLayer eps k z)) →
      ∀ j, layerPivot eps z ell j ≤ r →
        layerPivot eps z' ell j = layerPivot eps z ell j
  | 0, _, j, _ => by rw [layerPivot_zero hz, layerPivot_zero hz']
  | ell + 1, hfin, j, hj => by
    have ih := layerPivot_eq_of_le_of_lower_layers_finite hz hz' hkey ell
      (fun k hk => hfin k (hk.trans (Nat.lt_succ_self ell)))
    rw [layerPivot_succ] at hj ⊢
    rw [layerPivot_succ]
    have hkw : ∀ i ≤ blockStart eps (pairLayer eps ell z) j,
        pairKeys (pairLayer eps ell z) i = pairKeys (pairLayer eps ell z') i := by
      intro i hi
      have hpi : layerPivot eps z ell i ≤ r := (layerPivot_mono eps z ell hi).trans hj
      rw [pairKeys_pairLayer hz, pairKeys_pairLayer hz', ih i hpi, hkey _ hpi]
    rw [blockStart_eq_of_pairKeys_eq (hfin ell (Nat.lt_succ_self ell)) hkw j le_rfl, ih _ hj]

theorem completedPivot_eq_of_lower_layers_finite {eps : ℝ} {z : ℕ → ℝ × ℕ}
    (hz : ∀ i, (z i).2 = 1) (ell : ℕ)
    (hfin : ∀ k < ell, AllSegmentsFinite eps (pairLayer eps k z)) (j : ℕ) :
    completedPivot eps z ell j = layerPivot eps z ell j := by
  set r := layerPivot eps z ell j
  have he := layerPivot_eq_of_le_of_lower_layers_finite hz (truncPairs_snd z r)
    (fun i hi => (pairKeys_truncPairs z r i hi).symm) ell hfin j le_rfl
  have hle : completedPivot eps z ell j ≤ r :=
    (completedPivot_le_iff eps z ell j r).mpr he.le
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp
    (ne_top_of_le_ne_top (ENat.natCast_ne_top r) hle)
  have hv := completedPivot_eq_original_of_finite hz hs.symm
  exact hs.symm.trans (congrArg (fun k : ℕ => (k : ℕ∞)) hv.symm)

theorem completedPivot_mono_key {eps : ℝ} {z : ℕ → ℝ × ℕ}
    (ell : ℕ) {i j : ℕ} (hij : i ≤ j) :
    completedPivot eps z ell i ≤ completedPivot eps z ell j := by
  by_cases htop : completedPivot eps z ell j = ⊤
  · rw [htop]
    exact le_top
  · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp htop
    have hr' : completedPivot eps z ell j = (r : ℕ∞) := hr.symm
    have ht := (completedPivot_le_iff eps z ell j r).mp hr'.le
    have hi : completedPivotTest eps z ell i r :=
      (layerPivot_mono eps (truncPairs z r) ell hij).trans ht
    rw [hr']
    exact (completedPivot_le_iff eps z ell i r).mpr hi

end

end PGM
