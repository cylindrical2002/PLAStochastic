import PLAStochastic.Index.KEP.CompletedLayerFiniteness

/-!
# A finite original child stopping block completes its true parent pivot

Only the completed child ranks up to the stopping rank are used. Their
finite observed prefixes reproduce the original child keys, so the actual
failed prefix also appears in the base truncation. No finiteness of an
unobserved parent segment or of a future layer is required.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

theorem completedPivot_parent_of_child_stop {eps : ℝ} {z : ℕ → ℝ × ℕ}
    (hz : ∀ i, (z i).2 = 1) {ell t r : ℕ}
    (ht : pairSegLen eps (pairLayer eps ell z) = (t : ℕ∞))
    (hr : completedPivot eps z ell t = (r : ℕ∞)) :
    completedPivot eps z (ell + 1) 1 = (r : ℕ∞) := by
  let w := truncPairs z r
  have hkey : ∀ k ≤ t, pairKeys (pairLayer eps ell z) k =
      pairKeys (pairLayer eps ell w) k := by
    intro k hk
    have hkr : completedPivot eps z ell k ≤ r :=
      (completedPivot_mono_key ell hk).trans hr.le
    obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp
      (ne_top_of_le_ne_top (ENat.natCast_ne_top r) hkr)
    have hs' : completedPivot eps z ell k = (s : ℕ∞) := hs.symm
    have hsr : s ≤ r := by rw [hs'] at hkr; exact ENat.natCast_le_natCast.mp hkr
    have hws : completedPivot eps w ell k = (s : ℕ∞) := by
      apply completedPivot_eq_of_prefix (z := z) _ hs'
      intro a ha
      simp only [w, truncPairs, if_pos (ha.trans_le hsr)]
    rw [pairKeys_pairLayer hz, pairKeys_pairLayer (truncPairs_snd z r),
      completedPivot_eq_original_of_finite hz hs',
      completedPivot_eq_original_of_finite (truncPairs_snd z r) hws]
    exact (pairKeys_truncPairs z r s hsr).symm
  have htw : pairSegLen eps (pairLayer eps ell w) = (t : ℕ∞) :=
    segLen_eq_of_eq_natCast ht hkey
  have hpw : layerPivot eps w (ell + 1) 1 = r := by
    rw [layerPivot_succ]
    have hb : blockStart eps (pairLayer eps ell w) 1 = t := by
      simp only [blockStart, Finset.sum_range_one, Function.iterate_zero_apply,
        htw, ENat.toNat_natCast]
    rw [hb]
    exact completedPivot_finite_value hr
  have hle : completedPivot eps z (ell + 1) 1 ≤ r :=
    (completedPivot_le_iff eps z (ell + 1) 1 r).mpr hpw.le
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp
    (ne_top_of_le_ne_top (ENat.natCast_ne_top r) hle)
  have hs' : completedPivot eps z (ell + 1) 1 = (s : ℕ∞) := hs.symm
  have hpz : layerPivot eps z (ell + 1) 1 = r := by
    rw [layerPivot_succ]
    have hb : blockStart eps (pairLayer eps ell z) 1 = t := by
      simp only [blockStart, Finset.sum_range_one, Function.iterate_zero_apply,
        ht, ENat.toNat_natCast]
    rw [hb]
    exact completedPivot_eq_original_of_finite hz hr
  have he : s = r := (completedPivot_eq_original_of_finite hz hs').symm.trans hpz
  rw [hs', he]

theorem completedPivot_parent_finite_of_child_stop {eps : ℝ} {z : ℕ → ℝ × ℕ}
    (hz : ∀ i, (z i).2 = 1) (ell : ℕ)
    (ht : pairSegLen eps (pairLayer eps ell z) ≠ ⊤)
    (hfin : ∀ i, completedPivot eps z ell i ≠ ⊤) :
    completedPivot eps z (ell + 1) 1 ≠ ⊤ := by
  obtain ⟨t, ht'⟩ := WithTop.ne_top_iff_exists.mp ht
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp (hfin t)
  rw [completedPivot_parent_of_child_stop hz ht'.symm hr.symm]
  exact ENat.natCast_ne_top r

end

end PGM
