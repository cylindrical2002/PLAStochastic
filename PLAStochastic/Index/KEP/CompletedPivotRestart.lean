import PLAStochastic.Index.KEP.CompletedPivotStopping
import PLAStochastic.Index.KEP.PivotRestart

/-!
# Successive finite completions restart the original hierarchy

Two finite completed ranks concatenate to a finite next pivot. The proof
works entirely on the observed zero-tail truncation and uses the original
pointwise layer restart identity. It does not require future finiteness.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory Set

theorem completedPivot_zero (eps : ℝ) (z : ℕ → ℝ × ℕ) (ell : ℕ) :
    completedPivot eps z ell 0 = 0 := by
  apply le_antisymm
  exact (completedPivot_le_iff eps z ell 0 0).mpr (by simp [completedPivotTest, layerPivot, pairRank])
  exact zero_le

theorem completedPivot_zero_layer (eps : ℝ) (z : ℕ → ℝ × ℕ) (j : ℕ) :
    completedPivot eps z 0 j = j := by
  have hj : completedPivot eps z 0 j ≤ j :=
    (completedPivot_le_iff eps z 0 j j).mpr (by
      rw [completedPivotTest, layerPivot_zero (truncPairs_snd z j)])
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp
    (ne_top_of_le_ne_top (ENat.natCast_ne_top j) hj)
  have hr' : completedPivot eps z 0 j = (r : ℕ∞) := hr.symm
  have hv := completedPivot_finite_value hr'
  rw [layerPivot_zero (truncPairs_snd z r)] at hv
  rw [hr', hv]

theorem completedPivot_succ_of_finite_restarts {eps : ℝ} {z : ℕ → ℝ × ℕ}
    (hz : ∀ i, (z i).2 = 1) {ell i r s : ℕ}
    (hr : completedPivot eps z ell i = r)
    (hs : completedPivot eps (fun k => z (r + k)) ell 1 = s) :
    completedPivot eps z ell (i + 1) = (r + s : ℕ) := by
  let w := truncPairs z (r + s)
  have hw : AllLayersFinite eps w := allLayersFinite_truncPairs eps z (r + s)
  have hwr : completedPivot eps w ell i = r := by
    apply completedPivot_eq_of_prefix (z := z) _ hr
    intro k hk
    simp only [w, truncPairs, if_pos (show k < r + s by omega)]
  have hpi : layerPivot eps w ell i = r :=
    completedPivot_eq_original_of_finite (truncPairs_snd z (r + s)) hwr
  have hws : completedPivot eps (fun k => w (r + k)) ell 1 = s := by
    apply completedPivot_eq_of_prefix (z := fun k => z (r + k)) _ hs
    intro k hk
    simp only [w, truncPairs, if_pos (show r + k < r + s by omega)]
  have hp1 : layerPivot eps (fun k => w (r + k)) ell 1 = s :=
    completedPivot_eq_original_of_finite (fun k => truncPairs_snd z (r + s) (r + k)) hws
  have hpnext : layerPivot eps w ell (i + 1) = r + s := by
    rw [layerPivot_shift (truncPairs_snd z (r + s)) ell i 1, hpi, hp1]
  have hsmall : completedPivot eps z ell (i + 1) ≤ (r + s : ℕ) :=
    (completedPivot_le_iff eps z ell (i + 1) (r + s)).mpr hpnext.le
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp
    (ne_top_of_le_ne_top (ENat.natCast_ne_top (r + s)) hsmall)
  have hq' : completedPivot eps z ell (i + 1) = (q : ℕ∞) := hq.symm
  have hpq := completedPivot_eq_original_of_finite hz hq'
  have hpr := completedPivot_eq_original_of_finite hz hr
  have hps := completedPivot_eq_original_of_finite (fun k => hz (r + k)) hs
  have hval : layerPivot eps z ell (i + 1) = r + s := by
    rw [layerPivot_shift hz ell i 1, hpr, hps]
  have he : q = r + s := hpq.symm.trans hval
  rw [hq', he]

end

end PGM
