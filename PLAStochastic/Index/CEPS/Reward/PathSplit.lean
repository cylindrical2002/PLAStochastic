import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.Defs

/-! # First passage split at the first positive ladder epoch

These are pathwise statements, including paths which never cross the
threshold. They do not assume almost-sure finiteness of either epoch.
-/

noncomputable section
open Set
namespace PGM.WienerHopf

variable {ω : ℕ → ℝ} {x : ℝ} {n m : ℕ}

theorem firstEntry_Ioi_eq_of_asc_above (hx : 0 ≤ x)
    (hn : firstEntry (Ioi 0) ω = n) (hheight : x < partialSum n ω) :
    firstEntry (Ioi x) ω = n := by
  obtain ⟨hn0, _, hbefore⟩ := firstEntry_eq_coe_iff.mp hn
  apply firstEntry_eq_coe_iff.mpr
  refine ⟨hn0, hheight, fun j hj hjn => ?_⟩
  have hj0 : partialSum j ω ≤ 0 := not_lt.mp (hbefore j hj hjn)
  exact not_lt.mpr (hj0.trans hx)

theorem firstEntry_Ioi_eq_add_of_asc_below (hx : 0 ≤ x)
    (hn : firstEntry (Ioi 0) ω = n) (hheight : partialSum n ω ≤ x)
    (hm : firstEntry (Ioi (x - partialSum n ω)) (shift n ω) = m) :
    firstEntry (Ioi x) ω = (n + m : ℕ) := by
  obtain ⟨hn0, _, hbefore⟩ := firstEntry_eq_coe_iff.mp hn
  obtain ⟨hm0, hcross, hafter⟩ := firstEntry_eq_coe_iff.mp hm
  apply firstEntry_eq_coe_iff.mpr
  refine ⟨by omega, ?_, fun j hj hjnm => ?_⟩
  · rw [partialSum_add]
    change x < partialSum n ω + partialSum m (shift n ω)
    change x - partialSum n ω < partialSum m (shift n ω) at hcross
    linarith
  · by_cases hjn : j < n
    · exact not_lt.mpr ((not_lt.mp (hbefore j hj hjn)).trans hx)
    · by_cases hje : j = n
      · subst j
        exact not_lt.mpr hheight
      · have hk0 : 0 < j - n := by omega
        have hkm : j - n < m := by omega
        have hlow : partialSum (j - n) (shift n ω) ≤ x - partialSum n ω :=
          not_lt.mp (hafter (j - n) hk0 hkm)
        rw [show j = n + (j - n) by omega, partialSum_add]
        change ¬x < partialSum n ω + partialSum (j - n) (shift n ω)
        linarith

theorem firstEntry_Ioi_top_of_asc_top (hx : 0 ≤ x)
    (hn : firstEntry (Ioi 0) ω = ⊤) : firstEntry (Ioi x) ω = ⊤ := by
  apply ENat.eq_top_iff_forall_gt.mpr
  intro k
  apply coe_lt_firstEntry_iff.mpr
  intro j hj hjk
  have hb := coe_lt_firstEntry_iff.mp
    (show (k : ℕ∞) < firstEntry (Ioi 0) ω by rw [hn]; exact ENat.natCast_lt_top k)
      j hj hjk
  exact not_lt.mpr ((not_lt.mp hb).trans hx)

theorem firstEntry_Ioi_top_of_shift_top (hx : 0 ≤ x)
    (hn : firstEntry (Ioi 0) ω = n) (hheight : partialSum n ω ≤ x)
    (hm : firstEntry (Ioi (x - partialSum n ω)) (shift n ω) = ⊤) :
    firstEntry (Ioi x) ω = ⊤ := by
  obtain ⟨_, _, hbefore⟩ := firstEntry_eq_coe_iff.mp hn
  apply ENat.eq_top_iff_forall_gt.mpr
  intro k
  apply coe_lt_firstEntry_iff.mpr
  intro j hj _
  by_cases hjn : j < n
  · exact not_lt.mpr ((not_lt.mp (hbefore j hj hjn)).trans hx)
  · by_cases hje : j = n
    · subst j
      exact not_lt.mpr hheight
    · have hk0 : 0 < j - n := by omega
      have hlow := coe_lt_firstEntry_iff.mp
        (show ((j - n : ℕ) : ℕ∞) < firstEntry (Ioi (x - partialSum n ω)) (shift n ω) by
          rw [hm]; exact ENat.natCast_lt_top _) (j - n) hk0 le_rfl
      change ¬x - partialSum n ω < partialSum (j - n) (shift n ω) at hlow
      rw [show j = n + (j - n) by omega, partialSum_add]
      change ¬x < partialSum n ω + partialSum (j - n) (shift n ω)
      linarith

theorem entryOvershoot_eq_shift_of_asc_below (hx : 0 ≤ x)
    (hn : firstEntry (Ioi 0) ω = n) (hheight : partialSum n ω ≤ x)
    (hm : firstEntry (Ioi (x - partialSum n ω)) (shift n ω) = m) :
    entryValue (Ioi x) ω - x =
      entryValue (Ioi (x - partialSum n ω)) (shift n ω) - (x - partialSum n ω) := by
  rw [entryValue_of_eq (firstEntry_Ioi_eq_add_of_asc_below hx hn hheight hm),
    entryValue_of_eq hm, partialSum_add]
  ring

end PGM.WienerHopf
