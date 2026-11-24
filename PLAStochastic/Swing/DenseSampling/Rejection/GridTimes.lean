import PLAStochastic.Swing.DenseSampling.CarriedPrefix.CarryCoordinates
import PLAStochastic.Swing.DenseSampling.Segments.Permanence

/-! # Observed rejection grid times and their actual next fitted anchors -/
noncomputable section
open Classical
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

def nativeRejectionAt (t y : ℕ → ℝ) (ε : ℝ) (b : ℕ) : Prop :=
  0 < b ∧ (nativeStream t y ε b).length < (nativeStream t y ε (b+1)).length

def nativeCarryAnchor (t y : ℕ → ℝ) (ε : ℝ) (b : ℕ) : ℝ :=
  nativeSegmentEndpoint t (nativeSegmentAt (nativeStream t y ε b) ((nativeStream t y ε b).length-1))

theorem nativeStream_length_pos_of_pos (t y : ℕ → ℝ) (ε : ℝ) {b : ℕ} (hb : 0 < b) :
    0 < (nativeStream t y ε b).length := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
  exact List.length_pos_iff.mpr (scanNative_ne_nil t y ε n 0 1 (y 0) (by omega))

theorem nativeRejectionAt_dropLast (t y : ℕ → ℝ) (ε : ℝ) {b : ℕ}
    (hb : nativeRejectionAt t y ε b) :
    (nativeStream t y ε (b+1)).dropLast = nativeStream t y ε b := by
  rcases nativeStream_dropLast_succ t y ε b with hn | hy
  · have hl := congrArg List.length hn
    simp only [List.length_dropLast] at hl
    have hp := nativeStream_length_pos_of_pos t y ε hb.1
    have hstep := (nativeStream_length_succ_bounds t y ε b).2
    have hg := hb.2
    omega
  · exact hy

/-- Each observed rejection has a unique actual next segment at every later
horizon. Its anchor is exactly the endpoint of the preceding fitted output. -/
theorem nativeRejectionAt_next (t y : ℕ → ℝ) (ht : StrictMono t) {ε : ℝ} (hε : 0 ≤ ε)
    {b N : ℕ} (hb : nativeRejectionAt t y ε b) (hN : b+1 ≤ N) :
    let k := (nativeStream t y ε b).length
    1 ≤ k ∧ k < (nativeStream t y ε N).length ∧
      (nativeSegmentAt (nativeStream t y ε N) k).start = b ∧
      (nativeSegmentAt (nativeStream t y ε N) k).anchorValue = nativeCarryAnchor t y ε b := by
  let old := nativeStream t y ε b
  let now := nativeStream t y ε (b+1)
  let full := nativeStream t y ε N
  let k := old.length
  have hk : 0 < k := nativeStream_length_pos_of_pos t y ε hb.1
  have hdrop : now.dropLast = old := nativeRejectionAt_dropLast t y ε hb
  have hprefix : old <+: full.dropLast := by
    rw [← hdrop]
    exact nativeStream_dropLast_prefix t y ε hN
  have hlen : k < full.length := by
    have hh := hprefix.length_le
    simp only [List.length_dropLast] at hh
    dsimp only [k]
    omega
  have hprev : nativeSegmentAt full (k-1) = nativeSegmentAt old (k-1) := by
    have hi : k-1 < old.length := by omega
    have hi' : k-1 < full.dropLast.length := hi.trans_le hprefix.length_le
    rw [nativeSegmentAt_eq_getElem (by omega : k-1 < full.length), nativeSegmentAt_eq_getElem hi]
    exact (by simpa only [List.getElem_dropLast] using (hprefix.getElem hi).symm)
  have hc : NativeChain t y ε 0 (y 0) N full := nativeStream_spec t y ht hε N
  have hcold : NativeChain t y ε 0 (y 0) b old := nativeStream_spec t y ht hε b
  have hj := hc.getElem_succ (k := k-1) (by omega : k-1+1 < full.length)
  have heold : (nativeSegmentAt old (k-1)).finish = b := by
    rw [nativeSegmentAt_eq_getElem (by omega : k-1 < old.length)]
    exact hcold.getElem_last_finish (by omega) (by omega)
  have hj' : (nativeSegmentAt full k).start = (nativeSegmentAt full (k-1)).finish ∧
      (nativeSegmentAt full k).anchorValue = nativeSegmentEndpoint t (nativeSegmentAt full (k-1)) := by
    simpa only [Nat.sub_add_cancel hk, nativeSegmentAt_eq_getElem hlen,
      nativeSegmentAt_eq_getElem (by omega : k-1 < full.length)] using hj
  rw [hprev, heold] at hj'
  exact ⟨hk, hlen, hj'.1, hj'.2⟩

/-- Every post-first segment in the actual finite output arises from exactly
such an observed rejection at its inherited start sample. -/
theorem nativeStream_postFirst_rejection (t y : ℕ → ℝ) (ht : StrictMono t) {ε : ℝ}
    (hε : 0 ≤ ε) {N k : ℕ} (hk : 1 ≤ k) (hkN : k < (nativeStream t y ε N).length) :
    nativeRejectionAt t y ε (nativeSegmentAt (nativeStream t y ε N) k).start := by
  have hN : 0 < N := by
    by_contra hn
    have h0 : N = 0 := by omega
    simp only [h0, nativeStream, List.length_nil] at hkN
    omega
  let Y (j : ℕ) (_ : Unit) := y j
  have htime : nativeRecordingTime t Y ε k () ≤ (N-1 : ℕ) := by
    apply (nativeRecordingTime_le_iff t Y ε k (N-1) ()).mpr
    simpa only [Nat.sub_add_cancel hN, Y] using hkN
  have hfinite : nativeRecordingTime t Y ε k () ≠ ⊤ := by
    intro he
    rw [he] at htime
    exact WithTop.not_top_le_coe (N-1) htime
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hfinite
  have hrN : r+1 ≤ N := by
    rw [← hr] at htime
    have : r ≤ N-1 := WithTop.coe_le_coe.mp htime
    omega
  have hend := nativeRecordingTime_eq_native_finish t ht Y hε hk hrN () hr.symm
  have hobs := nativeStream_at_recordingTime t Y ε hk () hr.symm
  have hnow := (nativeRecordingTime_le_iff t Y ε k r ()).mp hr.symm.le
  have hc := nativeStream_spec t y ht hε N
  have hj := hc.getElem_succ (k := k-1) (by omega : k-1+1 < (nativeStream t y ε N).length)
  have hstart : (nativeSegmentAt (nativeStream t y ε N) k).start = r := by
    rw [nativeSegmentAt_eq_getElem hkN]
    have hj' : (nativeStream t y ε N)[k].start =
        (nativeSegmentAt (nativeStream t y ε N) (k-1)).finish := by
      simpa only [Nat.sub_add_cancel hk, nativeSegmentAt_eq_getElem (by omega :
        k-1 < (nativeStream t y ε N).length)] using hj.1
    exact hj'.trans hend
  rw [hstart]
  exact ⟨hobs.1, by simpa only [Y, hobs.2.1] using hnow⟩

end SwingRepair
