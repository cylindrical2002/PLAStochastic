import PLAStochastic.Swing.DenseSampling.Segments.FixedIndexLimits

/-! # Permanent recordings persist under online extension -/
noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

theorem scanNative_ne_nil (t y : ℕ → ℝ) (ε : ℝ) (fuel s e : ℕ)
    (q : ℝ) (hse : s < e) : scanNative t y ε fuel s e q hse ≠ [] := by
  induction fuel generalizing s e q with
  | zero => simp only [scanNative, ne_eq, List.cons_ne_self, not_false_eq_true]
  | succ n ih =>
      rw [scanNative]
      split_ifs
      · exact ih _ _ _ _
      · exact List.cons_ne_nil _ _

/-- On one new observation, either the completed list is unchanged, or the
previous EOF line is emitted. Its fit never includes the rejecting sample. -/
theorem scanNative_dropLast_succ (t y : ℕ → ℝ) (ε : ℝ) (fuel s e : ℕ)
    (q : ℝ) (hse : s < e) :
    (scanNative t y ε (fuel + 1) s e q hse).dropLast =
        (scanNative t y ε fuel s e q hse).dropLast ∨
      (scanNative t y ε (fuel + 1) s e q hse).dropLast = scanNative t y ε fuel s e q hse := by
  induction fuel generalizing s e q with
  | zero =>
      by_cases hh : nativePrefixFeasible t y ε s (e + 1) q
      · left
        simp only [scanNative, if_pos hh, List.dropLast_singleton]
      · right
        simp only [scanNative, if_neg hh, List.dropLast_cons_cons, List.dropLast_singleton]
  | succ n ih =>
      by_cases hh : nativePrefixFeasible t y ε s (e + 1) q
      · simpa only [scanNative, if_pos hh] using ih s (e + 1) q (by omega)
      · have heq (j : ℕ) : scanNative t y ε (j + 1) s e q hse =
            nativeOutputSegment t y ε s e q hse ::
              scanNative t y ε j e (e + 1)
                (nativeSegmentEndpoint t (nativeOutputSegment t y ε s e q hse)) (by omega) := by
          rw [scanNative, if_neg hh]
        rw [heq (n + 1), heq n]
        simp only [List.dropLast_cons_of_ne_nil (scanNative_ne_nil t y ε _ _ _ _ _)]
        rcases ih e (e + 1) (nativeSegmentEndpoint t (nativeOutputSegment t y ε s e q hse)) (by omega) with ha | hr
        · exact Or.inl (congrArg (List.cons _) ha)
        · exact Or.inr (congrArg (List.cons _) hr)

theorem nativeStream_dropLast_succ (t y : ℕ → ℝ) (ε : ℝ) (N : ℕ) :
    (nativeStream t y ε (N + 1)).dropLast = (nativeStream t y ε N).dropLast ∨
      (nativeStream t y ε (N + 1)).dropLast = nativeStream t y ε N := by
  cases N with
  | zero => simp only [nativeStream, scanNative, List.dropLast_singleton, List.dropLast_nil, or_self]
  | succ n => exact scanNative_dropLast_succ t y ε n 0 1 (y 0) (by omega)

theorem nativeStream_dropLast_prefix_succ (t y : ℕ → ℝ) (ε : ℝ) (N : ℕ) :
    (nativeStream t y ε N).dropLast <+: (nativeStream t y ε (N + 1)).dropLast := by
  rcases nativeStream_dropLast_succ t y ε N with hn | hr
  · rw [hn]
  · rw [hr]
    exact List.dropLast_prefix _

/-- All previously recorded fitted lines survive every later horizon exactly. -/
theorem nativeStream_dropLast_prefix (t y : ℕ → ℝ) (ε : ℝ) {n N : ℕ} (hn : n ≤ N) :
    (nativeStream t y ε n).dropLast <+: (nativeStream t y ε N).dropLast := by
  induction N, hn using Nat.le_induction with
  | base => rfl
  | succ N hN ih => exact ih.trans (nativeStream_dropLast_prefix_succ t y ε N)

theorem nativeStream_completed_getElem_stable (t y : ℕ → ℝ) (ε : ℝ)
    {n N k : ℕ} (hn : n ≤ N) (hk : k + 1 < (nativeStream t y ε n).length) :
    nativeSegmentAt (nativeStream t y ε n) k = nativeSegmentAt (nativeStream t y ε N) k := by
  have hp := nativeStream_dropLast_prefix t y ε hn
  have hk0 : k < (nativeStream t y ε n).dropLast.length := by simpa only [List.length_dropLast] using (show k < (nativeStream t y ε n).length - 1 by omega)
  have hg := hp.getElem hk0
  have hkN : k < (nativeStream t y ε N).length := by
    have hle := hp.length_le
    simp only [List.length_dropLast] at hle hk0
    omega
  rw [nativeSegmentAt_eq_getElem (by omega : k < (nativeStream t y ε n).length),
    nativeSegmentAt_eq_getElem hkN]
  simpa only [List.getElem_dropLast] using hg

theorem nativeSegmentAt_dropLast {segs : List NativeSegment} {k : ℕ}
    (hk : k + 1 < segs.length) : nativeSegmentAt segs.dropLast k = nativeSegmentAt segs k := by
  have hk' : k < segs.dropLast.length := by simp only [List.length_dropLast]; omega
  rw [nativeSegmentAt_eq_getElem hk', nativeSegmentAt_eq_getElem (by omega : k < segs.length)]
  exact List.getElem_dropLast _

/-- At the exact k-th rejection, the previous EOF fit becomes the k-th
permanent recording. The stopping-time clock counts increments, hence is the
last accepted sample index, while the rejection sample has index r+1. -/
theorem nativeStream_at_recordingTime {Ω : Type*} (t : ℕ → ℝ)
    (Y : ℕ → Ω → ℝ) (ε : ℝ) {k r : ℕ} (hk : 1 ≤ k) (ω : Ω)
    (hr : nativeRecordingTime t Y ε k ω = (r : WithTop ℕ)) :
    0 < r ∧ (nativeStream t (fun j => Y j ω) ε r).length = k ∧
      (nativeStream t (fun j => Y j ω) ε (r + 1)).dropLast =
        nativeStream t (fun j => Y j ω) ε r := by
  have hnow : k < (nativeStream t (fun j => Y j ω) ε (r + 1)).length :=
    (nativeRecordingTime_le_iff t Y ε k r ω).mp (by rw [hr])
  have hrpos : 0 < r := by
    by_contra hn
    have hr0 : r = 0 := by omega
    simp only [hr0, nativeStream, scanNative, List.length_singleton] at hnow
    omega
  have hprev : (nativeStream t (fun j => Y j ω) ε r).length ≤ k := by
    have hn : ¬ nativeRecordingTime t Y ε k ω ≤ (r - 1 : ℕ) := by
      rw [hr]
      exact_mod_cast (show ¬ r ≤ r - 1 by omega)
    rw [nativeRecordingTime_le_iff, Nat.sub_add_cancel hrpos] at hn
    omega
  have hstep := (nativeStream_length_succ_bounds t (fun j => Y j ω) ε r).2
  have hlen : (nativeStream t (fun j => Y j ω) ε r).length = k := by omega
  refine ⟨hrpos, hlen, ?_⟩
  rcases nativeStream_dropLast_succ t (fun j => Y j ω) ε r with hn | hy
  · have hlen' := congrArg List.length hn
    simp only [List.length_dropLast] at hlen'
    omega
  · exact hy

/-- Every permanent segment's endpoint is exactly its rejection stopping-time
clock, identified from the actual online output at any later finite horizon. -/
theorem nativeRecordingTime_eq_native_finish {Ω : Type*} (t : ℕ → ℝ) (ht : StrictMono t)
    (Y : ℕ → Ω → ℝ) {ε : ℝ} (hε : 0 ≤ ε) {k r N : ℕ}
    (hk : 1 ≤ k) (hN : r + 1 ≤ N) (ω : Ω)
    (hr : nativeRecordingTime t Y ε k ω = (r : WithTop ℕ)) :
    (nativeSegmentAt (nativeStream t (fun j => Y j ω) ε N) (k - 1)).finish = r := by
  obtain ⟨_, hlen, hdrop⟩ := nativeStream_at_recordingTime t Y ε hk ω hr
  have hnow : k < (nativeStream t (fun j => Y j ω) ε (r + 1)).length :=
    (nativeRecordingTime_le_iff t Y ε k r ω).mp (by rw [hr])
  have heq := congrArg (fun xs => nativeSegmentAt xs (k - 1)) hdrop
  rw [nativeSegmentAt_dropLast (by omega : k - 1 + 1 <
    (nativeStream t (fun j => Y j ω) ε (r + 1)).length)] at heq
  have hp := nativeStream_completed_getElem_stable t (fun j => Y j ω) ε hN
    (by omega : k - 1 + 1 < (nativeStream t (fun j => Y j ω) ε (r + 1)).length)
  rw [← hp, heq]
  have hkr : k - 1 < (nativeStream t (fun j => Y j ω) ε r).length := by omega
  rw [nativeSegmentAt_eq_getElem hkr]
  exact (nativeStream_spec t (fun j => Y j ω) ht hε r).getElem_last_finish hkr (by omega)

end SwingRepair
