import PLAStochastic.Swing.Algorithm.Causality
import PLAStochastic.Swing.Repair.FirstRejectionStopping

/-!
# Measurability of actual native output and repeated recording times

The finite output is encoded without loss by its length and every segment's
four fields. The proof follows the actual fitted-anchor accept/reject recursion.
The time of the k-th permanent recording is read from the actual output length;
the final open segment at EOF is not counted as a permanent recording.
-/

namespace SwingRepair

noncomputable section
open Classical MeasureTheory ProbabilityTheory
set_option backward.isDefEq.respectTransparency false

/-- Product coordinates of an actual emitted segment. -/
def nativeSegmentCode (seg : NativeSegment) : ℕ × ℕ × ℝ × ℝ :=
  (seg.start, seg.finish, seg.anchorValue, seg.slope)

/-- A countable product encoding of the complete finite output. -/
def nativeOutputCode (segments : List NativeSegment) : ℕ × (ℕ → ℕ × ℕ × ℝ × ℝ) :=
  (segments.length, fun k => nativeSegmentCode (segments.getD k ⟨0, 0, 0, 0⟩))

theorem nativeSegmentCode_injective : Function.Injective nativeSegmentCode := by
  rintro ⟨s, e, q, a⟩ ⟨s', e', q', a'⟩ h
  simp only [nativeSegmentCode, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl, rfl, rfl⟩
  rfl

theorem nativeOutputCode_injective : Function.Injective nativeOutputCode := by
  intro l l' h
  have hlen := congrArg Prod.fst h
  have hget := congrArg Prod.snd h
  apply List.ext_getElem hlen
  intro i hi hi'
  apply nativeSegmentCode_injective
  have heq := congrFun hget i
  simpa only [nativeOutputCode, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hi', Option.getD_some] using heq

variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurable_nativeOutputCode_cons {g : Ω → NativeSegment}
    {l : Ω → List NativeSegment} (hg : Measurable (fun ω => nativeSegmentCode (g ω)))
    (hl : Measurable (fun ω => nativeOutputCode (l ω))) :
    Measurable (fun ω => nativeOutputCode (g ω :: l ω)) := by
  refine (hl.fst.add_const 1).prodMk (measurable_pi_lambda _ fun k => ?_)
  cases k with
  | zero => simpa only [List.getD_cons_zero] using hg
  | succ k =>
      simpa only [List.getD_cons_succ, nativeOutputCode, Function.comp_def] using!
        (measurable_pi_apply k).comp hl.snd

theorem measurable_nativeConeLower {ι : Type*} (samples : Finset ι)
    (hne : samples.Nonempty) (t : ι → ℝ) (Y : ι → Ω → ℝ) (a ε : ℝ)
    {Q : Ω → ℝ} (hQ : Measurable Q) (hY : ∀ i ∈ samples, Measurable (Y i)) :
    Measurable (fun ω => nativeConeLower samples hne t (fun i => Y i ω) a (Q ω) ε) := by
  have h : Measurable (samples.sup' hne
      (fun i ω => (Y i ω - Q ω - ε) / (t i - a))) :=
    Finset.measurable_sup' hne (fun i hi => (((hY i hi).sub hQ).sub_const ε).div_const _)
  convert h using 1
  ext ω
  simp only [nativeConeLower, slopeLower, Finset.sup'_apply]

theorem measurable_nativeConeUpper {ι : Type*} (samples : Finset ι)
    (hne : samples.Nonempty) (t : ι → ℝ) (Y : ι → Ω → ℝ) (a ε : ℝ)
    {Q : Ω → ℝ} (hQ : Measurable Q) (hY : ∀ i ∈ samples, Measurable (Y i)) :
    Measurable (fun ω => nativeConeUpper samples hne t (fun i => Y i ω) a (Q ω) ε) := by
  have h : Measurable (samples.inf' hne
      (fun i ω => (Y i ω - Q ω + ε) / (t i - a))) :=
    Finset.measurable_sup' (α := ℝᵒᵈ) hne
      (fun i hi => (((hY i hi).sub hQ).add_const ε).div_const _)
  convert h using 1
  ext ω
  simp only [nativeConeUpper, slopeUpper, Finset.inf'_apply]

theorem measurable_nativeSelectedSlope {ι : Type*} (samples : Finset ι)
    (hne : samples.Nonempty) (t : ι → ℝ) (Y : ι → Ω → ℝ) (a ε : ℝ)
    {Q : Ω → ℝ} (hQ : Measurable Q) (hY : ∀ i ∈ samples, Measurable (Y i)) :
    Measurable (fun ω => nativeSelectedSlope samples hne t (fun i => Y i ω) a (Q ω) ε) := by
  have hC : Measurable (fun ω => nativeSSECross samples t (fun i => Y i ω) a (Q ω)) := by
    apply Finset.measurable_sum
    intro i hi
    exact ((hY i hi).sub hQ).const_mul _
  exact (measurable_nativeConeLower samples hne t Y a ε hQ hY).max
    ((hC.div_const (nativeSSETimeSquare samples t a)).min
      (measurable_nativeConeUpper samples hne t Y a ε hQ hY))

theorem nativePrefixFeasible_measurableSet (t : ℕ → ℝ) (ht : StrictMono t)
    (Y : ℕ → Ω → ℝ) (ε : ℝ) (s e : ℕ) (hse : s < e)
    {Q : Ω → ℝ} (hQ : Measurable Q)
    (hY : ∀ i ∈ Finset.Icc (s + 1) e, Measurable (Y i)) :
    MeasurableSet {ω | nativePrefixFeasible t (fun i => Y i ω) ε s e (Q ω)} := by
  have hne : (Finset.Icc (s + 1) e).Nonempty := Finset.nonempty_Icc.mpr hse
  have heq : {ω | nativePrefixFeasible t (fun i => Y i ω) ε s e (Q ω)} =
      {ω | nativeConeLower (Finset.Icc (s + 1) e) hne t (fun i => Y i ω) (t s) (Q ω) ε ≤
        nativeConeUpper (Finset.Icc (s + 1) e) hne t (fun i => Y i ω) (t s) (Q ω) ε} := by
    ext ω
    exact nativeCone_nonempty_iff _ hne _ _ _ _ _ (fun i hi => ht (Finset.mem_Icc.mp hi).1)
  rw [heq]
  exact measurableSet_le (measurable_nativeConeLower _ hne t Y (t s) ε hQ hY)
    (measurable_nativeConeUpper _ hne t Y (t s) ε hQ hY)

theorem measurable_nativeOutputSegment (t : ℕ → ℝ) (Y : ℕ → Ω → ℝ)
    (ε : ℝ) (s e : ℕ) (hse : s < e) {Q : Ω → ℝ} (hQ : Measurable Q)
    (hY : ∀ i ∈ Finset.Icc (s + 1) e, Measurable (Y i)) :
    Measurable (fun ω => nativeSegmentCode (nativeOutputSegment t (fun i => Y i ω)
      ε s e (Q ω) hse)) := by
  exact measurable_const.prodMk (measurable_const.prodMk
    (hQ.prodMk (measurable_nativeSelectedSlope _ _ t Y (t s) ε hQ hY)))

/-- All four fields of all segments are measurable in the available observations. -/
theorem measurable_scanNative_output (t : ℕ → ℝ) (ht : StrictMono t)
    (Y : ℕ → Ω → ℝ) (ε : ℝ) (fuel s e : ℕ) (hse : s < e) {N : ℕ}
    (hN : e + fuel ≤ N) {Q : Ω → ℝ} (hQ : Measurable Q)
    (hY : ∀ i ≤ N, Measurable (Y i)) :
    Measurable (fun ω => nativeOutputCode
      (scanNative t (fun i => Y i ω) ε fuel s e (Q ω) hse)) := by
  induction fuel generalizing s e Q with
  | zero =>
      exact measurable_nativeOutputCode_cons
        (measurable_nativeOutputSegment t Y ε s e hse hQ
          (fun i hi => hY i ((Finset.mem_Icc.mp hi).2.trans (by omega)))) measurable_const
  | succ fuel ih =>
      have hcond := nativePrefixFeasible_measurableSet t ht Y ε s (e + 1)
        (by omega) hQ (fun i hi => hY i ((Finset.mem_Icc.mp hi).2.trans (by omega)))
      have ha := ih s (e + 1) (by omega) (by omega) hQ
      have hseg := measurable_nativeOutputSegment t Y ε s e hse hQ
        (fun i hi => hY i ((Finset.mem_Icc.mp hi).2.trans (by omega)))
      have hend : Measurable (fun ω => nativeSegmentEndpoint t
          (nativeOutputSegment t (fun i => Y i ω) ε s e (Q ω) hse)) := by
        exact hQ.add (hseg.snd.snd.snd.mul_const (t e - t s))
      have hr := measurable_nativeOutputCode_cons hseg
        (ih e (e + 1) (by omega) (by omega) hend)
      simpa only [scanNative, apply_ite nativeOutputCode] using ha.ite hcond hr

theorem measurable_nativeStream_output (t : ℕ → ℝ) (ht : StrictMono t)
    (Y : ℕ → Ω → ℝ) (ε : ℝ) (last : ℕ)
    (hY : ∀ i ≤ last, Measurable (Y i)) :
    Measurable (fun ω => nativeOutputCode (nativeStream t (fun i => Y i ω) ε last)) := by
  cases last with
  | zero => simpa only [nativeStream] using (measurable_const (a := nativeOutputCode []))
  | succ n =>
      exact measurable_scanNative_output t ht Y ε n 0 1 (by omega) (by omega)
        (hY 0 (Nat.zero_le _)) hY

/-- One additional observation emits at most one new permanent segment. -/
theorem scanNative_length_succ_bounds (t y : ℕ → ℝ) (ε : ℝ)
    (fuel s e : ℕ) (q : ℝ) (hse : s < e) :
    (scanNative t y ε fuel s e q hse).length ≤
        (scanNative t y ε (fuel + 1) s e q hse).length ∧
      (scanNative t y ε (fuel + 1) s e q hse).length ≤
        (scanNative t y ε fuel s e q hse).length + 1 := by
  induction fuel generalizing s e q with
  | zero =>
      by_cases hc : nativePrefixFeasible t y ε s (e + 1) q
      · simp only [scanNative, if_pos hc, List.length_singleton]
        omega
      · simp only [scanNative, if_neg hc, List.length_cons]
        omega
  | succ fuel ih =>
      by_cases hc : nativePrefixFeasible t y ε s (e + 1) q
      · simpa only [scanNative, if_pos hc] using ih s (e + 1) q (by omega)
      · have h := ih e (e + 1)
          (nativeSegmentEndpoint t (nativeOutputSegment t y ε s e q hse)) (by omega)
        simpa only [scanNative, if_neg hc, List.length_cons, Nat.add_le_add_iff_right] using h

theorem nativeStream_length_succ_bounds (t y : ℕ → ℝ) (ε : ℝ) (last : ℕ) :
    (nativeStream t y ε last).length ≤ (nativeStream t y ε (last + 1)).length ∧
      (nativeStream t y ε (last + 1)).length ≤ (nativeStream t y ε last).length + 1 := by
  cases last with
  | zero => simp only [nativeStream, scanNative, List.length_nil, List.length_singleton]; omega
  | succ n => exact scanNative_length_succ_bounds t y ε n 0 1 (y 0) (by omega)

theorem nativeStream_length_monotone (t y : ℕ → ℝ) (ε : ℝ) :
    Monotone (fun last => (nativeStream t y ε last).length) :=
  monotone_nat_of_le_succ (fun last => (nativeStream_length_succ_bounds t y ε last).1)

theorem nativeStream_length_le_last (t y : ℕ → ℝ) (ε : ℝ) (last : ℕ) :
    (nativeStream t y ε last).length ≤ last := by
  induction last with
  | zero => rfl
  | succ n ih => exact (nativeStream_length_succ_bounds t y ε n).2.trans (Nat.add_le_add_right ih 1)

/-- The k-th permanent recording has occurred once the actual output has more
than k segments. At positive horizons the last segment is the unfinished EOF fit. -/
def nativeRecordingObserved (t : ℕ → ℝ) (Y : ℕ → Ω → ℝ) (ε : ℝ) (k n : ℕ)
    (ω : Ω) : Prop := k < (nativeStream t (fun i => Y i ω) ε (n + 1)).length

/-- All repeated native recording times, with infinity retained for absent recordings.
Actual recordings use k ≥ 1; k = 0 is the conventional initial time.
Time n means that increments through n, hence samples through n+1, have been observed. -/
def nativeRecordingTime (t : ℕ → ℝ) (Y : ℕ → Ω → ℝ) (ε : ℝ) (k : ℕ) : Ω → WithTop ℕ :=
  hittingAfter (nativeRecordingObserved t Y ε k) {True} 0

omit [MeasurableSpace Ω] in
theorem nativeRecordingTime_le_iff (t : ℕ → ℝ) (Y : ℕ → Ω → ℝ)
    (ε : ℝ) (k n : ℕ) (ω : Ω) :
    nativeRecordingTime t Y ε k ω ≤ n ↔
      k < (nativeStream t (fun i => Y i ω) ε (n + 1)).length := by
  have hh : nativeRecordingTime t Y ε k ω ≤ n ↔
      ∃ j ≤ n, nativeRecordingObserved t Y ε k j ω := by
    simpa [nativeRecordingTime] using
      (hittingAfter_le_iff (u := nativeRecordingObserved t Y ε k)
        (s := {True}) (n := 0) (i := n) (ω := ω))
  rw [hh]
  constructor
  · rintro ⟨j, hj, hrec⟩
    exact hrec.trans_le (nativeStream_length_monotone t (fun i => Y i ω) ε (by omega))
  · intro h
    exact ⟨n, le_rfl, h⟩

omit [MeasurableSpace Ω] in
theorem nativeRecordingTime_eq_top_iff (t : ℕ → ℝ) (Y : ℕ → Ω → ℝ)
    (ε : ℝ) (k : ℕ) (ω : Ω) :
    nativeRecordingTime t Y ε k ω = ⊤ ↔
      ∀ n, (nativeStream t (fun i => Y i ω) ε (n + 1)).length ≤ k := by
  simp only [nativeRecordingTime, hittingAfter_eq_top_iff, nativeRecordingObserved,
    Set.mem_singleton_iff, eq_iff_iff, iff_true, not_lt, Nat.zero_le, forall_true_left]

theorem nativeRecordingTime_isStoppingTime (t : ℕ → ℝ) (ht : StrictMono t)
    (Y : ℕ → Ω → ℝ) (ε : ℝ) (k : ℕ) (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (hY : ∀ n, ∀ i ≤ n + 1, Measurable[ℱ n] (Y i)) :
    IsStoppingTime ℱ (nativeRecordingTime t Y ε k) := by
  intro n
  have hlen : Measurable[ℱ n]
      (fun ω => (nativeStream t (fun i => Y i ω) ε (n + 1)).length) :=
    (@measurable_nativeStream_output Ω (ℱ n) t ht Y ε (n + 1) (hY n)).fst
  have heq : {ω | nativeRecordingTime t Y ε k ω ≤ n} =
      {ω | k < (nativeStream t (fun i => Y i ω) ε (n + 1)).length} := by
    ext ω
    exact nativeRecordingTime_le_iff t Y ε k n ω
  exact (measurableSet_lt measurable_const hlen).congr heq.symm

/-- Every actual native recording time is a stopping time for the observed increments. -/
theorem nativeRecordingTime_isStoppingTime_increment (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (ε : ℝ) (k : ℕ) :
    IsStoppingTime (incrementFiltration X hX)
      (nativeRecordingTime (fun i => (i : ℝ)) (cumulativeSamples X) ε k) := by
  apply nativeRecordingTime_isStoppingTime _ (fun i j hij => by exact_mod_cast hij)
  intro n i hi
  exact cumulativeSamples_measurable_at hX hi

end

end SwingRepair
