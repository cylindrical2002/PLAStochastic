import PLAStochastic.Swing.Algorithm.Cone

/-!
# The actual finite native Swing recursion

Each accepted prefix uses a fitted recording as its anchor. Rejection emits
the old constrained-SSE line at the last accepted sample and carries the
rejected sample into the new prefix. The old loss excludes that sample.
-/

namespace SwingRepair

noncomputable section
open Classical
set_option backward.isDefEq.respectTransparency false

structure NativeSegment where
  start : ℕ
  finish : ℕ
  anchorValue : ℝ
  slope : ℝ

def nativePrefixFeasible (t y : ℕ → ℝ) (ε : ℝ) (s e : ℕ) (q : ℝ) : Prop :=
  ∃ m, feasibleSlope (Finset.Icc (s + 1) e) t y (t s) q ε m

def nativeOutputSegment (t y : ℕ → ℝ) (ε : ℝ) (s e : ℕ) (q : ℝ)
    (hse : s < e) : NativeSegment :=
  ⟨s, e, q, nativeSelectedSlope (Finset.Icc (s + 1) e)
    (Finset.nonempty_Icc.mpr (Nat.succ_le_of_lt hse)) t y (t s) q ε⟩

def nativeSegmentEndpoint (t : ℕ → ℝ) (seg : NativeSegment) : ℝ :=
  seg.anchorValue + seg.slope * (t seg.finish - t seg.start)

def scanNative (t y : ℕ → ℝ) (ε : ℝ) :
    (fuel s e : ℕ) → (q : ℝ) → (hse : s < e) → List NativeSegment
  | 0, s, e, q, hse => [nativeOutputSegment t y ε s e q hse]
  | fuel + 1, s, e, q, hse =>
    if nativePrefixFeasible t y ε s (e + 1) q then
      scanNative t y ε fuel s (e + 1) q (hse.trans (Nat.lt_succ_self e))
    else
      let seg := nativeOutputSegment t y ε s e q hse
      seg :: scanNative t y ε fuel e (e + 1) (nativeSegmentEndpoint t seg) (Nat.lt_succ_self e)

/-- Input samples are indexed `0,...,last`, including the true initial anchor. -/
def nativeStream (t y : ℕ → ℝ) (ε : ℝ) : ℕ → List NativeSegment
  | 0 => []
  | n + 1 => scanNative t y ε n 0 1 (y 0) (by omega)

structure NativeSegmentValid (t y : ℕ → ℝ) (ε : ℝ) (seg : NativeSegment) : Prop where
  positive : seg.start < seg.finish
  feasible : feasibleSlope (Finset.Icc (seg.start + 1) seg.finish) t y
    (t seg.start) seg.anchorValue ε seg.slope
  optimal : ∀ m, feasibleSlope (Finset.Icc (seg.start + 1) seg.finish) t y
      (t seg.start) seg.anchorValue ε m →
    nativeSSE (Finset.Icc (seg.start + 1) seg.finish) t y (t seg.start) seg.anchorValue seg.slope ≤
      nativeSSE (Finset.Icc (seg.start + 1) seg.finish) t y (t seg.start) seg.anchorValue m

/-- A chain records actual fitted junctions, valid selected segments, and every rejection. -/
inductive NativeChain (t y : ℕ → ℝ) (ε : ℝ) : ℕ → ℝ → ℕ → List NativeSegment → Prop
  | empty (s : ℕ) (q : ℝ) : NativeChain t y ε s q s []
  | terminal {seg : NativeSegment} (hv : NativeSegmentValid t y ε seg) :
      NativeChain t y ε seg.start seg.anchorValue seg.finish [seg]
  | cons {seg : NativeSegment} {last : ℕ} {tail : List NativeSegment}
      (hv : NativeSegmentValid t y ε seg)
      (hreject : ¬ nativePrefixFeasible t y ε seg.start (seg.finish + 1) seg.anchorValue)
      (hnext : NativeChain t y ε seg.finish (nativeSegmentEndpoint t seg) last tail) :
      NativeChain t y ε seg.start seg.anchorValue last (seg :: tail)

theorem nativePrefix_singleton (t y : ℕ → ℝ) (ht : StrictMono t)
    {ε : ℝ} (hε : 0 ≤ ε) (s : ℕ) (q : ℝ) : nativePrefixFeasible t y ε s (s + 1) q := by
  change ∃ m, feasibleSlope (Finset.Icc (s + 1) (s + 1)) t y (t s) q ε m
  rw [Finset.Icc_self]
  exact ⟨_, feasibleSlope_singleton (s + 1) t y (t s) q ε (ht (Nat.lt_succ_self s)) hε⟩

theorem nativeOutputSegment_valid (t y : ℕ → ℝ) (ht : StrictMono t)
    (ε : ℝ) (s e : ℕ) (q : ℝ) (hse : s < e)
    (hc : nativePrefixFeasible t y ε s e q) :
    NativeSegmentValid t y ε (nativeOutputSegment t y ε s e q hse) := by
  have htime : ∀ i ∈ Finset.Icc (s + 1) e, t s < t i := by
    intro i hi
    exact ht (by have := (Finset.mem_Icc.mp hi).1; omega)
  refine ⟨hse, nativeSelectedSlope_feasible _ _ _ _ _ _ _ htime hc, ?_⟩
  intro m hm
  exact nativeSelectedSlope_minimal _ _ _ _ _ _ _ _ htime hm

/-- Induction follows the true accept/reject branches and carries the already observed rejection. -/
theorem scanNative_spec (t y : ℕ → ℝ) (ht : StrictMono t) {ε : ℝ} (hε : 0 ≤ ε)
    (fuel s e : ℕ) (q : ℝ) (hse : s < e) (hc : nativePrefixFeasible t y ε s e q) :
    NativeChain t y ε s q (e + fuel) (scanNative t y ε fuel s e q hse) := by
  induction fuel generalizing s e q with
  | zero =>
      simpa only [Nat.add_zero, scanNative] using!
        NativeChain.terminal (nativeOutputSegment_valid t y ht ε s e q hse hc)
  | succ fuel ih =>
      by_cases hn : nativePrefixFeasible t y ε s (e + 1) q
      · simpa only [scanNative, if_pos hn, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          ih s (e + 1) q (hse.trans (Nat.lt_succ_self e)) hn
      · have hnext := ih e (e + 1)
          (nativeSegmentEndpoint t (nativeOutputSegment t y ε s e q hse))
          (Nat.lt_succ_self e) (nativePrefix_singleton t y ht hε e _)
        have hchain := NativeChain.cons
          (nativeOutputSegment_valid t y ht ε s e q hse hc) hn hnext
        simpa only [scanNative, if_neg hn, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using! hchain

theorem nativeStream_spec (t y : ℕ → ℝ) (ht : StrictMono t) {ε : ℝ} (hε : 0 ≤ ε)
    (last : ℕ) : NativeChain t y ε 0 (y 0) last (nativeStream t y ε last) := by
  cases last with
  | zero => exact NativeChain.empty 0 (y 0)
  | succ n =>
      simpa only [nativeStream, Nat.add_comm] using
        scanNative_spec t y ht hε n 0 1 (y 0) (by omega) (nativePrefix_singleton t y ht hε 0 _)

theorem NativeChain.valid_segments {t y : ℕ → ℝ} {ε : ℝ} {s last : ℕ} {q : ℝ}
    {segments : List NativeSegment} (h : NativeChain t y ε s q last segments) :
    ∀ seg ∈ segments, NativeSegmentValid t y ε seg := by
  induction h with
  | empty => simp
  | terminal hv => simpa only [List.mem_singleton, forall_eq] using hv
  | cons hv _ _ ih =>
      intro seg hseg
      rcases List.mem_cons.mp hseg with rfl | hseg
      · exact hv
      · exact ih seg hseg

theorem NativeChain.endpoint_error {t y : ℕ → ℝ} {ε : ℝ} {seg : NativeSegment}
    (hv : NativeSegmentValid t y ε seg) : |nativeSegmentEndpoint t seg - y seg.finish| ≤ ε := by
  have hpos := hv.positive
  rw [abs_sub_comm]
  exact hv.feasible seg.finish (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)

theorem NativeChain.covers_index {t y : ℕ → ℝ} {ε : ℝ} {s last j : ℕ} {q : ℝ}
    {segments : List NativeSegment} (h : NativeChain t y ε s q last segments)
    (hsj : s < j) (hjl : j ≤ last) :
    ∃ seg ∈ segments, seg.start < j ∧ j ≤ seg.finish := by
  induction h with
  | empty => omega
  | terminal hv => exact ⟨_, List.mem_singleton_self _, hsj, hjl⟩
  | @cons seg last tail hv hr hn ih =>
      by_cases hj : j ≤ seg.finish
      · exact ⟨seg, List.mem_cons_self, hsj, hj⟩
      · obtain ⟨g, hg, hs, he⟩ := ih (by omega) hjl
        exact ⟨g, List.mem_cons_of_mem seg hg, hs, he⟩

theorem NativeChain.anchor_errors {t y : ℕ → ℝ} {ε : ℝ} {s last : ℕ} {q : ℝ}
    {segments : List NativeSegment} (h : NativeChain t y ε s q last segments)
    (hq : |q - y s| ≤ ε) :
    ∀ seg ∈ segments, |seg.anchorValue - y seg.start| ≤ ε := by
  induction h with
  | empty => simp
  | terminal hv => simpa only [List.mem_singleton, forall_eq] using hq
  | cons hv _ _ ih =>
      intro seg hseg
      rcases List.mem_cons.mp hseg with rfl | hseg
      · exact hq
      · exact ih (NativeChain.endpoint_error hv) seg hseg

theorem nativeStream_covers_index (t y : ℕ → ℝ) (ht : StrictMono t)
    {ε : ℝ} (hε : 0 ≤ ε) {last j : ℕ} (hj : 0 < j) (hjl : j ≤ last) :
    ∃ seg ∈ nativeStream t y ε last, seg.start < j ∧ j ≤ seg.finish :=
  (nativeStream_spec t y ht hε last).covers_index hj hjl

/-- Every actual emitted line fits its entire sample interval, including the inherited anchor. -/
theorem nativeStream_segment_sample_error (t y : ℕ → ℝ) (ht : StrictMono t)
    {ε : ℝ} (hε : 0 ≤ ε) {last : ℕ} {seg : NativeSegment}
    (hseg : seg ∈ nativeStream t y ε last) {j : ℕ} (hsj : seg.start ≤ j) (hje : j ≤ seg.finish) :
    |y j - (seg.anchorValue + seg.slope * (t j - t seg.start))| ≤ ε := by
  have hc := nativeStream_spec t y ht hε last
  by_cases hj : j = seg.start
  · subst j
    simpa only [sub_self, mul_zero, add_zero, abs_sub_comm] using
      hc.anchor_errors (by simpa only [sub_self, abs_zero] using hε) seg hseg
  · exact (hc.valid_segments seg hseg).feasible j (Finset.mem_Icc.mpr ⟨by omega, hje⟩)

end

end SwingRepair
