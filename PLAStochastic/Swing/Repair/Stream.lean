import PLAStochastic.Swing.Repair.AcceptedPrefix
import PLAStochastic.Swing.Repair.Bridge

/-!
# The complete finite repair loop

The input consists of the first `sampleCount` entries of `t` and `y`.
The exact-real acceptance test is nonemptiness of the paper's half-budget cone.
No output correctness assumption occurs in the loop specification.
-/

namespace SwingRepair

inductive StreamKind where
  | chord
  | bridge
  | terminal
  deriving DecidableEq, Repr

/-- Output endpoints are indices of true input samples. -/
structure StreamSegment where
  start : ℕ
  finish : ℕ
  kind : StreamKind
  deriving DecidableEq, Repr

/-- Scan the next `remaining` samples after `previous`, then apply the EOF rule. -/
noncomputable def scanRepair (t y : ℕ → ℝ) (ε : ℝ)
    (anchor previous remaining : ℕ) : List StreamSegment := by
  classical
  exact match remaining with
  | 0 => if anchor < previous then [⟨anchor, previous, .terminal⟩] else []
  | n + 1 =>
      if (prefixCone t y anchor (previous + 1) ε).Nonempty then
        scanRepair t y ε anchor (previous + 1) n
      else
        ⟨anchor, previous, .chord⟩ :: ⟨previous, previous + 1, .bridge⟩ ::
          scanRepair t y ε (previous + 1) (previous + 1) n

/-- Empty and singleton inputs have no segments. Nonempty streams start at sample zero. -/
noncomputable def repairStream (t y : ℕ → ℝ) (ε : ℝ) : ℕ → List StreamSegment
  | 0 => []
  | n + 1 => scanRepair t y ε 0 0 n

/-- An ordered, gap-free list of strictly positive index spans. -/
inductive SegmentChain : ℕ → ℕ → List StreamSegment → Prop where
  | nil (s : ℕ) : SegmentChain s s []
  | cons {s e z : ℕ} {kind : StreamKind} {rest : List StreamSegment} :
      s < e → SegmentChain e z rest →
        SegmentChain s z (⟨s, e, kind⟩ :: rest)

/-- A completed chord and a terminal chord have feasible half-budget prefixes;
a bridge joins consecutive input samples. -/
def SegmentValid (t y : ℕ → ℝ) (ε : ℝ) (seg : StreamSegment) : Prop :=
  seg.start < seg.finish ∧ match seg.kind with
    | .chord | .terminal => (prefixCone t y seg.start seg.finish ε).Nonempty
    | .bridge => seg.finish = seg.start + 1

theorem prefixCone_self_nonempty (t y : ℕ → ℝ) (s : ℕ) (ε : ℝ) :
    (prefixCone t y s s ε).Nonempty := by
  refine ⟨0, ?_⟩
  intro j hj
  have := Finset.mem_Icc.mp hj
  omega

/-- A single new sample always has a feasible anchored slope. -/
theorem prefixCone_next_nonempty {t y : ℕ → ℝ} {ε : ℝ}
    (ht : StrictMono t) (hε : 0 ≤ ε) (s : ℕ) :
    (prefixCone t y s (s + 1) ε).Nonempty := by
  refine ⟨(y (s + 1) - y s) / (t (s + 1) - t s), ?_⟩
  intro j hj
  have hj' := Finset.mem_Icc.mp hj
  have heq : j = s + 1 := by omega
  subst j
  apply (sample_error_iff_bounds (ht (Nat.lt_succ_self s))).mp
  exact feasibleSlope_singleton (s + 1) t y (t s) (y s) (ε / 2)
    (ht (Nat.lt_succ_self s)) (by linarith) (s + 1) (Finset.mem_singleton_self _)

/-- The loop invariant proves the actual output chain and every emitted segment's certificate. -/
theorem scanRepair_spec {t y : ℕ → ℝ} {ε : ℝ}
    (ht : StrictMono t) (hε : 0 ≤ ε) (remaining : ℕ) :
    ∀ anchor previous, anchor ≤ previous →
      (prefixCone t y anchor previous ε).Nonempty →
      SegmentChain anchor (previous + remaining)
          (scanRepair t y ε anchor previous remaining) ∧
        ∀ seg ∈ scanRepair t y ε anchor previous remaining,
          SegmentValid t y ε seg := by
  classical
  induction remaining with
  | zero =>
      intro s p hsp hcone
      by_cases hlt : s < p
      · simp only [scanRepair, if_pos hlt, Nat.add_zero]
        constructor
        · exact SegmentChain.cons hlt (SegmentChain.nil p)
        · intro seg hseg
          have heq : seg = ⟨s, p, .terminal⟩ := List.mem_singleton.mp hseg
          subst seg
          exact ⟨hlt, hcone⟩
      · have heq : s = p := by omega
        subst p
        simp only [scanRepair, if_neg (lt_irrefl s), Nat.add_zero]
        exact ⟨SegmentChain.nil s, by simp⟩
  | succ n ih =>
      intro s p hsp hcone
      by_cases haccept : (prefixCone t y s (p + 1) ε).Nonempty
      · simpa only [scanRepair, if_pos haccept, Nat.add_assoc, Nat.add_left_comm,
          Nat.add_comm] using
          ih s (p + 1) (by omega) haccept
      · have hlt : s < p := by
          by_contra h
          have heq : s = p := by omega
          subst p
          exact haccept (prefixCone_next_nonempty ht hε s)
        obtain ⟨hchain, hvalid⟩ :=
          ih (p + 1) (p + 1) le_rfl (prefixCone_self_nonempty t y (p + 1) ε)
        simp only [scanRepair, if_neg haccept]
        constructor
        · apply SegmentChain.cons hlt
          apply SegmentChain.cons (Nat.lt_succ_self p)
          simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hchain
        · intro seg hseg
          simp only [List.mem_cons] at hseg
          rcases hseg with heq | heq | hseg
          · subst seg
            exact ⟨hlt, hcone⟩
          · subst seg
            exact ⟨Nat.lt_succ_self p, rfl⟩
          · exact hvalid seg hseg

/-- The complete finite algorithm covers the first through last sample. -/
theorem repairStream_spec {t y : ℕ → ℝ} {ε : ℝ}
    (ht : StrictMono t) (hε : 0 ≤ ε) (last : ℕ) :
    SegmentChain 0 last (repairStream t y ε (last + 1)) ∧
      ∀ seg ∈ repairStream t y ε (last + 1), SegmentValid t y ε seg := by
  simpa only [repairStream, Nat.zero_add] using
    scanRepair_spec ht hε last 0 0 le_rfl (prefixCone_self_nonempty t y 0 ε)

@[simp] theorem repairStream_empty (t y : ℕ → ℝ) (ε : ℝ) :
    repairStream t y ε 0 = [] := rfl

@[simp] theorem repairStream_singleton (t y : ℕ → ℝ) (ε : ℝ) :
    repairStream t y ε 1 = [] := by
  simp [repairStream, scanRepair]

theorem SegmentChain.start_le_finish {s e : ℕ} {segments : List StreamSegment}
    (hc : SegmentChain s e segments) : s ≤ e := by
  induction hc with
  | nil => exact le_rfl
  | cons hlt _ ih => exact hlt.le.trans ih

/-- Every output endpoint lies inside the input range and every span is positive. -/
theorem SegmentChain.segment_bounds {s e : ℕ} {segments : List StreamSegment}
    (hc : SegmentChain s e segments) :
    ∀ seg ∈ segments, s ≤ seg.start ∧ seg.finish ≤ e ∧ seg.start < seg.finish := by
  induction hc with
  | nil => simp
  | @cons s b e kind rest hlt htail ih =>
      intro seg hseg
      rcases List.mem_cons.mp hseg with heq | hseg
      · subst seg
        exact ⟨le_rfl, htail.start_le_finish, hlt⟩
      · obtain ⟨hstart, hfinish, hpositive⟩ := ih seg hseg
        exact ⟨hlt.le.trans hstart, hfinish, hpositive⟩

/-- No original grid edge is omitted by the output chain. -/
theorem SegmentChain.covers_edge {s e i : ℕ} {segments : List StreamSegment}
    (hc : SegmentChain s e segments) (hsi : s ≤ i) (hie : i < e) :
    ∃ seg ∈ segments, seg.start ≤ i ∧ i < seg.finish := by
  induction hc with
  | nil => omega
  | @cons s b e kind rest hlt htail ih =>
      by_cases hib : i < b
      · exact ⟨⟨s, b, kind⟩, List.mem_cons_self, hsi, hib⟩
      · obtain ⟨seg, hseg, hstart, hfinish⟩ := ih (by omega) hie
        exact ⟨seg, List.mem_cons_of_mem _ hseg, hstart, hfinish⟩

/-- The finite loop supplies a certified output segment covering each original grid edge. -/
theorem repairStream_covers_edge {t y : ℕ → ℝ} {ε : ℝ}
    (ht : StrictMono t) (hε : 0 ≤ ε) {last i : ℕ} (hi : i < last) :
    ∃ seg ∈ repairStream t y ε (last + 1),
      seg.start ≤ i ∧ i < seg.finish ∧ SegmentValid t y ε seg := by
  obtain ⟨hc, hv⟩ := repairStream_spec ht hε last
  obtain ⟨seg, hseg, hs, he⟩ := hc.covers_edge (Nat.zero_le i) hi
  exact ⟨seg, hseg, hs, he, hv seg hseg⟩

/-- Every emitted endpoint is one of the supplied finite input samples. -/
theorem repairStream_true_sample_indices {t y : ℕ → ℝ} {ε : ℝ}
    (ht : StrictMono t) (hε : 0 ≤ ε) {last : ℕ} {seg : StreamSegment}
    (hseg : seg ∈ repairStream t y ε (last + 1)) :
    seg.start < last + 1 ∧ seg.finish < last + 1 := by
  have hb := (repairStream_spec ht hε last).1.segment_bounds seg hseg
  omega

/-- Every emitted segment has strictly positive physical duration. -/
theorem repairStream_positive_length {t y : ℕ → ℝ} {ε : ℝ}
    (ht : StrictMono t) (hε : 0 ≤ ε) {last : ℕ} {seg : StreamSegment}
    (hseg : seg ∈ repairStream t y ε (last + 1)) :
    0 < t seg.finish - t seg.start := by
  exact sub_pos.mpr (ht ((repairStream_spec ht hε last).2 seg hseg).1)

/-- Each emitted bridge spans exactly one original input edge. -/
theorem repairStream_bridge_adjacent {t y : ℕ → ℝ} {ε : ℝ}
    (ht : StrictMono t) (hε : 0 ≤ ε) {last : ℕ} {seg : StreamSegment}
    (hseg : seg ∈ repairStream t y ε (last + 1)) (hkind : seg.kind = .bridge) :
    seg.finish = seg.start + 1 := by
  have hv := ((repairStream_spec ht hε last).2 seg hseg).2
  simpa only [hkind] using hv

/-- Completed and terminal chords are emitted only from nonempty half-budget cones. -/
theorem repairStream_chord_cone {t y : ℕ → ℝ} {ε : ℝ}
    (ht : StrictMono t) (hε : 0 ≤ ε) {last : ℕ} {seg : StreamSegment}
    (hseg : seg ∈ repairStream t y ε (last + 1))
    (hkind : seg.kind = .chord ∨ seg.kind = .terminal) :
    (prefixCone t y seg.start seg.finish ε).Nonempty := by
  have hv := ((repairStream_spec ht hε last).2 seg hseg).2
  rcases hkind with hkind | hkind <;> simpa only [hkind] using hv

/-- Every actual output segment meets the full error budget on each grid edge it spans. -/
theorem segmentValid_edge_error {t y : ℕ → ℝ} {ε θ : ℝ}
    (ht : StrictMono t) (hε : 0 ≤ ε) {seg : StreamSegment}
    (hv : SegmentValid t y ε seg) {i : ℕ} (hs : seg.start ≤ i)
    (he : i < seg.finish) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    |blend (y i) (y (i + 1)) θ -
      chord (t seg.start) (t seg.finish) (y seg.start) (y seg.finish)
        (blend (t i) (t (i + 1)) θ)| ≤ ε := by
  obtain ⟨s, e, kind⟩ := seg
  cases kind with
  | chord => exact prefix_chord_interpolation_error ht hε hv.1 hv.2 hs he hθ₀ hθ₁
  | terminal => exact prefix_chord_interpolation_error ht hε hv.1 hv.2 hs he hθ₀ hθ₁
  | bridge =>
      have heq : e = s + 1 := hv.2
      have hi : i = s := by dsimp at hs he; omega
      subst i
      subst e
      simpa only [bridge_error_zero (ht (Nat.lt_succ_self s))] using hε

/-- Actual execution supplies both edge coverage and the interpolation error certificate. -/
theorem repairStream_edge_error {t y : ℕ → ℝ} {ε θ : ℝ}
    (ht : StrictMono t) (hε : 0 ≤ ε) {last i : ℕ} (hi : i < last)
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    ∃ seg ∈ repairStream t y ε (last + 1), seg.start ≤ i ∧ i < seg.finish ∧
      |blend (y i) (y (i + 1)) θ -
        chord (t seg.start) (t seg.finish) (y seg.start) (y seg.finish)
          (blend (t i) (t (i + 1)) θ)| ≤ ε := by
  obtain ⟨seg, hseg, hs, he, hv⟩ := repairStream_covers_edge ht hε hi
  exact ⟨seg, hseg, hs, he, segmentValid_edge_error ht hε hv hs he hθ₀ hθ₁⟩

end SwingRepair
