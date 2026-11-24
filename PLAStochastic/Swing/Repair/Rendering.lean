import PLAStochastic.Swing.Repair.Stream

/-!
# The reconstruction produced by the complete finite repair loop

The renderer uses each output chord through its true input endpoints. It is
extended affinely to the left and constantly after the last sample. Theorems
below concern the actual list returned by `repairStream`.
-/

namespace SwingRepair

/-- Evaluate the output chain, with a constant value when there are no further segments. -/
noncomputable def renderSegments (t y : ℕ → ℝ) (anchor : ℕ) :
    List StreamSegment → ℝ → ℝ
  | [], _ => y anchor
  | seg :: rest, x =>
      if x ≤ t seg.finish then
        chord (t seg.start) (t seg.finish) (y seg.start) (y seg.finish) x
      else renderSegments t y seg.finish rest x

theorem SegmentChain.render_at_start {t y : ℕ → ℝ} (ht : StrictMono t)
    {s e : ℕ} {segments : List StreamSegment} (hc : SegmentChain s e segments) :
    renderSegments t y s segments (t s) = y s := by
  cases hc with
  | nil => rfl
  | cons hlt _ =>
      simp only [renderSegments, if_pos (ht hlt).le, chord_left]

theorem SegmentChain.render_at_finish {t y : ℕ → ℝ} (ht : StrictMono t)
    {s e : ℕ} {segments : List StreamSegment} (hc : SegmentChain s e segments) :
    renderSegments t y s segments (t e) = y e := by
  induction hc with
  | nil => rfl
  | @cons s b e kind rest hlt htail ih =>
      by_cases hbe : b = e
      · subst e
        simp only [renderSegments, if_pos le_rfl, chord_right (ht hlt)]
      · have hbelt : b < e := by have := htail.start_le_finish; omega
        simpa only [renderSegments, if_neg (not_le_of_gt (ht hbelt))] using ih

/-- At and after a junction, the preceding segment can be replaced by its tail. -/
theorem renderSegments_tail_of_ge {t y : ℕ → ℝ} (ht : StrictMono t)
    {s b e : ℕ} {kind : StreamKind} {rest : List StreamSegment}
    (hsb : s < b) (htail : SegmentChain b e rest) {x : ℝ} (hx : t b ≤ x) :
    renderSegments t y s (⟨s, b, kind⟩ :: rest) x = renderSegments t y b rest x := by
  by_cases hle : x ≤ t b
  · have heq : x = t b := le_antisymm hle hx
    subst x
    rw [renderSegments, if_pos le_rfl, chord_right (ht hsb), htail.render_at_start ht]
  · simp only [renderSegments, if_neg hle]

/-- Every junction of the entire finite chain is continuous. -/
theorem SegmentChain.continuous_render {t y : ℕ → ℝ} (ht : StrictMono t)
    {s e : ℕ} {segments : List StreamSegment} (hc : SegmentChain s e segments) :
    Continuous (renderSegments t y s segments) := by
  induction hc with
  | nil => exact continuous_const
  | @cons s b e kind rest hlt htail ih =>
      change Continuous (fun x => if x ≤ t b then
        chord (t s) (t b) (y s) (y b) x else renderSegments t y b rest x)
      apply Continuous.if_le (continuous_chord (t s) (t b) (y s) (y b))
        ih continuous_id continuous_const
      intro x hx
      change x = t b at hx
      subst x
      rw [chord_right (ht hlt), htail.render_at_start ht]

/-- The renderer preserves both true endpoints of every emitted segment. -/
theorem SegmentChain.render_segment_knots {t y : ℕ → ℝ} (ht : StrictMono t)
    {s e : ℕ} {segments : List StreamSegment} (hc : SegmentChain s e segments) :
    ∀ seg ∈ segments,
      renderSegments t y s segments (t seg.start) = y seg.start ∧
      renderSegments t y s segments (t seg.finish) = y seg.finish := by
  induction hc with
  | nil => simp
  | @cons s b e kind rest hlt htail ih =>
      intro seg hseg
      rcases List.mem_cons.mp hseg with heq | hseg
      · subst seg
        constructor
        · simp only [renderSegments, if_pos (ht hlt).le, chord_left]
        · simp only [renderSegments, if_pos le_rfl, chord_right (ht hlt)]
      · have hb := htail.segment_bounds seg hseg
        obtain ⟨hs, he⟩ := ih seg hseg
        constructor
        · rw [renderSegments_tail_of_ge ht hlt htail (ht.monotone hb.1)]
          exact hs
        · rw [renderSegments_tail_of_ge ht hlt htail
            (ht.monotone (hb.1.trans hb.2.2.le))]
          exact he

/-- Barycentric times remain inside the corresponding original grid edge. -/
theorem blend_mem_interval {a b θ : ℝ} (hab : a ≤ b) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    a ≤ blend a b θ ∧ blend a b θ ≤ b := by
  have hleft := mul_nonneg hθ₀ (sub_nonneg.mpr hab)
  have hright := mul_nonneg (sub_nonneg.mpr hθ₁) (sub_nonneg.mpr hab)
  unfold blend
  constructor <;> nlinarith

/-- The renderer inherits every original-edge bound from its certified segment chain. -/
theorem SegmentChain.render_edge_error {t y : ℕ → ℝ} {ε θ : ℝ}
    (ht : StrictMono t) (hε : 0 ≤ ε) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    {s e : ℕ} {segments : List StreamSegment} (hc : SegmentChain s e segments) :
    (∀ seg ∈ segments, SegmentValid t y ε seg) →
    ∀ i, s ≤ i → i < e →
      |blend (y i) (y (i + 1)) θ -
        renderSegments t y s segments (blend (t i) (t (i + 1)) θ)| ≤ ε := by
  induction hc with
  | nil => intro _ i hsi hie; omega
  | @cons s b e kind rest hlt htail ih =>
      intro hv i hsi hie
      have hblend := blend_mem_interval (ht (Nat.lt_succ_self i)).le hθ₀ hθ₁
      by_cases hib : i < b
      · rw [renderSegments, if_pos (hblend.2.trans (ht.monotone hib))]
        exact segmentValid_edge_error ht hε (hv _ List.mem_cons_self) hsi hib hθ₀ hθ₁
      · have hbi : b ≤ i := by omega
        rw [renderSegments_tail_of_ge ht hlt htail ((ht.monotone hbi).trans hblend.1)]
        exact ih (fun seg hseg => hv seg (List.mem_cons_of_mem _ hseg)) i hbi hie

/-- The single reconstruction function returned by finite repair execution. -/
noncomputable def repairReconstruction (t y : ℕ → ℝ) (ε : ℝ)
    (sampleCount : ℕ) : ℝ → ℝ :=
  renderSegments t y 0 (repairStream t y ε sampleCount)

/-- Empty and singleton streams have no output segments; the singleton knot is retained. -/
theorem repairReconstruction_singleton (t y : ℕ → ℝ) (ε : ℝ) :
    repairReconstruction t y ε 1 = fun _ => y 0 := by
  simp [repairReconstruction, renderSegments]

theorem repairReconstruction_continuous {t y : ℕ → ℝ} {ε : ℝ}
    (ht : StrictMono t) (hε : 0 ≤ ε) (sampleCount : ℕ) :
    Continuous (repairReconstruction t y ε sampleCount) := by
  cases sampleCount with
  | zero => exact continuous_const
  | succ last => exact (repairStream_spec ht hε last).1.continuous_render ht

theorem repairReconstruction_endpoints {t y : ℕ → ℝ} {ε : ℝ}
    (ht : StrictMono t) (hε : 0 ≤ ε) (last : ℕ) :
    repairReconstruction t y ε (last + 1) (t 0) = y 0 ∧
      repairReconstruction t y ε (last + 1) (t last) = y last := by
  have hc := (repairStream_spec (y := y) ht hε last).1
  exact ⟨hc.render_at_start ht, hc.render_at_finish ht⟩

theorem repairReconstruction_true_knots {t y : ℕ → ℝ} {ε : ℝ}
    (ht : StrictMono t) (hε : 0 ≤ ε) (last : ℕ) :
    ∀ seg ∈ repairStream t y ε (last + 1),
      repairReconstruction t y ε (last + 1) (t seg.start) = y seg.start ∧
      repairReconstruction t y ε (last + 1) (t seg.finish) = y seg.finish := by
  exact (repairStream_spec ht hε last).1.render_segment_knots ht

/-- The complete finite repair algorithm has error at most ε on every original grid edge. -/
theorem repairReconstruction_edge_error {t y : ℕ → ℝ} {ε θ : ℝ}
    (ht : StrictMono t) (hε : 0 ≤ ε) {last i : ℕ} (hi : i < last)
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    |blend (y i) (y (i + 1)) θ -
      repairReconstruction t y ε (last + 1) (blend (t i) (t (i + 1)) θ)| ≤ ε := by
  obtain ⟨hc, hv⟩ := repairStream_spec ht hε last
  exact hc.render_edge_error ht hε hθ₀ hθ₁ hv i (Nat.zero_le i) hi

/-- The error guarantee includes every sample, including a singleton input and the last sample. -/
theorem repairReconstruction_sample_error {t y : ℕ → ℝ} {ε : ℝ}
    (ht : StrictMono t) (hε : 0 ≤ ε) {last i : ℕ} (hi : i ≤ last) :
    |y i - repairReconstruction t y ε (last + 1) (t i)| ≤ ε := by
  rcases eq_or_lt_of_le hi with heq | hlt
  · subst i
    rw [(repairReconstruction_endpoints ht hε last).2]
    simpa using hε
  · simpa only [blend_zero] using
      repairReconstruction_edge_error ht hε hlt (θ := 0) le_rfl zero_le_one

end SwingRepair
