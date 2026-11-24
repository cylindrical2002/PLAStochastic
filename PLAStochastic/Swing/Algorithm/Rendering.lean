import PLAStochastic.Swing.Algorithm.Stream
import PLAStochastic.Swing.Repair.Rendering

/-!
# Continuous rendering of actual native Swing output

The native renderer evaluates the emitted constrained-SSE lines and carries
their fitted endpoint values across junctions. Its certified error is against
the independent piecewise-linear interpolation of the original samples.
-/

noncomputable section

namespace SwingRepair

set_option backward.isDefEq.respectTransparency false

def nativeSegmentLine (t : ℕ → ℝ) (seg : NativeSegment) (x : ℝ) : ℝ :=
  seg.anchorValue + seg.slope * (x - t seg.start)

/-- The fallback is the last fitted recording, including the singleton-input case. -/
def renderNative (t : ℕ → ℝ) (q : ℝ) : List NativeSegment → ℝ → ℝ
  | [], _ => q
  | seg :: rest, x => if x ≤ t seg.finish then nativeSegmentLine t seg x
      else renderNative t (nativeSegmentEndpoint t seg) rest x

theorem nativeSegmentLine_start (t : ℕ → ℝ) (seg : NativeSegment) :
    nativeSegmentLine t seg (t seg.start) = seg.anchorValue := by
  simp only [nativeSegmentLine, sub_self, mul_zero, add_zero]

theorem nativeSegmentLine_finish (t : ℕ → ℝ) (seg : NativeSegment) :
    nativeSegmentLine t seg (t seg.finish) = nativeSegmentEndpoint t seg := rfl

theorem continuous_nativeSegmentLine (t : ℕ → ℝ) (seg : NativeSegment) :
    Continuous (nativeSegmentLine t seg) := by unfold nativeSegmentLine; fun_prop

theorem nativeSegmentLine_blend (t : ℕ → ℝ) (seg : NativeSegment) (u v θ : ℝ) :
    nativeSegmentLine t seg (blend u v θ) =
      blend (nativeSegmentLine t seg u) (nativeSegmentLine t seg v) θ := by
  unfold nativeSegmentLine blend
  ring

theorem NativeChain.start_le_finish {t y : ℕ → ℝ} {ε : ℝ} {s last : ℕ} {q : ℝ}
    {segments : List NativeSegment} (hc : NativeChain t y ε s q last segments) : s ≤ last := by
  induction hc with
  | empty => exact le_rfl
  | terminal hv => exact hv.positive.le
  | cons hv _ _ ih => exact hv.positive.le.trans ih

theorem NativeChain.segment_bounds {t y : ℕ → ℝ} {ε : ℝ} {s last : ℕ} {q : ℝ}
    {segments : List NativeSegment} (hc : NativeChain t y ε s q last segments) :
    ∀ seg ∈ segments, s ≤ seg.start ∧ seg.finish ≤ last ∧ seg.start < seg.finish := by
  induction hc with
  | empty => simp
  | terminal hv =>
      intro seg hs
      obtain rfl := List.mem_singleton.mp hs
      exact ⟨le_rfl, le_rfl, hv.positive⟩
  | @cons head last tail hv _ hn ih =>
      intro seg hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact ⟨le_rfl, hn.start_le_finish, hv.positive⟩
      · obtain ⟨hs, he, hp⟩ := ih seg hs
        exact ⟨hv.positive.le.trans hs, he, hp⟩

theorem NativeChain.render_at_start {t y : ℕ → ℝ} (ht : StrictMono t)
    {ε : ℝ} {s last : ℕ} {q : ℝ} {segments : List NativeSegment}
    (hc : NativeChain t y ε s q last segments) : renderNative t q segments (t s) = q := by
  cases hc with
  | empty => rfl
  | terminal hv =>
      simp only [renderNative, if_pos (ht hv.positive).le, nativeSegmentLine_start]
  | cons hv _ _ =>
      simp only [renderNative, if_pos (ht hv.positive).le, nativeSegmentLine_start]

/-- The actual fitted endpoint of a segment agrees with its tail's fitted anchor. -/
theorem renderNative_tail_of_ge {t y : ℕ → ℝ} (ht : StrictMono t)
    {ε q x : ℝ} {seg : NativeSegment} {last : ℕ} {tail : List NativeSegment}
    (hc : NativeChain t y ε seg.finish (nativeSegmentEndpoint t seg) last tail)
    (hx : t seg.finish ≤ x) :
    renderNative t q (seg :: tail) x = renderNative t (nativeSegmentEndpoint t seg) tail x := by
  by_cases hle : x ≤ t seg.finish
  · have heq : x = t seg.finish := le_antisymm hle hx
    subst x
    rw [renderNative, if_pos le_rfl, nativeSegmentLine_finish, hc.render_at_start ht]
  · simp only [renderNative, if_neg hle]

theorem NativeChain.continuous_render {t y : ℕ → ℝ} (ht : StrictMono t)
    {ε : ℝ} {s last : ℕ} {q : ℝ} {segments : List NativeSegment}
    (hc : NativeChain t y ε s q last segments) : Continuous (renderNative t q segments) := by
  induction hc with
  | empty => exact continuous_const
  | @terminal seg hv =>
      change Continuous (fun x => if x ≤ t seg.finish then nativeSegmentLine t seg x
        else nativeSegmentEndpoint t seg)
      apply Continuous.if_le (continuous_nativeSegmentLine t seg) continuous_const
        continuous_id continuous_const
      intro x hx
      change x = t seg.finish at hx
      subst x
      rfl
  | @cons seg last tail hv _ hn ih =>
      change Continuous (fun x => if x ≤ t seg.finish then nativeSegmentLine t seg x
        else renderNative t (nativeSegmentEndpoint t seg) tail x)
      apply Continuous.if_le (continuous_nativeSegmentLine t seg) ih continuous_id continuous_const
      intro x hx
      change x = t seg.finish at hx
      subst x
      rw [nativeSegmentLine_finish, hn.render_at_start ht]

/-- The single renderer agrees with every actual emitted fitted line on its complete span. -/
theorem NativeChain.render_on_segment {t y : ℕ → ℝ} (ht : StrictMono t)
    {ε : ℝ} {s last : ℕ} {q : ℝ} {segments : List NativeSegment}
    (hc : NativeChain t y ε s q last segments) :
    ∀ seg ∈ segments, ∀ x : ℝ, t seg.start ≤ x → x ≤ t seg.finish →
      renderNative t q segments x = nativeSegmentLine t seg x := by
  induction hc with
  | empty => simp
  | terminal hv =>
      intro seg hs x _ hx
      obtain rfl := List.mem_singleton.mp hs
      simp only [renderNative, if_pos hx]
  | @cons head last tail hv _ hn ih =>
      intro seg hs x hx₀ hx₁
      rcases List.mem_cons.mp hs with rfl | hs
      · simp only [renderNative, if_pos hx₁]
      · have hb := hn.segment_bounds seg hs
        rw [renderNative_tail_of_ge ht hn ((ht.monotone hb.1).trans hx₀)]
        exact ih seg hs x hx₀ hx₁

theorem NativeSegmentValid.sample_error {t y : ℕ → ℝ} {ε : ℝ} {seg : NativeSegment}
    (hv : NativeSegmentValid t y ε seg) (ha : |seg.anchorValue - y seg.start| ≤ ε)
    {j : ℕ} (hj₀ : seg.start ≤ j) (hj₁ : j ≤ seg.finish) :
    |y j - nativeSegmentLine t seg (t j)| ≤ ε := by
  by_cases hj : j = seg.start
  · subst j
    rw [nativeSegmentLine_start, abs_sub_comm]
    exact ha
  · exact hv.feasible j (Finset.mem_Icc.mpr ⟨by omega, hj₁⟩)

theorem NativeSegmentValid.edge_error {t y : ℕ → ℝ} {ε θ : ℝ} {seg : NativeSegment}
    (hv : NativeSegmentValid t y ε seg) (ha : |seg.anchorValue - y seg.start| ≤ ε)
    {i : ℕ} (hi₀ : seg.start ≤ i) (hi₁ : i < seg.finish)
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    |blend (y i) (y (i + 1)) θ - nativeSegmentLine t seg (blend (t i) (t (i + 1)) θ)| ≤ ε := by
  rw [nativeSegmentLine_blend]
  exact blend_error hθ₀ hθ₁ (hv.sample_error ha hi₀ hi₁.le)
    (hv.sample_error ha (by omega) (by omega))

theorem NativeChain.render_sample_error {t y : ℕ → ℝ} (ht : StrictMono t)
    {ε : ℝ} {s last : ℕ} {q : ℝ} {segments : List NativeSegment}
    (hc : NativeChain t y ε s q last segments) (hq : |q - y s| ≤ ε)
    {j : ℕ} (hj₀ : s ≤ j) (hj₁ : j ≤ last) :
    |y j - renderNative t q segments (t j)| ≤ ε := by
  by_cases hj : j = s
  · subst j
    rw [hc.render_at_start ht, abs_sub_comm]
    exact hq
  · obtain ⟨seg, hs, hj₀, hj₁⟩ := hc.covers_index (by omega) hj₁
    rw [hc.render_on_segment ht seg hs (t j) (ht.monotone hj₀.le) (ht.monotone hj₁)]
    exact (hc.valid_segments seg hs).sample_error (hc.anchor_errors hq seg hs) hj₀.le hj₁

theorem NativeChain.render_edge_error {t y : ℕ → ℝ} (ht : StrictMono t)
    {ε θ : ℝ} {s last : ℕ} {q : ℝ} {segments : List NativeSegment}
    (hc : NativeChain t y ε s q last segments) (hq : |q - y s| ≤ ε)
    {i : ℕ} (hi₀ : s ≤ i) (hi₁ : i < last) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    |blend (y i) (y (i + 1)) θ -
      renderNative t q segments (blend (t i) (t (i + 1)) θ)| ≤ ε := by
  obtain ⟨seg, hs, hi₀', hi₁'⟩ := hc.covers_index (j := i + 1) (by omega) (by omega)
  have hb := blend_mem_interval (ht (Nat.lt_succ_self i)).le hθ₀ hθ₁
  have hsi : seg.start ≤ i := by omega
  rw [hc.render_on_segment ht seg hs _ ((ht.monotone hsi).trans hb.1)
    (hb.2.trans (ht.monotone hi₁'))]
  exact (hc.valid_segments seg hs).edge_error (hc.anchor_errors hq seg hs) hsi
    (by omega) hθ₀ hθ₁

/-- `last` indexes the final sample, so `last = 0` is a singleton input. -/
def nativeReconstruction (t y : ℕ → ℝ) (ε : ℝ) (last : ℕ) : ℝ → ℝ :=
  renderNative t (y 0) (nativeStream t y ε last)

theorem nativeReconstruction_singleton (t y : ℕ → ℝ) (ε : ℝ) :
    nativeReconstruction t y ε 0 = fun _ => y 0 := rfl

theorem nativeReconstruction_continuous {t y : ℕ → ℝ} (ht : StrictMono t)
    {ε : ℝ} (hε : 0 ≤ ε) (last : ℕ) : Continuous (nativeReconstruction t y ε last) :=
  (nativeStream_spec t y ht hε last).continuous_render ht

theorem nativeReconstruction_on_segment {t y : ℕ → ℝ} (ht : StrictMono t)
    {ε : ℝ} (hε : 0 ≤ ε) {last : ℕ} {seg : NativeSegment}
    (hseg : seg ∈ nativeStream t y ε last) {x : ℝ}
    (hx₀ : t seg.start ≤ x) (hx₁ : x ≤ t seg.finish) :
    nativeReconstruction t y ε last x = nativeSegmentLine t seg x :=
  (nativeStream_spec t y ht hε last).render_on_segment ht seg hseg x hx₀ hx₁

theorem nativeReconstruction_fitted_knots {t y : ℕ → ℝ} (ht : StrictMono t)
    {ε : ℝ} (hε : 0 ≤ ε) {last : ℕ} {seg : NativeSegment}
    (hseg : seg ∈ nativeStream t y ε last) :
    nativeReconstruction t y ε last (t seg.start) = seg.anchorValue ∧
      nativeReconstruction t y ε last (t seg.finish) = nativeSegmentEndpoint t seg := by
  have htime := (ht ((nativeStream_spec t y ht hε last).valid_segments seg hseg).positive).le
  constructor
  · rw [nativeReconstruction_on_segment ht hε hseg le_rfl htime, nativeSegmentLine_start]
  · rw [nativeReconstruction_on_segment ht hε hseg htime le_rfl, nativeSegmentLine_finish]

theorem nativeReconstruction_sample_error {t y : ℕ → ℝ} (ht : StrictMono t)
    {ε : ℝ} (hε : 0 ≤ ε) {last j : ℕ} (hj : j ≤ last) :
    |y j - nativeReconstruction t y ε last (t j)| ≤ ε :=
  (nativeStream_spec t y ht hε last).render_sample_error ht
    (by simpa only [sub_self, abs_zero] using hε) (Nat.zero_le j) hj

theorem nativeReconstruction_edge_error {t y : ℕ → ℝ} (ht : StrictMono t)
    {ε θ : ℝ} (hε : 0 ≤ ε) {last i : ℕ} (hi : i < last)
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    |blend (y i) (y (i + 1)) θ -
      nativeReconstruction t y ε last (blend (t i) (t (i + 1)) θ)| ≤ ε :=
  (nativeStream_spec t y ht hε last).render_edge_error ht
    (by simpa only [sub_self, abs_zero] using hε) (Nat.zero_le i) hi hθ₀ hθ₁

/-- The original input grid, with one true-endpoint interpolation segment per cell. -/
def interpolationSegments (s : ℕ) : ℕ → List StreamSegment
  | 0 => []
  | n + 1 => ⟨s, s + 1, .bridge⟩ :: interpolationSegments (s + 1) n

theorem interpolationSegments_chain (s n : ℕ) :
    SegmentChain s (s + n) (interpolationSegments s n) := by
  induction n generalizing s with
  | zero => simpa only [Nat.add_zero, interpolationSegments] using SegmentChain.nil s
  | succ n ih =>
      simpa only [interpolationSegments, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        SegmentChain.cons (kind := .bridge) (Nat.lt_succ_self s) (ih (s + 1))

theorem interpolationSegments_valid (t y : ℕ → ℝ) (s n : ℕ) :
    ∀ seg ∈ interpolationSegments s n, SegmentValid t y 0 seg := by
  induction n generalizing s with
  | zero => simp [interpolationSegments]
  | succ n ih =>
      intro seg hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact ⟨Nat.lt_succ_self s, rfl⟩
      · exact ih (s + 1) seg hs

/-- Independent original-sample interpolation; no native fit is used in this definition. -/
def inputInterpolation (t y : ℕ → ℝ) (last : ℕ) : ℝ → ℝ :=
  renderSegments t y 0 (interpolationSegments 0 last)

theorem inputInterpolation_continuous {t y : ℕ → ℝ} (ht : StrictMono t) (last : ℕ) :
    Continuous (inputInterpolation t y last) :=
  (interpolationSegments_chain 0 last).continuous_render ht

theorem inputInterpolation_edge {t y : ℕ → ℝ} (ht : StrictMono t)
    {last i : ℕ} (hi : i < last) {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    inputInterpolation t y last (blend (t i) (t (i + 1)) θ) = blend (y i) (y (i + 1)) θ := by
  have hc : SegmentChain 0 last (interpolationSegments 0 last) := by
    simpa only [Nat.zero_add] using interpolationSegments_chain 0 last
  have he := hc.render_edge_error ht (by norm_num : (0 : ℝ) ≤ 0) hθ₀ hθ₁
    (interpolationSegments_valid t y 0 last) i (Nat.zero_le i) hi
  exact (sub_eq_zero.mp (abs_nonpos_iff.mp he)).symm

theorem inputInterpolation_sample {t y : ℕ → ℝ} (ht : StrictMono t)
    {last i : ℕ} (hi : i ≤ last) : inputInterpolation t y last (t i) = y i := by
  rcases eq_or_lt_of_le hi with heq | hi
  · subst i
    have hc : SegmentChain 0 last (interpolationSegments 0 last) := by
      simpa only [Nat.zero_add] using interpolationSegments_chain 0 last
    exact hc.render_at_finish ht
  · simpa only [blend_zero] using inputInterpolation_edge ht hi (θ := 0) le_rfl zero_le_one

private theorem time_mem_some_edge {t : ℕ → ℝ} (last : ℕ) :
    0 < last → ∀ x : ℝ, x ∈ Set.Icc (t 0) (t last) →
      ∃ i : ℕ, i < last ∧ t i ≤ x ∧ x ≤ t (i + 1) := by
  induction last with
  | zero => intro h; omega
  | succ n ih =>
      intro _ x hx
      by_cases hn : n = 0
      · subst n
        exact ⟨0, by omega, hx⟩
      · by_cases hxn : x ≤ t n
        · obtain ⟨i, hi, h₀, h₁⟩ := ih (by omega) x ⟨hx.1, hxn⟩
          exact ⟨i, by omega, h₀, h₁⟩
        · exact ⟨n, Nat.lt_succ_self n, (lt_of_not_ge hxn).le, hx.2⟩

private theorem exists_blend_of_mem {a b x : ℝ} (hab : a < b)
    (hx : x ∈ Set.Icc a b) : ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ blend a b θ = x := by
  refine ⟨(x - a) / (b - a), div_nonneg (sub_nonneg.mpr hx.1) (sub_pos.mpr hab).le,
    (div_le_one (sub_pos.mpr hab)).mpr (by linarith [hx.2]), ?_⟩
  unfold blend
  field_simp [(sub_pos.mpr hab).ne']
  ring

/-- The complete native output is within ε of the original piecewise-linear input
at every real time in the supplied finite input interval, including singleton inputs. -/
theorem nativeReconstruction_uniform_error {t y : ℕ → ℝ} (ht : StrictMono t)
    {ε : ℝ} (hε : 0 ≤ ε) (last : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (t 0) (t last)) :
    |inputInterpolation t y last x - nativeReconstruction t y ε last x| ≤ ε := by
  by_cases hn : last = 0
  · subst last
    have heq : x = t 0 := le_antisymm hx.2 hx.1
    subst x
    rw [inputInterpolation_sample ht le_rfl]
    exact nativeReconstruction_sample_error ht hε le_rfl
  · obtain ⟨i, hi, h₀, h₁⟩ := time_mem_some_edge last (by omega) x hx
    obtain ⟨θ, hθ₀, hθ₁, rfl⟩ := exists_blend_of_mem (ht (Nat.lt_succ_self i)) ⟨h₀, h₁⟩
    rw [inputInterpolation_edge ht hi hθ₀ hθ₁]
    exact nativeReconstruction_edge_error ht hε hi hθ₀ hθ₁

/-- Finite native Swing has one continuous fitted-line reconstruction with both
the sample guarantee and the full original-input interpolation guarantee. -/
theorem nativeReconstruction_spec {t y : ℕ → ℝ} (ht : StrictMono t)
    {ε : ℝ} (hε : 0 ≤ ε) (last : ℕ) :
    Continuous (nativeReconstruction t y ε last) ∧
      (∀ j ≤ last, |y j - nativeReconstruction t y ε last (t j)| ≤ ε) ∧
      ∀ x ∈ Set.Icc (t 0) (t last),
        |inputInterpolation t y last x - nativeReconstruction t y ε last x| ≤ ε :=
  ⟨nativeReconstruction_continuous ht hε last,
    fun _ hj => nativeReconstruction_sample_error ht hε hj,
    fun _ hx => nativeReconstruction_uniform_error ht hε last hx⟩

end SwingRepair
