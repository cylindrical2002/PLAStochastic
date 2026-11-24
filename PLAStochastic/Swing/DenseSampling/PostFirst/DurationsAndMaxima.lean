import PLAStochastic.Swing.DenseSampling.Empirical.BrownianBoundaryLaw

/-! # Actual post-first durations, maxima, and covered time -/
noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- Actual duration at index k, with zero for a missing segment. -/
def nativeDurationAt (t : ℕ → ℝ) (segs : List NativeSegment) (k : ℕ) : ℝ :=
  nativeElapsedTime t (nativeSegmentAt segs k)

theorem nativeDurationAt_eq_zero {t : ℕ → ℝ} {segs : List NativeSegment} {k : ℕ}
    (hk : segs.length ≤ k) : nativeDurationAt t segs k = 0 := by
  simp [nativeDurationAt, nativeElapsedTime, nativeSegmentAt, List.getElem?_eq_none hk]

/-- Maximum duration after the first interval. The EOF interval is included.
The extra missing index supplies zero, including for empty output. -/
def nativePostFirstMaximum (t : ℕ → ℝ) (segs : List NativeSegment) : ℝ :=
  (Finset.range (segs.length + 1)).sup' (by simp)
    (fun k => max 0 (nativeDurationAt t segs (k + 1)))

/-- Total duration covered by post-first intervals at least a long. This also
includes a terminal interval clipped at the finite observation horizon. -/
def nativePostFirstLongTime (t : ℕ → ℝ) (segs : List NativeSegment) (a : ℝ) : ℝ :=
  ∑ k ∈ Finset.range segs.length,
    if a ≤ nativeDurationAt t segs (k + 1) then nativeDurationAt t segs (k + 1) else 0

theorem nativePostFirstMaximum_nonneg (t : ℕ → ℝ) (segs : List NativeSegment) :
    0 ≤ nativePostFirstMaximum t segs := by
  exact (le_max_left _ _).trans (Finset.le_sup' (fun k => max 0 (nativeDurationAt t segs (k + 1))) (Finset.mem_range.mpr (by omega : 0 < segs.length + 1)))

theorem nativeDurationAt_le_postFirstMaximum {t : ℕ → ℝ} {segs : List NativeSegment}
    {k : ℕ} (hk : k < segs.length) :
    nativeDurationAt t segs (k + 1) ≤ nativePostFirstMaximum t segs := by
  exact (le_max_right _ _).trans (Finset.le_sup' (fun k => max 0 (nativeDurationAt t segs (k + 1))) (Finset.mem_range.mpr (by omega : k < segs.length + 1)))

theorem NativeChain.durationAt_nonneg {t y : ℕ → ℝ} (ht : Monotone t)
    {ε q : ℝ} {s last : ℕ} {segs : List NativeSegment}
    (hc : NativeChain t y ε s q last segs) (k : ℕ) : 0 ≤ nativeDurationAt t segs k := by
  by_cases hk : k < segs.length
  · rw [nativeDurationAt, nativeSegmentAt_eq_getElem hk]
    exact sub_nonneg.mpr (ht (hc.getElem_bounds hk).2.2.le)
  · rw [nativeDurationAt_eq_zero (Nat.le_of_not_gt hk)]

/-- Every actual segment fits within the full time budget, including EOF. -/
theorem NativeChain.durationAt_le_budget {t y : ℕ → ℝ} (ht : Monotone t)
    {ε q : ℝ} {s last : ℕ} {segs : List NativeSegment}
    (hc : NativeChain t y ε s q last segs) (hsl : s ≤ last) (k : ℕ) :
    nativeDurationAt t segs k ≤ t last - t s := by
  by_cases hk : k < segs.length
  · rw [nativeDurationAt, nativeSegmentAt_eq_getElem hk]
    exact sub_le_sub (ht (hc.getElem_bounds hk).2.1) (ht (hc.getElem_bounds hk).1)
  · rw [nativeDurationAt_eq_zero (Nat.le_of_not_gt hk)]
    exact sub_nonneg.mpr (ht hsl)

theorem NativeChain.postFirstMaximum_le_budget {t y : ℕ → ℝ} (ht : Monotone t)
    {ε q : ℝ} {s last : ℕ} {segs : List NativeSegment}
    (hc : NativeChain t y ε s q last segs) (hsl : s ≤ last) :
    nativePostFirstMaximum t segs ≤ t last - t s := by
  apply Finset.sup'_le
  intro k _
  exact max_le (sub_nonneg.mpr (ht hsl)) (hc.durationAt_le_budget ht hsl (k + 1))

private theorem list_sum_getD {α : Type*} (xs : List α) (d : α) (w : α → ℝ) :
    (∑ k ∈ Finset.range xs.length, w (xs[k]?.getD d)) = (xs.map w).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.length_cons, Finset.sum_range_succ', List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some, List.map_cons, List.sum_cons, ih, add_comm]

theorem sum_nativeDurationAt (t : ℕ → ℝ) (segs : List NativeSegment) :
    (∑ k ∈ Finset.range segs.length, nativeDurationAt t segs k) =
      (segs.map (nativeElapsedTime t)).sum :=
  list_sum_getD segs _ _

theorem sum_nativePostFirstDuration (t : ℕ → ℝ) (segs : List NativeSegment) :
    (∑ k ∈ Finset.range segs.length, nativeDurationAt t segs (k + 1)) + nativeDurationAt t segs 0 =
      (segs.map (nativeElapsedTime t)).sum := by
  rw [← Finset.sum_range_succ', Finset.sum_range_succ, nativeDurationAt_eq_zero le_rfl,
    add_zero, sum_nativeDurationAt]

theorem NativeChain.postFirstLongTime_nonneg {t y : ℕ → ℝ} (ht : Monotone t)
    {ε q : ℝ} {s last : ℕ} {segs : List NativeSegment}
    (hc : NativeChain t y ε s q last segs) (a : ℝ) :
    0 ≤ nativePostFirstLongTime t segs a := by
  apply Finset.sum_nonneg
  intro k _
  split_ifs
  · exact hc.durationAt_nonneg ht _
  · exact le_rfl

theorem NativeChain.postFirstLongTime_le_budget {t y : ℕ → ℝ} (ht : Monotone t)
    {ε q : ℝ} {s last : ℕ} {segs : List NativeSegment}
    (hc : NativeChain t y ε s q last segs) (a : ℝ) :
    nativePostFirstLongTime t segs a ≤ t last - t s := by
  have hb : nativePostFirstLongTime t segs a ≤
      ∑ k ∈ Finset.range segs.length, nativeDurationAt t segs (k + 1) := by
    apply Finset.sum_le_sum
    intro k _
    split_ifs
    · exact le_rfl
    · exact hc.durationAt_nonneg ht _
  have hs := sum_nativePostFirstDuration t segs
  rw [hc.sum_elapsedTime] at hs
  linarith [hc.durationAt_nonneg ht 0]

/-- The deterministic indicator bound used for time-weighted convergence. -/
theorem NativeChain.postFirstLongTime_le_indicator {t y : ℕ → ℝ} (ht : Monotone t)
    {ε q : ℝ} {s last : ℕ} {segs : List NativeSegment}
    (hc : NativeChain t y ε s q last segs) (a : ℝ) :
    nativePostFirstLongTime t segs a ≤
      if a ≤ nativePostFirstMaximum t segs then t last - t s else 0 := by
  split_ifs with ha
  · exact hc.postFirstLongTime_le_budget ht a
  · have hz : nativePostFirstLongTime t segs a = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [if_neg]
      intro hd
      exact ha (hd.trans (nativeDurationAt_le_postFirstMaximum (Finset.mem_range.mp hk)))
    rw [hz]

private theorem measurable_code_duration (t : ℕ → ℝ) (k : ℕ) :
    Measurable (fun c : ℕ → ℕ × ℕ × ℝ × ℝ => t (c k).2.1 - t (c k).1) := by
  have ht : Measurable t := measurable_of_countable t
  exact (ht.comp (measurable_pi_apply k).snd.fst).sub (ht.comp (measurable_pi_apply k).fst)

theorem measurable_nativePostFirstMaximum_of_code {Ω : Type*} [MeasurableSpace Ω]
    (t : ℕ → ℝ) {segs : Ω → List NativeSegment}
    (hcode : Measurable (fun ω => nativeOutputCode (segs ω))) :
    Measurable (fun ω => nativePostFirstMaximum t (segs ω)) := by
  let F (c : ℕ × (ℕ → ℕ × ℕ × ℝ × ℝ)) : ℝ :=
    (Finset.range (c.1 + 1)).sup' (by simp) (fun k => max 0 (t (c.2 (k + 1)).2.1 - t (c.2 (k + 1)).1))
  have hF : Measurable F := by
    apply measurable_from_prod_countable_right
    intro n
    dsimp only [F]
    have hs : Measurable ((Finset.range (n + 1)).sup' (by simp)
        (fun k (c : ℕ → ℕ × ℕ × ℝ × ℝ) => max 0 (t (c (k + 1)).2.1 - t (c (k + 1)).1))) :=
      Finset.measurable_sup' (by simp) (fun k _ => (measurable_const (a := (0 : ℝ))).max (measurable_code_duration t (k + 1)))
    convert hs using 1
    ext c
    simp only [Finset.sup'_apply]
  simpa only [Function.comp_def, F, nativeOutputCode, nativeSegmentCode, nativePostFirstMaximum,
    nativeDurationAt, nativeElapsedTime, nativeSegmentAt, List.getD_eq_getElem?_getD] using hF.comp hcode

theorem measurable_nativePostFirstLongTime_of_code {Ω : Type*} [MeasurableSpace Ω]
    (t : ℕ → ℝ) {segs : Ω → List NativeSegment} (a : ℝ)
    (hcode : Measurable (fun ω => nativeOutputCode (segs ω))) :
    Measurable (fun ω => nativePostFirstLongTime t (segs ω) a) := by
  let F (c : ℕ × (ℕ → ℕ × ℕ × ℝ × ℝ)) : ℝ :=
    ∑ k ∈ Finset.range c.1, if a ≤ t (c.2 (k + 1)).2.1 - t (c.2 (k + 1)).1
      then t (c.2 (k + 1)).2.1 - t (c.2 (k + 1)).1 else 0
  have hF : Measurable F := by
    apply measurable_from_prod_countable_right
    intro n
    dsimp only [F]
    apply Finset.measurable_sum
    intro k _
    exact (measurable_code_duration t (k + 1)).ite
      (measurableSet_le measurable_const (measurable_code_duration t (k + 1))) measurable_const
  simpa only [Function.comp_def, F, nativeOutputCode, nativeSegmentCode, nativePostFirstLongTime,
    nativeDurationAt, nativeElapsedTime, nativeSegmentAt, List.getD_eq_getElem?_getD] using hF.comp hcode

/-- Positive exceedance of the maximum means a genuine post-first output
segment has that duration; the artificial zero indices disappear. -/
theorem le_nativePostFirstMaximum_iff {t : ℕ → ℝ} {segs : List NativeSegment}
    {a : ℝ} (ha : 0 < a) : a ≤ nativePostFirstMaximum t segs ↔
      ∃ k : ℕ, 1 ≤ k ∧ k < segs.length ∧ a ≤ nativeDurationAt t segs k := by
  rw [nativePostFirstMaximum, Finset.le_sup'_iff]
  constructor
  · rintro ⟨j, _, hj⟩
    have hd : a ≤ nativeDurationAt t segs (j + 1) := (le_max_iff.mp hj).resolve_left (not_le.mpr ha)
    have hk : j + 1 < segs.length := by
      by_contra hk
      rw [nativeDurationAt_eq_zero (Nat.le_of_not_gt hk)] at hd
      exact (not_le.mpr ha) hd
    exact ⟨j + 1, by omega, hk, hd⟩
  · rintro ⟨k, hk, hklen, hd⟩
    refine ⟨k - 1, Finset.mem_range.mpr (by omega), ?_⟩
    simpa only [Nat.sub_add_cancel hk] using hd.trans (le_max_right 0 (nativeDurationAt t segs k))

theorem nativePostFirstMaximum_eq_zero_of_length_le_one (t : ℕ → ℝ)
    {segs : List NativeSegment} (hlen : segs.length ≤ 1) : nativePostFirstMaximum t segs = 0 := by
  apply le_antisymm _ (nativePostFirstMaximum_nonneg t segs)
  apply Finset.sup'_le
  intro k _
  rw [nativeDurationAt_eq_zero (by omega : segs.length ≤ k + 1), max_self]

/-- Finite native output remains measurable under almost surely measurable
observations, without assuming a specially chosen Brownian version. -/
theorem aemeasurable_nativeOutputCode {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (t : ℕ → ℝ) (ht : StrictMono t) (Y : ℕ → Ω → ℝ) (ε : ℝ) (N : ℕ)
    (hY : ∀ j, AEMeasurable (Y j) μ) :
    AEMeasurable (fun ω => nativeOutputCode (nativeStream t (fun j => Y j ω) ε N)) μ := by
  have hc := measurable_nativeStream_output t ht (fun j (y : ℕ → ℝ) => y j) ε N
    (fun j _ => measurable_pi_apply j)
  exact hc.comp_aemeasurable (aemeasurable_pi_lambda _ hY)

def brownianNativePostFirstMaximum {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (ε H : ℝ) (h : ℝ≥0) (ω : Ω) : ℝ :=
  nativePostFirstMaximum (fun j => (j : ℝ) * h) (brownianNativeMeshStream B ε H h ω)

def brownianNativePostFirstLongTime {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (ε H a : ℝ) (h : ℝ≥0) (ω : Ω) : ℝ :=
  nativePostFirstLongTime (fun j => (j : ℝ) * h) (brownianNativeMeshStream B ε H h ω) a

theorem aemeasurable_brownianNativePostFirstMaximum {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    (ε H : ℝ) {h : ℝ≥0} (hh : h ≠ 0) :
    AEMeasurable (brownianNativePostFirstMaximum B ε H h) μ := by
  let t (j : ℕ) : ℝ := (j : ℝ) * h
  have ht : StrictMono t := strictMono_mesh_times (show (0 : ℝ≥0) < h from pos_iff_ne_zero.mpr hh)
  have hc := measurable_nativeStream_output t ht (fun j (y : ℕ → ℝ) => y j) ε ⌊H / (h : ℝ)⌋₊
    (fun j _ => measurable_pi_apply j)
  exact (measurable_nativePostFirstMaximum_of_code t hc).comp_aemeasurable
    (aemeasurable_pi_lambda _ (fun j : ℕ => hB.aemeasurable ((j : ℝ≥0) * h)))

theorem aemeasurable_brownianNativePostFirstLongTime {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    (ε H a : ℝ) {h : ℝ≥0} (hh : h ≠ 0) :
    AEMeasurable (brownianNativePostFirstLongTime B ε H a h) μ := by
  let t (j : ℕ) : ℝ := (j : ℝ) * h
  have ht : StrictMono t := strictMono_mesh_times (show (0 : ℝ≥0) < h from pos_iff_ne_zero.mpr hh)
  have hc := measurable_nativeStream_output t ht (fun j (y : ℕ → ℝ) => y j) ε ⌊H / (h : ℝ)⌋₊
    (fun j _ => measurable_pi_apply j)
  exact (measurable_nativePostFirstLongTime_of_code t a hc).comp_aemeasurable
    (aemeasurable_pi_lambda _ (fun j : ℕ => hB.aemeasurable ((j : ℝ≥0) * h)))

theorem brownianNativePostFirstMaximum_bounds {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    {ε H : ℝ} (hε : 0 ≤ ε) (hH : 0 ≤ H) {h : ℝ≥0} (hh : h ≠ 0) (ω : Ω) :
    0 ≤ brownianNativePostFirstMaximum B ε H h ω ∧
      brownianNativePostFirstMaximum B ε H h ω ≤ H := by
  have hh' : (0 : ℝ) < h := by exact_mod_cast (pos_iff_ne_zero.mpr hh)
  have hc := nativeStream_spec (fun j => (j : ℝ) * h) (fun j => B ((j : ℝ≥0) * h) ω)
    (strictMono_mesh_times hh') hε ⌊H / (h : ℝ)⌋₊
  refine ⟨nativePostFirstMaximum_nonneg _ _, ?_⟩
  have hb := hc.postFirstMaximum_le_budget (strictMono_mesh_times hh').monotone (Nat.zero_le _)
  have hN := (le_div_iff₀ hh').mp (Nat.floor_le (div_nonneg hH hh'.le))
  exact hb.trans (by simpa only [Nat.cast_zero, zero_mul, sub_zero] using hN)

theorem brownianNativePostFirstLongTime_bounds {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    {ε H : ℝ} (hε : 0 ≤ ε) (hH : 0 ≤ H) (a : ℝ) {h : ℝ≥0} (hh : h ≠ 0) (ω : Ω) :
    0 ≤ brownianNativePostFirstLongTime B ε H a h ω ∧
      brownianNativePostFirstLongTime B ε H a h ω ≤
        if a ≤ brownianNativePostFirstMaximum B ε H h ω then H else 0 := by
  have hh' : (0 : ℝ) < h := by exact_mod_cast (pos_iff_ne_zero.mpr hh)
  have hc := nativeStream_spec (fun j => (j : ℝ) * h) (fun j => B ((j : ℝ≥0) * h) ω)
    (strictMono_mesh_times hh') hε ⌊H / (h : ℝ)⌋₊
  refine ⟨hc.postFirstLongTime_nonneg (strictMono_mesh_times hh').monotone a, ?_⟩
  have hb := hc.postFirstLongTime_le_indicator (strictMono_mesh_times hh').monotone a
  have hN := (le_div_iff₀ hh').mp (Nat.floor_le (div_nonneg hH hh'.le))
  simp only [Nat.cast_zero, zero_mul, sub_zero] at hb
  change brownianNativePostFirstLongTime B ε H a h ω ≤
    (if a ≤ brownianNativePostFirstMaximum B ε H h ω then (⌊H / (h : ℝ)⌋₊ : ℝ) * h else 0) at hb
  refine hb.trans ?_
  split_ifs
  · exact hN
  · exact le_rfl

end SwingRepair
