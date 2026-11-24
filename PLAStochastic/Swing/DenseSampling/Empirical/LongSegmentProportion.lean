import PLAStochastic.Swing.DenseSampling.Empirical.LimitingBoundarySign

/-! # Duration budgets and empirical long-segment proportions -/
noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

def nativeElapsedTime (t : ℕ → ℝ) (seg : NativeSegment) : ℝ := t seg.finish - t seg.start

def nativeLongCompletedCount (t : ℕ → ℝ) (segs : List NativeSegment) (a : ℝ) : ℕ :=
  (segs.dropLast.filter (fun seg => decide (a ≤ nativeElapsedTime t seg))).length

/-- Actual fitted junctions make every segment's elapsed time telescope,
including the terminal EOF segment. -/
theorem NativeChain.sum_elapsedTime {t y : ℕ → ℝ} {ε : ℝ} {s last : ℕ} {q : ℝ}
    {segs : List NativeSegment} (hc : NativeChain t y ε s q last segs) :
    (segs.map (nativeElapsedTime t)).sum = t last - t s := by
  induction hc with
  | empty => simp
  | terminal hv => simp only [List.map_singleton, List.sum_singleton, nativeElapsedTime]
  | @cons head last tail hv hr hn ih =>
      simp only [List.map_cons, List.sum_cons, ih, nativeElapsedTime]
      ring

/-- Threshold-count times threshold is bounded by total nonnegative weight. -/
theorem list_large_count_mul_le_sum {α : Type*} (xs : List α) (w : α → ℝ)
    {a : ℝ} (hw : ∀ x ∈ xs, 0 ≤ w x) :
    ((xs.filter (fun x => decide (a ≤ w x))).length : ℝ) * a ≤ (xs.map w).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := hw x List.mem_cons_self
      have hi := ih (fun y hy => hw y (List.mem_cons_of_mem x hy))
      by_cases hax : a ≤ w x
      · simp only [List.filter_cons, decide_eq_true_eq, if_pos hax, List.length_cons,
          Nat.cast_add, Nat.cast_one, List.map_cons, List.sum_cons]
        nlinarith
      · simp only [List.filter_cons, decide_eq_true_eq, if_neg hax, List.map_cons, List.sum_cons]
        linarith

/-- The completed long-interval count is controlled by the true time budget. -/
theorem NativeChain.longCompletedCount_mul_le {t y : ℕ → ℝ} (ht : Monotone t)
    {ε : ℝ} {s last : ℕ} {q : ℝ} {segs : List NativeSegment}
    (hc : NativeChain t y ε s q last segs) {a : ℝ} (ha : 0 ≤ a) :
    (nativeLongCompletedCount t segs a : ℝ) * a ≤ t last - t s := by
  have hw : ∀ seg ∈ segs, 0 ≤ nativeElapsedTime t seg := by
    intro seg hs
    exact sub_nonneg.mpr (ht (hc.segment_bounds seg hs).2.2.le)
  have hfilter := ((List.dropLast_sublist segs).filter
    (fun seg => decide (a ≤ nativeElapsedTime t seg))).length_le
  have hlen : ((segs.dropLast.filter (fun seg => decide (a ≤ nativeElapsedTime t seg))).length : ℝ) ≤
      ((segs.filter (fun seg => decide (a ≤ nativeElapsedTime t seg))).length : ℝ) := by
    exact_mod_cast hfilter
  have hsum := list_large_count_mul_le_sum segs (nativeElapsedTime t) (a := a) hw
  exact ((mul_le_mul_of_nonneg_right hlen ha).trans hsum).trans_eq hc.sum_elapsedTime

/-- Every positive-duration threshold has vanishing count proportion as soon
as the actual number of completed native recordings diverges. -/
theorem native_long_completed_proportion_tendsto_zero (f : C(ℝ, ℝ))
    {T ε a : ℝ} (hε : 0 ≤ ε) (ha : 0 < a)
    {ι : Type*} {l : Filter ι} {h : ι → ℝ} {N : ι → ℕ}
    (hh : ∀ i, 0 < h i) (hN : ∀ i, (N i : ℝ) * h i ≤ T)
    (hcount : Tendsto (fun i => nativeCompletedCount (fun j => (j : ℝ) * h i)
      (fun j => f ((j : ℝ) * h i)) ε (N i)) l atTop) :
    Tendsto (fun i =>
      (nativeLongCompletedCount (fun j => (j : ℝ) * h i)
        (nativeStream (fun j => (j : ℝ) * h i) (fun j => f ((j : ℝ) * h i)) ε (N i)) a : ℝ) /
      (nativeCompletedCount (fun j => (j : ℝ) * h i)
        (fun j => f ((j : ℝ) * h i)) ε (N i) : ℝ)) l (𝓝 0) := by
  have hden := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp hcount
  apply squeeze_zero (fun i => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (fun i => ?_) (hden.const_div_atTop (T / a))
  have ht := strictMono_mesh_times (hh i)
  have hc := nativeStream_spec (fun j => (j : ℝ) * h i)
    (fun j => f ((j : ℝ) * h i)) ht hε (N i)
  have hb := hc.longCompletedCount_mul_le ht.monotone ha.le
  have hnum : (nativeLongCompletedCount (fun j => (j : ℝ) * h i)
      (nativeStream (fun j => (j : ℝ) * h i) (fun j => f ((j : ℝ) * h i)) ε (N i)) a : ℝ) ≤ T / a := by
    apply (le_div_iff₀ ha).mpr
    simpa only [Nat.cast_zero, zero_mul, sub_zero] using hb.trans (by simpa using hN i)
  exact div_le_div_of_nonneg_right hnum (Nat.cast_nonneg _)

end SwingRepair
