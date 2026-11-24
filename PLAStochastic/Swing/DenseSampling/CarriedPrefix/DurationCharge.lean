import PLAStochastic.Swing.DenseSampling.CarriedPrefix.CarryCoordinates

/-! # Genuine carried continuations are charged to actual segment durations -/
noncomputable section
open Classical
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- A real rejection prevents the local carried-prefix duration from crossing
that endpoint. No property of the chosen feasible slope is used. -/
theorem nativeCarriedFiniteDuration_le_of_reject (y : ℕ → ℝ) (ε q : ℝ)
    {h : ℝ} (hh : 0 ≤ h) {b e : ℕ} (hbe : b < e)
    (hr : ¬ nativePrefixFeasible (fun j => (j : ℝ)*h) y ε b (e+1) q) (K : ℕ) :
    nativeCarriedFiniteDuration (nativeCarriedFuture y q b) (nativeCarriedState y ε q b) ε h K ≤
      ((e : ℝ)-(b : ℝ))*h := by
  apply Finset.sup'_le
  intro j _
  split_ifs with hf
  · have hfit := (nativeCarriedFit_state_iff_nativePrefix y ε q h b j).mp hf
    have hj : (b+1)+j ≤ e := by
      by_contra hn
      exact hr (nativePrefixFeasible_mono_end hfit (by omega))
    have hjR : (b : ℝ)+1+(j : ℝ) ≤ (e : ℝ) := by exact_mod_cast hj
    exact mul_le_mul_of_nonneg_right (by linarith) hh
  · have hle : (b : ℝ) ≤ e := by exact_mod_cast hbe.le
    exact mul_nonneg (sub_nonneg.mpr hle) hh

/-- Either a true next rejection or enough remaining EOF horizon supplies a
valid duration charge for the capped carried continuation. -/
theorem nativeCarriedTruncatedDuration_le_span (y : ℕ → ℝ) (ε q : ℝ)
    (h H : ℝ≥0) {b e : ℕ} (hbe : b < e)
    (hr : (¬ nativePrefixFeasible (fun j => (j : ℝ)*(h : ℝ)) y ε b (e+1) q) ∨
      (H : ℝ) ≤ ((e : ℝ)-(b : ℝ))*(h : ℝ)) :
    nativeCarriedTruncatedDuration (nativeCarriedFuture y q b) (nativeCarriedState y ε q b) ε h H ≤
      ((e : ℝ)-(b : ℝ))*(h : ℝ) := by
  rcases hr with hr | hr
  · exact (min_le_right _ _).trans (nativeCarriedFiniteDuration_le_of_reject y ε q h.coe_nonneg hbe hr _)
  · exact (min_le_left _ _).trans hr

/-- Every actual post-first segment starting before the primary horizon pays
for its capped continuation, if the stream was observed an extra H time. -/
theorem NativeChain.carried_duration_le_elapsed {y : ℕ → ℝ} {ε : ℝ}
    {h H : ℝ≥0} {last : ℕ} {segs : List NativeSegment}
    (hc : NativeChain (fun j => (j : ℝ)*(h : ℝ)) y ε 0 (y 0) last segs)
    {k : ℕ} (hk : k < segs.length) {T : ℝ}
    (hsT : (segs[k].start : ℝ)*(h : ℝ) ≤ T)
    (horizon : T+(H : ℝ) ≤ (last : ℝ)*(h : ℝ)) :
    nativeCarriedTruncatedDuration (nativeCarriedFuture y segs[k].anchorValue segs[k].start)
      (nativeCarriedState y ε segs[k].anchorValue segs[k].start) ε h H ≤
      nativeElapsedTime (fun j => (j : ℝ)*(h : ℝ)) segs[k] := by
  have hr : (¬ nativePrefixFeasible (fun j => (j : ℝ)*(h : ℝ)) y ε segs[k].start
      (segs[k].finish+1) segs[k].anchorValue) ∨
      (H : ℝ) ≤ ((segs[k].finish : ℝ)-(segs[k].start : ℝ))*(h : ℝ) := by
    by_cases hkn : k+1 < segs.length
    · exact Or.inl (hc.getElem_reject hkn)
    · apply Or.inr
      have he := hc.getElem_last_finish hk (by omega)
      rw [he]
      nlinarith
  calc
    _ ≤ ((segs[k].finish : ℝ)-(segs[k].start : ℝ))*(h : ℝ) :=
      nativeCarriedTruncatedDuration_le_span y ε segs[k].anchorValue h H (hc.getElem_bounds hk).2.2 hr
    _ = _ := by unfold nativeElapsedTime; ring

end SwingRepair
