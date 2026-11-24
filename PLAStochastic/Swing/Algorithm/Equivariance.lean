import PLAStochastic.Swing.DenseSampling.Rejection.LongOutputCover

/-! # Exact positive time and amplitude equivariance of the actual native SSE recursion -/
noncomputable section
open Classical
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

private theorem native_scaling_residual (c d y q m t a : ℝ) (hc : c ≠ 0) :
    d*y-(d*q+(d/c*m)*(c*t-c*a)) = d*(y-(q+m*(t-a))) := by
  field_simp

/-- Feasibility itself commutes with positive rescaling. -/
theorem feasibleSlope_scaling_iff {ι : Type*} (s : Finset ι) (t y : ι → ℝ)
    (a q ε m : ℝ) {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    feasibleSlope s (fun i => c*t i) (fun i => d*y i) (c*a) (d*q) (d*ε) (d/c*m) ↔
      feasibleSlope s t y a q ε m := by
  unfold feasibleSlope
  simp only [native_scaling_residual _ _ _ _ _ _ _ hc.ne', abs_mul, abs_of_pos hd,
    mul_le_mul_iff_of_pos_left hd]

theorem nativePrefixFeasible_scaling_iff (t y : ℕ → ℝ) (ε q : ℝ) (s e : ℕ)
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    nativePrefixFeasible (fun i => c*t i) (fun i => d*y i) (d*ε) s e (d*q) ↔
      nativePrefixFeasible t y ε s e q := by
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨c/d*m, (feasibleSlope_scaling_iff _ t y (t s) q ε (c/d*m) hc hd).mp ?_⟩
    have he : d/c*(c/d*m) = m := by field_simp
    simpa only [he] using hm
  · rintro ⟨m, hm⟩
    exact ⟨d/c*m, (feasibleSlope_scaling_iff _ t y (t s) q ε m hc hd).mpr hm⟩

theorem nativeSelectedSlope_scaling {ι : Type*} (s : Finset ι) (hne : s.Nonempty)
    (t y : ι → ℝ) (a q ε : ℝ) {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    nativeSelectedSlope s hne (fun i => c*t i) (fun i => d*y i) (c*a) (d*q) (d*ε) =
      (d/c)*nativeSelectedSlope s hne t y a q ε := by
  have hdc : 0 < d/c := div_pos hd hc
  have hL : nativeConeLower s hne (fun i => c*t i) (fun i => d*y i) (c*a) (d*q) (d*ε) =
      (d/c)*nativeConeLower s hne t y a q ε := by
    unfold nativeConeLower
    have he := map_finset_sup' (OrderIso.mulLeft₀ (d/c) hdc) hne (fun i => slopeLower (t i) (y i) a q ε)
    change (d/c)*s.sup' hne (fun i => slopeLower (t i) (y i) a q ε) = _ at he
    rw [he]
    apply Finset.sup'_congr hne rfl
    intro i _
    dsimp only [slopeLower]
    rw [show d*y i-d*q-d*ε = d*(y i-q-ε) by ring, ← mul_sub, mul_div_mul_comm]
    rfl
  have hU : nativeConeUpper s hne (fun i => c*t i) (fun i => d*y i) (c*a) (d*q) (d*ε) =
      (d/c)*nativeConeUpper s hne t y a q ε := by
    unfold nativeConeUpper
    have he := map_finset_inf' (OrderIso.mulLeft₀ (d/c) hdc) hne (fun i => slopeUpper (t i) (y i) a q ε)
    change (d/c)*s.inf' hne (fun i => slopeUpper (t i) (y i) a q ε) = _ at he
    rw [he]
    apply Finset.inf'_congr hne rfl
    intro i _
    dsimp only [slopeUpper]
    rw [show d*y i-d*q+d*ε = d*(y i-q+ε) by ring, ← mul_sub, mul_div_mul_comm]
    rfl
  have hC : nativeSSECross s (fun i => c*t i) (fun i => d*y i) (c*a) (d*q) =
      (c*d)*nativeSSECross s t y a q := by
    unfold nativeSSECross
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hD : nativeSSETimeSquare s (fun i => c*t i) (c*a) = c^2*nativeSSETimeSquare s t a := by
    unfold nativeSSETimeSquare
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hA : nativeLeastSquares s (fun i => c*t i) (fun i => d*y i) (c*a) (d*q) =
      (d/c)*nativeLeastSquares s t y a q := by
    unfold nativeLeastSquares
    rw [hC, hD, mul_div_mul_comm]
    have he : c*d/c^2 = d/c := by field_simp
    rw [he]
  unfold nativeSelectedSlope nativeClippedSlope
  rw [hL, hU, hA, mul_max_of_nonneg _ _ hdc.le, mul_min_of_nonneg _ _ hdc.le]

/-- Positive coordinate scaling changes only the fitted values and slopes. -/
def nativeScaleSegment (c d : ℝ) (seg : NativeSegment) : NativeSegment :=
  ⟨seg.start, seg.finish, d*seg.anchorValue, (d/c)*seg.slope⟩

theorem nativeOutputSegment_scaling (t y : ℕ → ℝ) (ε q : ℝ) (s e : ℕ) (hse : s < e)
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    nativeOutputSegment (fun i => c*t i) (fun i => d*y i) (d*ε) s e (d*q) hse =
      nativeScaleSegment c d (nativeOutputSegment t y ε s e q hse) := by
  unfold nativeOutputSegment nativeScaleSegment
  rw [nativeSelectedSlope_scaling _ _ _ _ _ _ _ hc hd]

theorem nativeSegmentEndpoint_scaling (t : ℕ → ℝ) (seg : NativeSegment)
    {c d : ℝ} (hc : 0 < c) :
    nativeSegmentEndpoint (fun j => c*t j) (nativeScaleSegment c d seg) =
      d*nativeSegmentEndpoint t seg := by
  unfold nativeSegmentEndpoint nativeScaleSegment
  field_simp

theorem scanNative_scaling (t y : ℕ → ℝ) (ε : ℝ) (fuel s e : ℕ) (q : ℝ) (hse : s < e)
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    scanNative (fun i => c*t i) (fun i => d*y i) (d*ε) fuel s e (d*q) hse =
      (scanNative t y ε fuel s e q hse).map (nativeScaleSegment c d) := by
  induction fuel generalizing s e q with
  | zero => simp only [scanNative, List.map_singleton, nativeOutputSegment_scaling t y ε q s e hse hc hd]
  | succ fuel ih =>
    by_cases ha : nativePrefixFeasible t y ε s (e+1) q
    · have ha' := (nativePrefixFeasible_scaling_iff t y ε q s (e+1) hc hd).mpr ha
      simp only [scanNative, if_pos ha, if_pos ha']
      exact ih s (e+1) q (by omega)
    · have ha' : ¬ nativePrefixFeasible (fun i => c*t i) (fun i => d*y i) (d*ε) s (e+1) (d*q) :=
        fun h => ha ((nativePrefixFeasible_scaling_iff t y ε q s (e+1) hc hd).mp h)
      simp only [scanNative, if_neg ha, if_neg ha', List.map_cons,
        nativeOutputSegment_scaling t y ε q s e hse hc hd, nativeSegmentEndpoint_scaling t _ hc]
      rw [ih]

theorem nativeStream_scaling (t y : ℕ → ℝ) (ε : ℝ) (last : ℕ)
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    nativeStream (fun i => c*t i) (fun i => d*y i) (d*ε) last =
      (nativeStream t y ε last).map (nativeScaleSegment c d) := by
  cases last with
  | zero => rfl
  | succ n => exact scanNative_scaling t y ε n 0 1 (y 0) (by omega) hc hd

theorem nativeDurationAt_scaling (t : ℕ → ℝ) (segs : List NativeSegment) (k : ℕ) (c d : ℝ) :
    nativeDurationAt (fun j => c*t j) (segs.map (nativeScaleSegment c d)) k = c*nativeDurationAt t segs k := by
  have hz : nativeScaleSegment c d ⟨0, 0, 0, 0⟩ = ⟨0, 0, 0, 0⟩ := by
    simp only [nativeScaleSegment, mul_zero]
  have he : nativeSegmentAt (segs.map (nativeScaleSegment c d)) k =
      nativeScaleSegment c d (nativeSegmentAt segs k) := by
    unfold nativeSegmentAt
    rw [List.getElem?_map, ← hz, Option.getD_map, hz]
  simp only [nativeDurationAt, he, nativeElapsedTime, nativeScaleSegment]
  ring

theorem nativePostFirstMaximum_scaling (t : ℕ → ℝ) (segs : List NativeSegment)
    {c d : ℝ} (hc : 0 < c) :
    nativePostFirstMaximum (fun j => c*t j) (segs.map (nativeScaleSegment c d)) =
      c*nativePostFirstMaximum t segs := by
  unfold nativePostFirstMaximum
  simp only [List.length_map]
  have he := map_finset_sup' (OrderIso.mulLeft₀ c hc)
    (show (Finset.range (segs.length+1)).Nonempty by simp)
    (fun k => max 0 (nativeDurationAt t segs (k+1)))
  change c*((Finset.range (segs.length+1)).sup' _ _) = _ at he
  rw [he]
  apply Finset.sup'_congr _ rfl
  intro k _
  simp only [nativeDurationAt_scaling, Function.comp_def, OrderIso.mulLeft₀_apply, mul_max_of_nonneg _ _ hc.le, mul_zero]

end SwingRepair
