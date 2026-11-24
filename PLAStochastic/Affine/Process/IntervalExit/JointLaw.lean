import PLAStochastic.Affine.Process.IntervalExit.TimeDensity

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

def intervalExitJointMeasure {Ω : Type*} [MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ)
    (μ : Measure Ω) (x r : ℝ) : Measure (ℝ × ℝ) :=
  μ.map (fun ω => ((intervalTouchClock B x r ω : ℝ),intervalTouchEndpoint B x r ω))

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

private theorem intervalExit_restrict_partition (hB : IsBrownianReal B μ)
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) :
    μ.restrict {ω | intervalTouchEndpoint B x r ω = 0} +
      μ.restrict {ω | intervalTouchEndpoint B x r ω = r} = μ := by
  have hd : Disjoint {ω | intervalTouchEndpoint B x r ω = 0} {ω | intervalTouchEndpoint B x r ω = r} := by
    apply Set.disjoint_left.mpr
    intro ω h0 hrω
    exact hr.ne' (h0.symm.trans hrω).symm
  have hm : NullMeasurableSet {ω | intervalTouchEndpoint B x r ω = r} μ :=
    (intervalTouchEndpoint_aemeasurable hB hr hx).nullMeasurableSet_preimage (measurableSet_singleton r)
  rw [← Measure.restrict_union₀ hd.aedisjoint hm]
  exact Measure.restrict_eq_self_of_ae_mem (intervalTouchEndpoint_boundary_ae hB hr hx)

private theorem intervalExitSideMeasure_map_endpoint (hB : IsBrownianReal B μ)
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) (side : ℝ) :
    (intervalExitSideMeasure B μ x r side).map (fun t => (t,side)) =
      (μ.restrict {ω | intervalTouchEndpoint B x r ω = side}).map
        (fun ω => ((intervalTouchClock B x r ω : ℝ),intervalTouchEndpoint B x r ω)) := by
  unfold intervalExitSideMeasure
  rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop)
    ((intervalTouchClock_aemeasurable hB hr x).coe_nnreal_real.restrict)]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem₀ ((intervalTouchEndpoint_aemeasurable hB hr hx).nullMeasurableSet_preimage
    (measurableSet_singleton side))] with ω hω
  exact Prod.ext rfl hω.symm

/-- The actual time-and-endpoint joint law decomposes into the two actual side laws. -/
theorem intervalExitJointMeasure_eq_side_sum (hB : IsBrownianReal B μ)
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) :
    intervalExitJointMeasure B μ x r =
      (intervalExitSideMeasure B μ x r 0).map (fun t => (t,0)) +
      (intervalExitSideMeasure B μ x r r).map (fun t => (t,r)) := by
  let J : Ω → ℝ × ℝ := fun ω => ((intervalTouchClock B x r ω : ℝ),intervalTouchEndpoint B x r ω)
  have hm : AEMeasurable J μ :=
    ((intervalTouchClock_aemeasurable hB hr x).coe_nnreal_real).prodMk
      (intervalTouchEndpoint_aemeasurable hB hr hx)
  calc
    _ = (μ.restrict {ω | intervalTouchEndpoint B x r ω = 0} +
        μ.restrict {ω | intervalTouchEndpoint B x r ω = r}).map J :=
      congrArg (fun ρ : Measure Ω => ρ.map J) (intervalExit_restrict_partition hB hr hx).symm
    _ = (μ.restrict {ω | intervalTouchEndpoint B x r ω = 0}).map J +
        (μ.restrict {ω | intervalTouchEndpoint B x r ω = r}).map J := AEMeasurable.map_add₀ hm.restrict hm.restrict
    _ = _ := by rw [← intervalExitSideMeasure_map_endpoint hB hr hx 0,
      ← intervalExitSideMeasure_map_endpoint hB hr hx r]

/-- The complete first-touch time/endpoint law, including its endpoint atoms in space
and its genuine time densities. -/
theorem intervalExitJointMeasure_eq_boundary_density (hB : IsBrownianReal B μ)
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) :
    intervalExitJointMeasure B μ x r =
      (positiveTimeDensity (fun t => heatBoundaryLeft r t x/2)).map (fun t => (t,0)) +
      (positiveTimeDensity (fun t => heatBoundaryRight r t x/2)).map (fun t => (t,r)) := by
  rw [intervalExitJointMeasure_eq_side_sum hB hr hx,
    intervalExitSideMeasure_left_eq_density hB hr hx,intervalExitSideMeasure_right_eq_density hB hr hx]

theorem intervalExitTimeMeasure_eq_boundary_sum (hB : IsBrownianReal B μ)
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) :
    μ.map (fun ω => (intervalTouchClock B x r ω : ℝ)) =
      positiveTimeDensity (fun t => heatBoundaryLeft r t x/2) +
      positiveTimeDensity (fun t => heatBoundaryRight r t x/2) := by
  have hm := (intervalTouchClock_aemeasurable hB hr x).coe_nnreal_real
  calc
    _ = (μ.restrict {ω | intervalTouchEndpoint B x r ω = 0} +
        μ.restrict {ω | intervalTouchEndpoint B x r ω = r}).map
          (fun ω => (intervalTouchClock B x r ω : ℝ)) :=
      congrArg (fun ρ : Measure Ω => ρ.map (fun ω => (intervalTouchClock B x r ω : ℝ)))
        (intervalExit_restrict_partition hB hr hx).symm
    _ = intervalExitSideMeasure B μ x r 0+intervalExitSideMeasure B μ x r r := AEMeasurable.map_add₀ hm.restrict hm.restrict
    _ = _ := by rw [intervalExitSideMeasure_left_eq_density hB hr hx,intervalExitSideMeasure_right_eq_density hB hr hx]

theorem intervalExitJointMeasure_univ (hB : IsBrownianReal B μ)
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) : intervalExitJointMeasure B μ x r univ = 1 := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  unfold intervalExitJointMeasure
  rw [Measure.map_apply_of_aemeasurable
    (((intervalTouchClock_aemeasurable hB hr x).coe_nnreal_real).prodMk (intervalTouchEndpoint_aemeasurable hB hr hx)) MeasurableSet.univ]
  simp

theorem positiveTimeDensity_absolutelyContinuous (f : ℝ → ℝ) : positiveTimeDensity f ≪ volume :=
  (withDensity_absolutelyContinuous _ _).trans Measure.absolutelyContinuous_restrict

/-- There are no singular time components, including at time zero. -/
theorem intervalExitTimeMeasure_absolutelyContinuous (hB : IsBrownianReal B μ)
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) :
    μ.map (fun ω => (intervalTouchClock B x r ω : ℝ)) ≪ volume := by
  rw [intervalExitTimeMeasure_eq_boundary_sum hB hr hx]
  intro s hs
  rw [Measure.add_apply,(positiveTimeDensity_absolutelyContinuous _) hs,
    (positiveTimeDensity_absolutelyContinuous _) hs,zero_add]

theorem intervalTouchClock_ne_fixed_ae (hB : IsBrownianReal B μ)
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) (t : ℝ) :
    ∀ᵐ ω ∂μ, (intervalTouchClock B x r ω : ℝ) ≠ t := by
  have h := intervalExitTimeMeasure_absolutelyContinuous hB hr hx (show volume {t} = 0 by simp)
  rw [Measure.map_apply_of_aemeasurable (intervalTouchClock_aemeasurable hB hr x).coe_nnreal_real
    (measurableSet_singleton t)] at h
  rw [ae_iff]
  convert! h using 1
  congr 1
  ext ω
  simp

end BrownianAffine
