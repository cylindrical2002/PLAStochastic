import PLAStochastic.Affine.Process.IntervalExit.ContactRegularity
import PLAStochastic.Affine.Process.Killed.Boundary.Identities

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem integral_actualBrownianExponentialWith_boundedIntervalExit (hB : IsBrownianReal B μ)
    (c x r : ℝ) (T : ℝ≥0) :
    Integrable (fun ω => actualBrownianExponentialWith B c (boundedIntervalExit B x r T ω) ω) μ ∧
      (∫ ω, actualBrownianExponentialWith B c (boundedIntervalExit B x r T ω) ω ∂μ) = 1 := by
  obtain ⟨H, hH⟩ := exists_nat_ge T
  let G : ℕ → Ω → ℝ≥0 := fun n =>
    gridHittingTime (fun t ω => x + measurableBrownian hB.toIsPreBrownianReal t ω)
      (driftBarrierSet r 0) (reciprocalMesh n) (H * (n + 1))
  apply integral_actualBrownianExponentialWith_stopping_limit hB c
    (τ := fun n ω => min (G n ω : WithTop ℝ≥0) (T : WithTop ℝ≥0)) (T := T)
  · intro n
    exact (isStoppingTime_gridHittingTime (adapted_shiftedBrownian hB.toIsPreBrownianReal x)
      (measurableSet_driftBarrierSet r 0) (reciprocalMesh_pos n) (H * (n + 1))).min_const T
  · exact fun _ _ => min_le_right _ _
  · intro n
    have hc := (gridHittingTime_countable_range
      (fun t ω => x + measurableBrownian hB.toIsPreBrownianReal t ω)
      (driftBarrierSet r 0) (reciprocalMesh n) (H * (n + 1))).image
      (fun z : WithTop ℝ≥0 => min z T)
    simpa only [← Set.range_comp, Function.comp_def, G] using hc
  · have heq : ∀ᵐ ω ∂μ, ∀ n, G n ω =
        gridHittingTime (fun t ω => x + B t ω) (driftBarrierSet r 0)
          (reciprocalMesh n) (H * (n + 1)) ω :=
      ae_all_iff.mpr (fun n => gridHittingTime_shiftedBrownian_ae_eq hB.toIsPreBrownianReal
        x r (reciprocalMesh n) (H * (n + 1)))
    filter_upwards [hB.cont, heq] with ω hω heqω
    have ht := gridHittingTime_tendsto_boundedOpenExitTime
      (X := fun t ω => x + B t ω) (ω := ω) (S := driftBarrierSet r 0) (isOpen_Iio.union isOpen_Ioi) (hω.const_add x) H
    have hm := (ht.congr (fun n => (heqω n).symm)).min (tendsto_const_nhds (x := T))
    rw [← boundedOpenExitTime_min hH] at hm
    simpa only [← WithTop.coe_min, WithTop.untopD_coe, boundedIntervalExit] using hm

/-- The actual finite first-contact clock, with a harmless zero value on infinite paths. -/
def intervalTouchClock (B : ℝ≥0 → Ω → ℝ) (x r : ℝ) (ω : Ω) : ℝ≥0 :=
  (intervalTouchTime B x r ω).untopD 0

/-- The spatial endpoint at the actual first contact. -/
def intervalTouchEndpoint (B : ℝ≥0 → Ω → ℝ) (x r : ℝ) (ω : Ω) : ℝ :=
  x+B (intervalTouchClock B x r ω) ω

theorem boundedIntervalExit_eventually_eq_touch (hB : IsBrownianReal B μ)
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) :
    ∀ᵐ ω ∂μ, ∀ᶠ H : ℕ in atTop, boundedIntervalExit B x r H ω = intervalTouchClock B x r ω := by
  filter_upwards [boundedIntervalExit_eq_min_touch_ae hB hr hx] with ω hω
  have ht : Tendsto (fun H : ℕ => (H : ℝ≥0)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (eventually_ge_atTop (intervalTouchClock B x r ω))] with H hH
  rw [hω H]
  exact min_eq_left hH

theorem intervalTouchEndpoint_boundary_ae (hB : IsBrownianReal B μ)
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) :
    ∀ᵐ ω ∂μ, intervalTouchEndpoint B x r ω = 0 ∨ intervalTouchEndpoint B x r ω = r := by
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero, intervalTouchTime_ae_ne_top hB x r] with ω hc hz hf
  obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp hf
  have hu : intervalTouchClock B x r ω = t := by rw [intervalTouchClock, ← ht]; rfl
  simpa only [intervalTouchEndpoint, hu] using intervalTouchTime_terminal hc hz hr hx ht.symm

/-- Removing the deterministic cutoff preserves the genuine exponential stopping identity. -/
theorem integral_actualBrownianExponentialWith_intervalTouch (hB : IsBrownianReal B μ)
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) (c : ℝ) :
    Integrable (fun ω => actualBrownianExponentialWith B c (intervalTouchClock B x r ω) ω) μ ∧
      (∫ ω, actualBrownianExponentialWith B c (intervalTouchClock B x r ω) ω ∂μ) = 1 := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  let F : ℕ → Ω → ℝ := fun H ω => actualBrownianExponentialWith B c (boundedIntervalExit B x r H ω) ω
  let f : Ω → ℝ := fun ω => actualBrownianExponentialWith B c (intervalTouchClock B x r ω) ω
  have hF (H : ℕ) : Integrable (F H) μ ∧ (∫ ω, F H ω ∂μ) = 1 :=
    integral_actualBrownianExponentialWith_boundedIntervalExit hB c x r H
  have ht : ∀ᵐ ω ∂μ, Tendsto (fun H => F H ω) atTop (𝓝 (f ω)) := by
    filter_upwards [boundedIntervalExit_eventually_eq_touch hB hr hx] with ω hω
    apply tendsto_const_nhds.congr'
    exact hω.mono (fun H hH => by dsimp only [F,f]; rw [hH])
  have hb (H : ℕ) : ∀ᵐ ω ∂μ, ‖F H ω‖ ≤ Real.exp (|c| *(r+|x|)) := by
    filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero] with ω hc hz
    have h0 : x+B 0 ω ∈ Icc (-0) r := by simpa only [hz,add_zero,neg_zero] using Ioo_subset_Icc_self hx
    have hs := boundedOpenExitTime_mem_strip (X := fun t ω => x+B t ω) (a := r) (b := 0)
      (T := (H : ℝ≥0)) (hc.const_add x) h0
    change x+B (boundedIntervalExit B x r H ω) ω ∈ Icc (-0) r at hs
    have hX : |B (boundedIntervalExit B x r H ω) ω| ≤ r+|x| := by
      have he : B (boundedIntervalExit B x r H ω) ω =
          (x+B (boundedIntervalExit B x r H ω) ω)-x := by ring
      rw [he]
      calc
        _ ≤ |x+B (boundedIntervalExit B x r H ω) ω|+|x| := abs_sub _ _
        _ ≤ _ := by rw [abs_of_nonneg (by simpa only [neg_zero] using hs.1)]; linarith [hs.2]
    dsimp only [F,actualBrownianExponentialWith]
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ c*B (boundedIntervalExit B x r H ω) ω := sub_le_self _ (by positivity)
      _ ≤ |c*B (boundedIntervalExit B x r H ω) ω| := le_abs_self _
      _ = |c| *|B (boundedIntervalExit B x r H ω) ω| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hX (abs_nonneg _)
  have hm : AEStronglyMeasurable f μ := aestronglyMeasurable_of_tendsto_ae atTop
    (fun H => (hF H).1.aestronglyMeasurable) ht
  have hfb : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ Real.exp (|c| *(r+|x|)) := by
    filter_upwards [ht, ae_all_iff.mpr hb] with ω ht hb
    exact le_of_tendsto ht.norm (Eventually.of_forall hb)
  refine ⟨(integrable_const _).mono' hm hfb, ?_⟩
  have hi := tendsto_integral_of_dominated_convergence (fun _ : Ω => Real.exp (|c| *(r+|x|)))
    (fun H => (hF H).1.aestronglyMeasurable) (integrable_const _) hb ht
  have he : (fun H : ℕ => ∫ ω, F H ω ∂μ) = fun _ => (1 : ℝ) := funext (fun H => (hF H).2)
  rw [he] at hi
  exact tendsto_nhds_unique hi tendsto_const_nhds

end BrownianAffine
