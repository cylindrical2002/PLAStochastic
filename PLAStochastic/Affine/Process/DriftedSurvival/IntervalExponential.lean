import PLAStochastic.Affine.Process.IntervalExit.ExponentialStopping

/-! # Exponential stopping at genuine drifted interval exits -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- Exit from the closed strip [0,r] by the path x+B_t+d*t, capped at T. -/
def boundedDriftedIntervalExit (B : ℝ≥0 → Ω → ℝ) (x d r : ℝ) (T : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  boundedOpenExitTime (fun t ω => x + B t ω + d * (t : ℝ)) (driftBarrierSet r 0) T ω

theorem adapted_affineBrownian (hB : IsPreBrownianReal B μ) (x d : ℝ) :
    Adapted (brownianNaturalFiltration hB)
      (fun t ω => x + measurableBrownian hB t ω + d * (t : ℝ)) := by
  intro t
  exact ((adapted_shiftedBrownian hB x) t).add_const _

theorem gridHittingTime_affineBrownian_ae_eq (hB : IsPreBrownianReal B μ)
    (x d : ℝ) (S : Set ℝ) (δ : ℝ≥0) (N : ℕ) :
    gridHittingTime (fun t ω => x + measurableBrownian hB t ω + d * (t : ℝ)) S δ N =ᵐ[μ]
      gridHittingTime (fun t ω => x + B t ω + d * (t : ℝ)) S δ N := by
  filter_upwards [measurableBrownian_countable_ae_eq hB (fun k : ℕ => δ * k)] with ω hω
  have hp : (fun n : ℕ => x + measurableBrownian hB (δ * n) ω + d * ((δ * n : ℝ≥0) : ℝ)) =
      (fun n : ℕ => x + B (δ * n) ω + d * ((δ * n : ℝ≥0) : ℝ)) := by
    funext n
    rw [hω n]
  have hh := congrArg (fun f : ℕ → ℝ => hittingBtwn (fun n (_ : Unit) => f n) S 0 N ()) hp
  exact congrArg (fun k : ℕ => δ * (k : ℝ≥0)) hh

/-- Every real exponential parameter retains expectation one at this actual
bounded drifted exit, proved through adapted finite-grid stopping limits. -/
theorem integral_actualBrownianExponentialWith_boundedDriftedIntervalExit
    (hB : IsBrownianReal B μ) (c x d r : ℝ) (T : ℝ≥0) :
    Integrable (fun ω => actualBrownianExponentialWith B c
      (boundedDriftedIntervalExit B x d r T ω) ω) μ ∧
      (∫ ω, actualBrownianExponentialWith B c
        (boundedDriftedIntervalExit B x d r T ω) ω ∂μ) = 1 := by
  obtain ⟨H, hH⟩ := exists_nat_ge T
  let G : ℕ → Ω → ℝ≥0 := fun n =>
    gridHittingTime (fun t ω => x + measurableBrownian hB.toIsPreBrownianReal t ω + d * (t : ℝ))
      (driftBarrierSet r 0) (reciprocalMesh n) (H * (n + 1))
  apply integral_actualBrownianExponentialWith_stopping_limit hB c
    (τ := fun n ω => min (G n ω : WithTop ℝ≥0) (T : WithTop ℝ≥0)) (T := T)
  · intro n
    exact (isStoppingTime_gridHittingTime (adapted_affineBrownian hB.toIsPreBrownianReal x d)
      (measurableSet_driftBarrierSet r 0) (reciprocalMesh_pos n) (H * (n + 1))).min_const T
  · exact fun _ _ => min_le_right _ _
  · intro n
    have hc := (gridHittingTime_countable_range
      (fun t ω => x + measurableBrownian hB.toIsPreBrownianReal t ω + d * (t : ℝ))
      (driftBarrierSet r 0) (reciprocalMesh n) (H * (n + 1))).image
      (fun z : WithTop ℝ≥0 => min z T)
    simpa only [← Set.range_comp, Function.comp_def, G] using hc
  · have heq : ∀ᵐ ω ∂μ, ∀ n, G n ω =
        gridHittingTime (fun t ω => x + B t ω + d * (t : ℝ)) (driftBarrierSet r 0)
          (reciprocalMesh n) (H * (n + 1)) ω :=
      ae_all_iff.mpr (fun n => gridHittingTime_affineBrownian_ae_eq hB.toIsPreBrownianReal
        x d (driftBarrierSet r 0) (reciprocalMesh n) (H * (n + 1)))
    filter_upwards [hB.cont, heq] with ω hω heqω
    have ht := gridHittingTime_tendsto_boundedOpenExitTime
      (X := fun t ω => x + B t ω + d * (t : ℝ)) (ω := ω) (S := driftBarrierSet r 0)
      (isOpen_Iio.union isOpen_Ioi) ((hω.const_add x).add (continuous_subtype_val.const_mul d)) H
    have hm := (ht.congr (fun n => (heqω n).symm)).min (tendsto_const_nhds (x := T))
    rw [← boundedOpenExitTime_min hH] at hm
    simpa only [← WithTop.coe_min, WithTop.untopD_coe, boundedDriftedIntervalExit] using hm

omit [MeasurableSpace Ω] in
theorem boundedDriftedIntervalExit_le (x d r : ℝ) (T : ℝ≥0) (ω : Ω) :
    boundedDriftedIntervalExit B x d r T ω ≤ T :=
  boundedOpenExitTime_le _ _ _ _

theorem boundedDriftedIntervalExit_endpoint_mem_ae (hB : IsBrownianReal B μ)
    {x r : ℝ} (hx : x ∈ Icc 0 r) (d : ℝ) (T : ℝ≥0) :
    ∀ᵐ ω ∂μ, x + B (boundedDriftedIntervalExit B x d r T ω) ω +
      d * (boundedDriftedIntervalExit B x d r T ω : ℝ) ∈ Icc 0 r := by
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero] with ω hc hz
  have h0 : x + B 0 ω + d * ((0 : ℝ≥0) : ℝ) ∈ Icc (-0) r := by
    simpa only [hz, add_zero, NNReal.coe_zero, mul_zero, neg_zero] using hx
  simpa only [boundedDriftedIntervalExit, neg_zero] using
    boundedOpenExitTime_mem_strip (X := fun t ω => x + B t ω + d * (t : ℝ))
      (a := r) (b := 0) (T := T) ((hc.const_add x).add (continuous_subtype_val.const_mul d)) h0

end BrownianAffine
