import PLAStochastic.Affine.Process.Killed.Boundary.CrossMoment

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem hasDerivAt_crossBoundaryTransform_spectral (hB : IsBrownianReal B μ)
    {r k : ℝ} (hr : 0 < r) (hk : 0 < k) :
    HasDerivAt (fun k => crossBoundaryTransform r (k^2/2))
      (-k*boundaryPairTransform r k) k := by
  have hd := (hasDerivAt_crossBoundaryTransform hB hr (by positivity : 0 < k^2/2)).2
  rw [integral_laplace_heatCrossBoundary_moment hB hr hk] at hd
  convert! hd.comp k (((hasDerivAt_id k).pow 2).div_const 2) using 1
  simp only [id_eq]
  ring

theorem crossBoundaryTransform_nonneg (hB : IsBrownianReal B μ)
    {r lam : ℝ} (hr : 0 < r) : 0 ≤ crossBoundaryTransform r lam := by
  apply setIntegral_nonneg measurableSet_Ioi
  intro t ht
  exact mul_nonneg (Real.exp_nonneg _) (heatCrossBoundary_nonneg hB hr (T := ⟨t,ht.le⟩) ht)

theorem tendsto_crossBoundaryTransform_spectral (hB : IsBrownianReal B μ)
    {r : ℝ} (hr : 0 < r) :
    Tendsto (fun k => crossBoundaryTransform r (k^2/2)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (tendsto_crossBoundaryGreen_atTop hr)
  · exact Eventually.of_forall (fun _ => crossBoundaryTransform_nonneg hB hr)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with k hk
    exact (laplace_heatCrossBoundary_integrable_bound hB hr hk).2

/-- The actual cross-boundary Laplace integral is fixed by its proved derivative and
its proved limit at infinity; no boundary-transform identity is assumed. -/
theorem crossBoundaryTransform_eq_green (hB : IsBrownianReal B μ)
    {r k : ℝ} (hr : 0 < r) (hk : 0 < k) :
    crossBoundaryTransform r (k^2/2) = crossBoundaryGreen r k := by
  let F : ℝ → ℝ := fun u => crossBoundaryTransform r (u^2/2)-crossBoundaryGreen r u
  have hd (u : ℝ) (hu : u ∈ Ioi (0 : ℝ)) : HasDerivAt F 0 u := by
    convert! (hasDerivAt_crossBoundaryTransform_spectral hB hr hu).sub
      (hasDerivAt_crossBoundaryGreen hr hu) using 1
    ring
  have hc (u : ℝ) (hu : 0 < u) : F u = F k :=
    isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi (0 : ℝ)).isPreconnected
      (fun u hu => (hd u hu).differentiableAt.differentiableWithinAt)
      (fun u hu => (hd u hu).deriv) hu hk
  have ht : Tendsto F atTop (𝓝 0) := by
    simpa only [sub_zero, zero_sub] using
      (tendsto_crossBoundaryTransform_spectral hB hr).sub (tendsto_crossBoundaryGreen_atTop hr)
  have ht' : Tendsto F atTop (𝓝 (F k)) := tendsto_const_nhds.congr' (by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    exact (hc u hu).symm)
  have hz : F k = 0 := tendsto_nhds_unique ht' ht
  exact sub_eq_zero.mp hz

theorem integral_laplace_heatCrossBoundary (hB : IsBrownianReal B μ)
    {r k : ℝ} (hr : 0 < r) (hk : 0 < k) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-(k^2/2)*t)*heatCrossBoundary r t) =
      2*k/Real.sinh (k*r) := crossBoundaryTransform_eq_green hB hr hk

end BrownianAffine
