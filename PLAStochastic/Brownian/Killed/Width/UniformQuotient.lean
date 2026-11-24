import PLAStochastic.Brownian.Killed.Width.QuotientBounds

/-! # Compact uniform convergence of the two actual moving-width boundary quotients -/
noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- The right flux is jointly continuous in time and position, for positive time. -/
theorem continuousOn_heatBoundaryRight_time_space {r : ℝ} (hr : 0 < r)
    {K : Set (ℝ × ℝ)} (hK : ∀ p ∈ K, 0 < p.1) :
    ContinuousOn (fun p : ℝ × ℝ => heatBoundaryRight r p.1 p.2) K := by
  intro p hp
  apply ContinuousAt.continuousWithinAt
  exact (tendsto_heatSpatialSeries_joint tendsto_const_nhds continuous_fst.continuousAt
    continuous_snd.continuousAt tendsto_const_nhds hr (hK p hp) 0 1).neg

/-- The cross-boundary kernel is continuous for positive time. -/
theorem continuousOn_heatCrossBoundary_time {r : ℝ} (hr : 0 < r)
    {K : Set ℝ} (hK : ∀ t ∈ K, 0 < t) : ContinuousOn (heatCrossBoundary r) K := by
  intro t ht
  apply ContinuousAt.continuousWithinAt
  exact (tendsto_heatSpatialSeries_joint tendsto_const_nhds tendsto_id
    tendsto_const_nhds tendsto_const_nhds hr (hK t ht) 1 1).neg

/-- Increasing the interval width has the actual right flux as compact uniform first variation. -/
theorem tendstoUniformlyOn_dirichletHeatKernel_width_quotient {r : ℝ} (hr : 0 < r)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (htime : ∀ p ∈ K, 0 < p.1) :
    TendstoUniformlyOn (fun e p => dirichletHeatKernel (r+e) p.1 r p.2 / e)
      (fun p => heatBoundaryRight r p.1 p.2) (𝓝[>] (0 : ℝ)) K := by
  rw [tendstoUniformlyOn_iff_seq_tendstoUniformlyOn]
  intro e he
  apply tendstoUniformlyOn_of_joint_sequence hK (continuousOn_heatBoundaryRight_time_space hr htime)
  intro k hk u _ p hp hu
  obtain ⟨hek, hepos⟩ := tendsto_nhdsWithin_iff.mp (he.comp hk)
  have hwidth : Tendsto (fun n => r + e (k n)) atTop (𝓝 r) := by
    simpa only [Function.comp_def, add_zero] using! (tendsto_const_nhds (x := r)).add hek
  have hlt : ∀ᶠ n in atTop, r < r + e (k n) := hepos.mono (fun n hn => by exact lt_add_of_pos_right r hn)
  simpa only [add_sub_cancel_left] using!
    tendsto_dirichletHeatKernel_right_quotient hwidth (continuous_fst.tendsto p |>.comp hu)
      tendsto_const_nhds (continuous_snd.tendsto p |>.comp hu) hr (htime p hp) hlt

/-- The first variation of the opposite boundary flux is the cross-boundary kernel, uniformly. -/
theorem tendstoUniformlyOn_heatBoundaryRight_width_quotient {r : ℝ} (hr : 0 < r)
    {K : Set ℝ} (hK : IsCompact K) (htime : ∀ t ∈ K, 0 < t) :
    TendstoUniformlyOn (fun e t => heatBoundaryRight (r+e) t e / e)
      (heatCrossBoundary r) (𝓝[>] (0 : ℝ)) K := by
  rw [tendstoUniformlyOn_iff_seq_tendstoUniformlyOn]
  intro e he
  apply tendstoUniformlyOn_of_joint_sequence hK (continuousOn_heatCrossBoundary_time hr htime)
  intro k hk u _ t ht hu
  obtain ⟨hek, hepos⟩ := tendsto_nhdsWithin_iff.mp (he.comp hk)
  have hwidth : Tendsto (fun n => r + e (k n)) atTop (𝓝 r) := by
    simpa only [Function.comp_def, add_zero] using! (tendsto_const_nhds (x := r)).add hek
  exact tendsto_heatBoundaryRight_left_quotient hwidth hu hek hr (htime t ht) hepos

end BrownianAffine
