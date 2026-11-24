import PLAStochastic.Brownian.Killed.OrderedBoundary.Limit

/-! # Uniform double-boundary convergence on compact interior parameter sets -/
noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- Parameters are ((width, horizon), (first contact time, contact lag), (start, endpoint)). -/
abbrev OrderedHeatParameters := (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ)

/-- The time region where all three heat factors are evaluated at strictly positive times. -/
def orderedHeatInterior : Set OrderedHeatParameters :=
  {p | 0 < p.1.1 ∧ 0 < p.2.1.1 ∧ 0 < p.2.1.2 ∧ p.2.1.1+p.2.1.2 < p.1.2}

theorem continuousOn_orderedContactDensityKernel :
    ContinuousOn (fun p : OrderedHeatParameters =>
      orderedContactDensityKernel p.1.1 p.1.2 p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2)
      orderedHeatInterior := by
  intro p hp
  apply ContinuousAt.continuousWithinAt
  have hi : Tendsto (id : OrderedHeatParameters → OrderedHeatParameters) (𝓝 p) (𝓝 p) := tendsto_id
  exact tendsto_orderedContactDensityKernel hi.fst_nhds.fst_nhds hi.fst_nhds.snd_nhds
    hi.snd_nhds.fst_nhds.fst_nhds hi.snd_nhds.fst_nhds.snd_nhds
    hi.snd_nhds.snd_nhds.fst_nhds hi.snd_nhds.snd_nhds.snd_nhds
    hp.1 hp.2.1 hp.2.2.1 hp.2.2.2

/-- Joint positive boundary shrinkage is uniform on every compact interior parameter set. -/
theorem tendstoUniformlyOn_orderedContactLayerQuotient
    {K : Set OrderedHeatParameters} (hK : IsCompact K) (hKi : K ⊆ orderedHeatInterior) :
    TendstoUniformlyOn (fun e p =>
      orderedContactLayerQuotient p.1.1 e.1 e.2 p.1.2 p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2)
      (fun p => orderedContactDensityKernel p.1.1 p.1.2 p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2)
      ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ))) K := by
  rw [tendstoUniformlyOn_iff_seq_tendstoUniformlyOn]
  intro e he
  apply tendstoUniformlyOn_of_joint_sequence hK (continuousOn_orderedContactDensityKernel.mono hKi)
  intro k hk u _ p hp hu
  obtain ⟨hek, hepos⟩ := tendsto_nhdsWithin_iff.mp (he.comp hk).fst
  obtain ⟨hdk, hdpos⟩ := tendsto_nhdsWithin_iff.mp (he.comp hk).snd
  have hi := hKi hp
  exact tendsto_orderedContactLayerQuotient hu.fst_nhds.fst_nhds hek hdk
    hu.fst_nhds.snd_nhds hu.snd_nhds.fst_nhds.fst_nhds hu.snd_nhds.fst_nhds.snd_nhds
    hu.snd_nhds.snd_nhds.fst_nhds hu.snd_nhds.snd_nhds.snd_nhds
    hi.1 hi.2.1 hi.2.2.1 hi.2.2.2 hepos hdpos

/-- Compact uniform convergence supplies one finite constant for all sufficiently small layers. -/
theorem orderedContactLayerQuotient_eventually_bounded
    {K : Set OrderedHeatParameters} (hK : IsCompact K) (hKi : K ⊆ orderedHeatInterior) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ e : ℝ × ℝ in ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ))),
      ∀ p ∈ K, ‖orderedContactLayerQuotient p.1.1 e.1 e.2 p.1.2 p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2‖ ≤ C := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (continuousOn_orderedContactDensityKernel.mono hKi)
  refine ⟨|M|+1, by positivity, ?_⟩
  have h := (Metric.tendstoUniformlyOn_iff.mp (tendstoUniformlyOn_orderedContactLayerQuotient hK hKi)) 1 zero_lt_one
  filter_upwards [h] with e he p hp
  have hdist := he p hp
  have hbound := hM p hp
  have htri := norm_le_norm_add_norm_sub
    (orderedContactDensityKernel p.1.1 p.1.2 p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2)
    (orderedContactLayerQuotient p.1.1 e.1 e.2 p.1.2 p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2)
  rw [norm_sub_rev] at htri
  rw [dist_comm, dist_eq_norm] at hdist
  linarith [le_abs_self M]

end BrownianAffine
