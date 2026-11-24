import PLAStochastic.Affine.Extrema.OrderedVector

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- Approximate minimizing values localize their observation times at the unique minimum. -/
theorem tendsto_lowerTime_of_residual_values (g : Path 1) {a : ℝ}
    (hg : DifferentiableAt ℝ (slopeLower g) a) {u : ℕ → RangeTime}
    (hu : Tendsto (fun n => slopeResidual g a (u n)) atTop (𝓝 (slopeLower g a))) :
    Tendsto u atTop (𝓝 (lowerTime g a)) := by
  apply tendsto_nhds_of_unique_mapClusterPt
  intro t ht
  obtain ⟨φ,hφ,hφtop⟩ := ht.exists_seq_tendsto
  have hcont := (continuous_slopeResidual g a).continuousAt.tendsto.comp hφ
  have hval := hu.comp hφtop
  apply lowerTime_unique_of_differentiable g hg
  exact tendsto_nhds_unique hcont hval

/-- The same compactness argument localizes observation times approaching the maximum. -/
theorem tendsto_upperTime_of_residual_values (g : Path 1) {a : ℝ}
    (hg : DifferentiableAt ℝ (slopeUpper g) a) {u : ℕ → RangeTime}
    (hu : Tendsto (fun n => slopeResidual g a (u n)) atTop (𝓝 (slopeUpper g a))) :
    Tendsto u atTop (𝓝 (upperTime g a)) := by
  apply tendsto_nhds_of_unique_mapClusterPt
  intro t ht
  obtain ⟨φ,hφ,hφtop⟩ := ht.exists_seq_tendsto
  have hcont := (continuous_slopeResidual g a).continuousAt.tendsto.comp hφ
  have hval := hu.comp hφtop
  apply upperTime_unique_of_differentiable g hg
  exact tendsto_nhds_unique hcont hval

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- On one full-measure set, every sequence of near-extremal observations of the
actual Brownian path localizes at its corresponding unique extremum time. -/
theorem brownian_extrema_time_localization_ae (hB : IsBrownianReal B μ) (a : ℝ) :
    ∀ᵐ ω ∂μ,
      (∀ u : ℕ → RangeTime,
        Tendsto (fun n => slopeResidual (unitPath (processPath B ω) 1) a (u n)) atTop
          (𝓝 (slopeLower (unitPath (processPath B ω) 1) a)) →
        Tendsto u atTop (𝓝 (lowerTime (unitPath (processPath B ω) 1) a))) ∧
      (∀ u : ℕ → RangeTime,
        Tendsto (fun n => slopeResidual (unitPath (processPath B ω) 1) a (u n)) atTop
          (𝓝 (slopeUpper (unitPath (processPath B ω) 1) a)) →
        Tendsto u atTop (𝓝 (upperTime (unitPath (processPath B ω) 1) a))) := by
  filter_upwards [brownian_upper_lower_differentiable_ae hB a] with ω hω
  exact ⟨fun _ hu => tendsto_lowerTime_of_residual_values _ hω.2 hu,
    fun _ hu => tendsto_upperTime_of_residual_values _ hω.1 hu⟩

end BrownianAffine
