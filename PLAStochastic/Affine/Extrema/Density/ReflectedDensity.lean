import PLAStochastic.Affine.Extrema.Density.OrderedDensity
import PLAStochastic.Affine.Extrema.Density.Reflection

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

theorem map_extremaReflection_involutive (ν : Measure ExtremaVector) :
    (ν.map extremaReflection).map extremaReflection=ν := by
  rw [Measure.map_map continuous_extremaReflection.measurable continuous_extremaReflection.measurable,
    show extremaReflection ∘ extremaReflection=id from funext extremaReflection_involutive,
    Measure.map_id]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem brownianExtremaMeasure_neg (hB : IsBrownianReal B μ) :
    brownianExtremaMeasure (-B) μ=(brownianExtremaMeasure B μ).map extremaReflection := by
  rw [brownianExtremaMeasure,brownianExtremaMeasure,
    AEMeasurable.map_map_of_aemeasurable continuous_extremaReflection.measurable.aemeasurable
      (aemeasurable_brownianExtremaVector hB)]
  exact Measure.map_congr (brownianExtremaVector_neg_ae hB)

/-- Spatially reflected ordered extrema are the actual reverse-order component. -/
theorem brownianOrderedExtremaMeasure_neg (hB : IsBrownianReal B μ) :
    brownianOrderedExtremaMeasure (-B) μ=
      ((brownianExtremaMeasure B μ).restrict reverseOrderedExtremaDomain).map extremaReflection := by
  rw [brownianOrderedExtremaMeasure,brownianExtremaMeasure_neg hB,
    Measure.restrict_map continuous_extremaReflection.measurable measurableSet_orderedExtremaDomain,
    extremaReflection_preimage_ordered]

/-- The second time order is the reflected actual density measure. -/
theorem brownianReverseExtremaMeasure_eq_reflected_density (hB : IsBrownianReal B μ) :
    (brownianExtremaMeasure B μ).restrict reverseOrderedExtremaDomain =
      orderedExtremaDensityMeasure.map extremaReflection := by
  have h := congrArg (fun ν : Measure ExtremaVector => ν.map extremaReflection)
    (brownianOrderedExtremaMeasure_neg hB)
  rw [brownianOrderedExtremaMeasure_eq_density hB.neg,map_extremaReflection_involutive] at h
  exact h.symm

/-- Both actual time orders exhaust the entire five-variable distribution,
including exclusion of all time endpoints and time-diagonal components. -/
theorem brownianExtremaMeasure_eq_density_and_reflection (hB : IsBrownianReal B μ) :
    brownianExtremaMeasure B μ=orderedExtremaDensityMeasure+
      orderedExtremaDensityMeasure.map extremaReflection := by
  rw [brownianExtremaMeasure_eq_ordered_sum hB,brownianOrderedExtremaMeasure_eq_density hB,
    brownianReverseExtremaMeasure_eq_reflected_density hB]

theorem orderedExtremaDensity_and_reflection_mass_one (hB : IsBrownianReal B μ) :
    (orderedExtremaDensityMeasure+orderedExtremaDensityMeasure.map extremaReflection) univ=1 := by
  rw [←brownianExtremaMeasure_eq_density_and_reflection hB,brownianExtremaMeasure_univ hB]

end BrownianAffine
