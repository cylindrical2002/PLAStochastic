import PLAStochastic.Affine.Extrema.Density.CombinedDensity

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

theorem reverseOrderedExtremaDensity_indicator_eq :
    reverseOrderedExtremaDomain.indicator reverseOrderedExtremaDensity =
      reverseOrderedExtremaDomain.indicator (orderedExtremaDensity ∘ extremaReflection) := by
  funext p
  by_cases hp : p ∈ reverseOrderedExtremaDomain
  · simp only [indicator_of_mem hp,Function.comp_apply,orderedExtremaDensity_reflection hp]
  · simp only [indicator_of_notMem hp]

theorem measurable_brownianExtremaDensity : Measurable brownianExtremaDensity := by
  unfold brownianExtremaDensity
  rw [show (fun p => orderedExtremaDomain.indicator orderedExtremaDensity p+
      reverseOrderedExtremaDomain.indicator reverseOrderedExtremaDensity p)=
      orderedExtremaDomain.indicator orderedExtremaDensity+
        reverseOrderedExtremaDomain.indicator reverseOrderedExtremaDensity from rfl,
    reverseOrderedExtremaDensity_indicator_eq]
  exact (measurable_orderedExtremaDensity.indicator measurableSet_orderedExtremaDomain).add
    ((measurable_orderedExtremaDensity.comp continuous_extremaReflection.measurable).indicator
      measurableSet_reverseOrderedExtremaDomain)

theorem orderedExtremaDensity_indicator_nonneg (p : ExtremaVector) :
    0 ≤ orderedExtremaDomain.indicator orderedExtremaDensity p := by
  by_cases hp : p ∈ orderedExtremaDomain
  · simpa only [indicator_of_mem hp] using (orderedExtremaDensity_pos hp).le
  · simp only [indicator_of_notMem hp,le_refl]

theorem reverseOrderedExtremaDensity_indicator_nonneg (p : ExtremaVector) :
    0 ≤ reverseOrderedExtremaDomain.indicator reverseOrderedExtremaDensity p := by
  by_cases hp : p ∈ reverseOrderedExtremaDomain
  · simpa only [indicator_of_mem hp] using (reverseOrderedExtremaDensity_pos hp).le
  · simp only [indicator_of_notMem hp,le_refl]

theorem brownianExtremaDensity_nonneg (p : ExtremaVector) : 0 ≤ brownianExtremaDensity p :=
  add_nonneg (orderedExtremaDensity_indicator_nonneg p) (reverseOrderedExtremaDensity_indicator_nonneg p)

theorem withDensity_brownianExtremaDensity :
    volume.withDensity (fun p => ENNReal.ofReal (brownianExtremaDensity p))=
      orderedExtremaDensityMeasure+reverseOrderedExtremaDensityMeasure := by
  have heq : (fun p => ENNReal.ofReal (brownianExtremaDensity p))=
      orderedExtremaDomain.indicator (fun p => ENNReal.ofReal (orderedExtremaDensity p))+
      reverseOrderedExtremaDomain.indicator (fun p => ENNReal.ofReal (reverseOrderedExtremaDensity p)) := by
    funext p
    rw [brownianExtremaDensity,ENNReal.ofReal_add (orderedExtremaDensity_indicator_nonneg p)
      (reverseOrderedExtremaDensity_indicator_nonneg p)]
    simp only [Pi.add_apply]
    congr 1
    · by_cases hp : p ∈ orderedExtremaDomain <;> simp [hp]
    · by_cases hp : p ∈ reverseOrderedExtremaDomain <;> simp [hp]
  rw [heq,withDensity_add_left
    (measurable_orderedExtremaDensity.ennreal_ofReal.indicator measurableSet_orderedExtremaDomain),
    withDensity_indicator measurableSet_orderedExtremaDomain,
    withDensity_indicator measurableSet_reverseOrderedExtremaDomain,
    ←restrict_withDensity measurableSet_orderedExtremaDomain,
    ←restrict_withDensity measurableSet_reverseOrderedExtremaDomain]
  rfl

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- A global Radon--Nikodym representation of the complete actual extrema law. -/
theorem brownianExtremaMeasure_eq_withDensity (hB : IsBrownianReal B μ) :
    brownianExtremaMeasure B μ=volume.withDensity (fun p => ENNReal.ofReal (brownianExtremaDensity p)) := by
  rw [withDensity_brownianExtremaDensity,brownianExtremaMeasure_eq_densities hB]

theorem brownianExtremaMeasure_absolutelyContinuous (hB : IsBrownianReal B μ) :
    brownianExtremaMeasure B μ ≪ volume := by
  rw [brownianExtremaMeasure_eq_withDensity hB]
  exact withDensity_absolutelyContinuous _ _

end BrownianAffine
