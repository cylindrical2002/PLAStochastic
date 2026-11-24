import PLAStochastic.Affine.Extrema.Density.ReflectedDensity
import PLAStochastic.Affine.Extrema.Density.ReflectedKernels
import PLAStochastic.Affine.Extrema.Density.ReflectionVolume

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

theorem measurableEmbedding_extremaReflection : MeasurableEmbedding extremaReflection :=
  continuous_extremaReflection.measurableEmbedding extremaReflection_involutive.injective

theorem map_orderedExtremaDensityMeasure_reflection :
    orderedExtremaDensityMeasure.map extremaReflection=reverseOrderedExtremaDensityMeasure := by
  have hρ : MeasurePreserving extremaReflection volume volume := measurePreserving_extrema_reflection
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply continuous_extremaReflection.measurable hS,
    orderedExtremaDensityMeasure,Measure.restrict_apply (continuous_extremaReflection.measurable hS),
    withDensity_apply _ ((continuous_extremaReflection.measurable hS).inter measurableSet_orderedExtremaDomain),
    reverseOrderedExtremaDensityMeasure,Measure.restrict_apply hS,
    withDensity_apply _ (hS.inter measurableSet_reverseOrderedExtremaDomain)]
  rw [←hρ.setLIntegral_comp_preimage_emb measurableEmbedding_extremaReflection
    (fun p => ENNReal.ofReal (orderedExtremaDensity p)) (extremaReflection ⁻¹' S ∩ orderedExtremaDomain)]
  have hset : extremaReflection ⁻¹' (extremaReflection ⁻¹' S ∩ orderedExtremaDomain)=
      S ∩ reverseOrderedExtremaDomain := by
    rw [preimage_inter,←preimage_comp,show extremaReflection ∘ extremaReflection=id from
      funext extremaReflection_involutive,preimage_id,extremaReflection_preimage_ordered]
  rw [hset]
  apply setLIntegral_congr_fun (hS.inter measurableSet_reverseOrderedExtremaDomain)
  intro p hp
  exact congrArg ENNReal.ofReal (orderedExtremaDensity_reflection hp.2)

theorem reverseOrderedExtremaDensity_pos {p : ExtremaVector}
    (hp : p ∈ reverseOrderedExtremaDomain) : 0 < reverseOrderedExtremaDensity p := by
  rw [←orderedExtremaDensity_reflection hp]
  apply orderedExtremaDensity_pos
  change p ∈ extremaReflection ⁻¹' orderedExtremaDomain
  rwa [extremaReflection_preimage_ordered]

theorem reverseOrderedExtremaDensityMeasure_apply {S : Set ExtremaVector} (hS : MeasurableSet S) :
    reverseOrderedExtremaDensityMeasure S=
      ∫⁻ p in S ∩ reverseOrderedExtremaDomain, ENNReal.ofReal (reverseOrderedExtremaDensity p) := by
  rw [reverseOrderedExtremaDensityMeasure,Measure.restrict_apply hS,
    withDensity_apply _ (hS.inter measurableSet_reverseOrderedExtremaDomain)]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The reverse time order has the boundary labels exchanged, for the actual Brownian vector. -/
theorem brownianReverseExtremaMeasure_eq_density (hB : IsBrownianReal B μ) :
    (brownianExtremaMeasure B μ).restrict reverseOrderedExtremaDomain=reverseOrderedExtremaDensityMeasure := by
  rw [brownianReverseExtremaMeasure_eq_reflected_density hB,map_orderedExtremaDensityMeasure_reflection]

/-- The entire actual extrema distribution is exhausted by the two explicit interior densities. -/
theorem brownianExtremaMeasure_eq_densities (hB : IsBrownianReal B μ) :
    brownianExtremaMeasure B μ=orderedExtremaDensityMeasure+reverseOrderedExtremaDensityMeasure := by
  rw [brownianExtremaMeasure_eq_density_and_reflection hB,map_orderedExtremaDensityMeasure_reflection]

/-- Every Borel observation obeys the full five-variable density formula, including both time orders. -/
theorem brownianExtremaMeasure_apply_eq_densities (hB : IsBrownianReal B μ)
    {S : Set ExtremaVector} (hS : MeasurableSet S) :
    brownianExtremaMeasure B μ S=
      (∫⁻ p in S ∩ orderedExtremaDomain, ENNReal.ofReal (orderedExtremaDensity p))+
      ∫⁻ p in S ∩ reverseOrderedExtremaDomain, ENNReal.ofReal (reverseOrderedExtremaDensity p) := by
  rw [brownianExtremaMeasure_eq_densities hB,Measure.add_apply,
    reverseOrderedExtremaDensityMeasure_apply hS,orderedExtremaDensityMeasure,
    Measure.restrict_apply hS,withDensity_apply _ (hS.inter measurableSet_orderedExtremaDomain)]

/-- There is no boundary or equal-time component left outside the two strict domains. -/
theorem brownianExtremaMeasure_no_boundary_component (hB : IsBrownianReal B μ) :
    brownianExtremaMeasure B μ (orderedExtremaDomain ∪ reverseOrderedExtremaDomain)ᶜ=0 := by
  rw [brownianExtremaMeasure_apply_eq_densities hB
    (measurableSet_orderedExtremaDomain.union measurableSet_reverseOrderedExtremaDomain).compl]
  rw [show (orderedExtremaDomain ∪ reverseOrderedExtremaDomain)ᶜ ∩ orderedExtremaDomain=∅ by
    exact disjoint_compl_left.mono_right subset_union_left |>.inter_eq,
    show (orderedExtremaDomain ∪ reverseOrderedExtremaDomain)ᶜ ∩ reverseOrderedExtremaDomain=∅ by
    exact disjoint_compl_left.mono_right subset_union_right |>.inter_eq]
  simp

theorem brownianExtremaDensity_integrals_eq_one (hB : IsBrownianReal B μ) :
    (∫⁻ p in orderedExtremaDomain, ENNReal.ofReal (orderedExtremaDensity p))+
      ∫⁻ p in reverseOrderedExtremaDomain, ENNReal.ofReal (reverseOrderedExtremaDensity p)=1 := by
  simpa only [univ_inter] using
    (brownianExtremaMeasure_apply_eq_densities hB MeasurableSet.univ).symm.trans
      (brownianExtremaMeasure_univ hB)

theorem orderedExtremaDensityMeasure_mass_half (hB : IsBrownianReal B μ) :
    orderedExtremaDensityMeasure univ=(1:ℝ≥0∞)/2 := by
  have h := orderedExtremaDensity_and_reflection_mass_one hB
  rw [Measure.add_apply,Measure.map_apply continuous_extremaReflection.measurable MeasurableSet.univ,
    preimage_univ] at h
  apply (ENNReal.eq_div_iff (by norm_num) (by norm_num)).mpr
  simpa only [two_mul] using h

theorem reverseOrderedExtremaDensityMeasure_mass_half (hB : IsBrownianReal B μ) :
    reverseOrderedExtremaDensityMeasure univ=(1:ℝ≥0∞)/2 := by
  rw [←map_orderedExtremaDensityMeasure_reflection,
    Measure.map_apply continuous_extremaReflection.measurable MeasurableSet.univ,preimage_univ,
    orderedExtremaDensityMeasure_mass_half hB]

end BrownianAffine
