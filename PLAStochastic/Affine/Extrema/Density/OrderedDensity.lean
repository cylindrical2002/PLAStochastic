import PLAStochastic.Affine.Extrema.Density.MeasureTests
import PLAStochastic.Affine.Extrema.Density.OpenCompactTestUniqueness

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- The actual Brownian minimum, maximum, their ordered occurrence times, and
endpoint have the A0-C-Ar/4 joint density. No density identity is assumed. -/
theorem brownianOrderedExtremaMeasure_eq_density {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ) :
    brownianOrderedExtremaMeasure B μ=orderedExtremaDensityMeasure := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have : IsFiniteMeasure (brownianOrderedExtremaMeasure B μ) := by
    unfold brownianOrderedExtremaMeasure brownianExtremaMeasure
    infer_instance
  apply measure_eq_of_open_compact_tests isOpen_orderedExtremaDomain
  · rw [brownianOrderedExtremaMeasure,Measure.restrict_apply measurableSet_orderedExtremaDomain.compl]
    simp only [compl_inter_self,measure_empty]
  · rw [orderedExtremaDensityMeasure,Measure.restrict_apply measurableSet_orderedExtremaDomain.compl]
    simp only [compl_inter_self,measure_empty]
  · exact fun K hK hKi => orderedExtremaDensityMeasure_compact_lt_top hK hKi
  · intro φ hφ hc hs hn
    exact lintegral_brownianOrderedExtrema_eq_density_compact_test hB hφ hc hn hs

/-- Every Borel observation of the actual ordered extrema vector has the density integral. -/
theorem brownianOrderedExtremaMeasure_apply_eq_density {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    {S : Set ExtremaVector} (hS : MeasurableSet S) :
    brownianOrderedExtremaMeasure B μ S =
      ∫⁻ p in S ∩ orderedExtremaDomain, ENNReal.ofReal (orderedExtremaDensity p) := by
  rw [brownianOrderedExtremaMeasure_eq_density hB,orderedExtremaDensityMeasure,
    Measure.restrict_apply hS,withDensity_apply _ (hS.inter measurableSet_orderedExtremaDomain)]

end BrownianAffine
