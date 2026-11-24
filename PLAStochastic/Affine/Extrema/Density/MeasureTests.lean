import PLAStochastic.Affine.Extrema.Density.CompactTests
import PLAStochastic.Affine.Extrema.Density.DensityMeasure

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- The candidate's interior compact tests are exactly its density integrals. -/
theorem lintegral_orderedExtremaDensityMeasure_compact_test
    {K : Set ExtremaVector} (hK : IsCompact K) (hKi : K ⊆ orderedExtremaDomain)
    {φ : ExtremaVector → ℝ} (hφ : Measurable φ) (hn : ∀ p, 0 ≤ φ p)
    (hsupp : ∀ p, p ∉ K → φ p=0) :
    (∫⁻ p, ENNReal.ofReal (φ p) ∂orderedExtremaDensityMeasure) =
      ∫⁻ p in K, ENNReal.ofReal (φ p*orderedExtremaDensity p) := by
  rw [orderedExtremaDensityMeasure,
    setLIntegral_withDensity_eq_setLIntegral_mul volume
      measurable_orderedExtremaDensity.ennreal_ofReal hφ.ennreal_ofReal
      measurableSet_orderedExtremaDomain,
    ←lintegral_indicator measurableSet_orderedExtremaDomain,
    ←lintegral_indicator hK.measurableSet]
  apply lintegral_congr
  intro p
  by_cases hp : p ∈ K
  · rw [indicator_of_mem hp,indicator_of_mem (hKi hp)]
    simp only [Pi.mul_apply,ENNReal.ofReal_mul (hn _),mul_comm]
  · rw [indicator_of_notMem hp]
    by_cases hU : p ∈ orderedExtremaDomain
    · rw [indicator_of_mem hU]
      simp only [Pi.mul_apply,hsupp p hp,ENNReal.ofReal_zero,mul_zero]
    · rw [indicator_of_notMem hU]

/-- The real Brownian ordered law and its density candidate agree on every
nonnegative continuous compactly supported test inside the physical domain. -/
theorem lintegral_brownianOrderedExtrema_eq_density_compact_test
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B μ) {φ : ExtremaVector → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (hn : ∀ p, 0 ≤ φ p)
    (hs : tsupport φ ⊆ orderedExtremaDomain) :
    (∫⁻ p, ENNReal.ofReal (φ p) ∂brownianOrderedExtremaMeasure B μ) =
      ∫⁻ p, ENNReal.ofReal (φ p) ∂orderedExtremaDensityMeasure := by
  have hz : ∀ p, p ∉ tsupport φ → φ p=0 := fun p hp => image_eq_zero_of_notMem_tsupport hp
  exact (lintegral_brownianOrderedExtrema_compact_test hB hc hs hφ hn hz).trans
    (lintegral_orderedExtremaDensityMeasure_compact_test hc hs hφ.measurable hn hz).symm

end BrownianAffine
