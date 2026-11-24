import PLAStochastic.Affine.Extrema.Density.FullDensity
import PLAStochastic.Affine.Extrema.ExtremalTimeMoment

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- The endpoint and extremal-time weight in the genuine Brownian moment identity. -/
def optimalExtremaMomentWeight (q : ℝ) (p : ExtremaVector) : ℝ :=
  Real.exp (p.2.2.2.2 ^ 2 / 2) * |p.2.2.2.1-p.2.2.1| / (p.2.1-p.1) ^ (2*q+1)

theorem measurable_optimalExtremaMomentWeight (q : ℝ) : Measurable (optimalExtremaMomentWeight q) := by
  unfold optimalExtremaMomentWeight
  fun_prop

theorem optimalExtremaMomentWeight_reflection (q : ℝ) (p : ExtremaVector) :
    optimalExtremaMomentWeight q (extremaReflection p)=optimalExtremaMomentWeight q p := by
  simp only [optimalExtremaMomentWeight,extremaReflection,neg_sub_neg,neg_sq,abs_sub_comm]

theorem optimalExtremaMomentWeight_comp {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (q : ℝ) :
    optimalExtremaMomentWeight q ∘ brownianExtremaVector B=brownianExtremaIntegrand q B := by
  funext ω
  simp only [Function.comp_apply,optimalExtremaMomentWeight,brownianExtremaVector,
    brownianExtremaIntegrand,extremaWeight,slopeRange,mul_div_assoc]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- Arbitrary nonnegative Borel observations invariant under spatial reflection
have equal contributions from the two time orders. -/
theorem lintegral_brownianExtremaVector_eq_twice_ordered (hB : IsBrownianReal B μ)
    {φ : ExtremaVector → ℝ≥0∞} (hφ : Measurable φ)
    (hρ : ∀ p, φ (extremaReflection p)=φ p) :
    (∫⁻ ω, φ (brownianExtremaVector B ω) ∂μ)=
      2 * ∫⁻ p in orderedExtremaDomain, ENNReal.ofReal (orderedExtremaDensity p) * φ p := by
  rw [←lintegral_map' hφ.aemeasurable (aemeasurable_brownianExtremaVector hB)]
  change (∫⁻ p, φ p ∂brownianExtremaMeasure B μ)=_
  rw [brownianExtremaMeasure_eq_density_and_reflection hB,lintegral_add_measure,
    measurableEmbedding_extremaReflection.lintegral_map]
  simp only [hρ]
  rw [←two_mul,orderedExtremaDensityMeasure,restrict_withDensity measurableSet_orderedExtremaDomain,
    lintegral_withDensity_eq_lintegral_mul _ measurable_orderedExtremaDensity.ennreal_ofReal hφ]
  rfl

theorem integrable_optimalExtremaMomentWeight (hB : IsBrownianReal B μ)
    {q : ℝ} (hq : 0 < q) : Integrable (optimalExtremaMomentWeight q) (brownianExtremaMeasure B μ) := by
  apply (integrable_map_measure (measurable_optimalExtremaMomentWeight q).aestronglyMeasurable
    (aemeasurable_brownianExtremaVector hB)).mpr
  rw [optimalExtremaMomentWeight_comp]
  exact integrable_brownianExtremaIntegrand hB hq

theorem integral_brownianExtremaIntegrand_eq_twice_ordered (hB : IsBrownianReal B μ)
    {q : ℝ} (hq : 0 < q) :
    (∫ ω, brownianExtremaIntegrand q B ω ∂μ)=
      2 * ∫ p, optimalExtremaMomentWeight q p ∂orderedExtremaDensityMeasure := by
  have hi := integrable_optimalExtremaMomentWeight hB hq
  rw [brownianExtremaMeasure_eq_density_and_reflection hB] at hi
  have hm := integral_map (aemeasurable_brownianExtremaVector hB)
    (measurable_optimalExtremaMomentWeight q).aestronglyMeasurable
  change (∫ p, optimalExtremaMomentWeight q p ∂brownianExtremaMeasure B μ)=
    ∫ ω, optimalExtremaMomentWeight q (brownianExtremaVector B ω) ∂μ at hm
  have heq : (fun ω => optimalExtremaMomentWeight q (brownianExtremaVector B ω))=
      brownianExtremaIntegrand q B := optimalExtremaMomentWeight_comp B q
  rw [heq] at hm
  rw [←hm,brownianExtremaMeasure_eq_density_and_reflection hB,
    integral_add_measure hi.left_of_add_measure hi.right_of_add_measure,
    measurableEmbedding_extremaReflection.integral_map]
  simp only [optimalExtremaMomentWeight_reflection,two_mul]

theorem integral_optimalExtremaMomentWeight_eq_density (q : ℝ) :
    (∫ p, optimalExtremaMomentWeight q p ∂orderedExtremaDensityMeasure)=
      ∫ p in orderedExtremaDomain, orderedExtremaDensity p * optimalExtremaMomentWeight q p := by
  rw [orderedExtremaDensityMeasure,setIntegral_withDensity_eq_setIntegral_toReal_smul
    measurable_orderedExtremaDensity.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
    (optimalExtremaMomentWeight q) measurableSet_orderedExtremaDomain]
  apply setIntegral_congr_fun measurableSet_orderedExtremaDomain
  intro p hp
  simp only [ENNReal.toReal_ofReal (orderedExtremaDensity_pos hp).le,smul_eq_mul]

/-- Every positive real moment of the actual optimal lifetime is the explicit
five-variable boundary-kernel integral, with the two time orders combined. -/
theorem optimalUnitLifetime_moment_ordered_density (hB : IsBrownianReal B μ)
    {q : ℝ} (hq : 0 < q) :
    (∫ ω, optimalUnitLifetime B ω ^ q ∂μ)=
      (2:ℝ) ^ (2*q) * q * Real.sqrt (2*Real.pi) * 2 *
        ∫ p in orderedExtremaDomain, orderedExtremaDensity p * optimalExtremaMomentWeight q p := by
  rw [optimalUnitLifetime_moment_slope_integral hB hq,
    integral_congr_ae (brownian_slopeIntegrand_eq_extremaIntegrand_ae hB q),
    integral_brownianExtremaIntegrand_eq_twice_ordered hB hq,
    integral_optimalExtremaMomentWeight_eq_density]
  ring

end BrownianAffine
