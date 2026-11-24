import PLAStochastic.Affine.Moments.Optimal.Slope.SurvivalCoarea
import PLAStochastic.Affine.Moments.Optimal.Width.MomentCoordinates
import PLAStochastic.Affine.Lifetime.InverseErrorMoments

/-! # The actual optimal survival law in physical extremum coordinates -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

def optimalExtremaSurvivalWeight (h : ℝ → ℝ≥0∞) (p : ExtremaVector) : ℝ≥0∞ :=
  gaussianEndpointWeight p.2.2.2.2 * ENNReal.ofReal |p.2.2.2.1 - p.2.2.1| * h (p.2.1 - p.1)

theorem measurable_optimalExtremaSurvivalWeight {h : ℝ → ℝ≥0∞} (hh : Measurable h) :
    Measurable (optimalExtremaSurvivalWeight h) := by
  unfold optimalExtremaSurvivalWeight
  exact ((measurable_gaussianEndpointWeight.comp (by fun_prop)).mul
    ((by fun_prop : Measurable (fun p : ExtremaVector => |p.2.2.2.1 - p.2.2.1|)).ennreal_ofReal)).mul
      (hh.comp (by fun_prop))

theorem optimalExtremaSurvivalWeight_reflection (h : ℝ → ℝ≥0∞) (p : ExtremaVector) :
    optimalExtremaSurvivalWeight h (extremaReflection p) = optimalExtremaSurvivalWeight h p := by
  simp only [optimalExtremaSurvivalWeight, extremaReflection, gaussianEndpointWeight,
    neg_sq, abs_sub_comm, neg_sub_neg]

/-- The Jacobian-one coordinate transformation also applies to extended tests. -/
theorem lintegral_orderedExtrema_coordinates {F : ExtremaVector → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ p in orderedExtremaDomain, F p) =
      ∫⁻ p in optimalMomentDomain, F (optimalMomentCoordinates p) := by
  have hh := lintegral_optimalMomentCoordinates (hF.indicator measurableSet_orderedExtremaDomain)
  rw [lintegral_indicator measurableSet_orderedExtremaDomain] at hh
  rw [← optimalMomentCoordinates_preimage_ordered, ← lintegral_indicator
    (measurableSet_orderedExtremaDomain.preimage continuous_optimalMomentCoordinates.measurable)]
  exact hh.symm

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem brownian_slopeCoareaTest_eq_extrema_ae (hB : IsBrownianReal B μ) (h : ℝ → ℝ≥0∞) :
    (fun ω => gaussianEndpointWeight (B 1 ω) * slopeCoareaTest h (unitPath (processPath B ω) 1)) =ᵐ[μ]
      (fun ω => optimalExtremaSurvivalWeight h (brownianExtremaVector B ω)) := by
  filter_upwards [brownian_slopeRange_deriv_eq_extremal_times_ae hB 0] with ω hω
  simp only [optimalExtremaSurvivalWeight, brownianExtremaVector, slopeCoareaTest, hω,
    slopeRange, abs_sub_comm, mul_assoc]

/-- Arbitrary positive tests of the true optimal-range CDF are given by the actual
ordered extremum density, after combining the equally weighted time orders. -/
theorem optimal_range_cdf_test_ordered_density (hB : IsBrownianReal B μ)
    {h : ℝ → ℝ≥0∞} (hh : Measurable h) :
    (∫⁻ r : ℝ, h r * μ {ω | 2 * optimalProcessError B 1 ω < r}) =
      ∫⁻ p in orderedExtremaDomain, ENNReal.ofReal (orderedExtremaDensity p) *
        optimalExtremaSurvivalWeight h p := by
  have he := brownian_coarea_test_lintegral hB hh
  rw [lintegral_congr_ae (brownian_slopeCoareaTest_eq_extrema_ae hB h),
    lintegral_brownianExtremaVector_eq_twice_ordered hB
      (measurable_optimalExtremaSurvivalWeight hh) (optimalExtremaSurvivalWeight_reflection h)] at he
  exact (ENNReal.mul_right_inj (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num)).mp he

theorem optimal_range_cdf_test_physical_density (hB : IsBrownianReal B μ)
    {h : ℝ → ℝ≥0∞} (hh : Measurable h) :
    (∫⁻ r : ℝ, h r * μ {ω | 2 * optimalProcessError B 1 ω < r}) =
      ∫⁻ p in optimalMomentDomain, ENNReal.ofReal (orderedExtremaDensity (optimalMomentCoordinates p)) *
        optimalExtremaSurvivalWeight h (optimalMomentCoordinates p) := by
  rw [optimal_range_cdf_test_ordered_density hB hh]
  exact lintegral_orderedExtrema_coordinates
    (measurable_orderedExtremaDensity.ennreal_ofReal.mul (measurable_optimalExtremaSurvivalWeight hh))

/-- The inverse-range event is the survival event of the genuine Brownian lifetime. -/
theorem measure_optimalUnitLifetime_gt_inverse_width (hB : IsBrownianReal B μ)
    {r : ℝ} (hr : 0 < r) :
    μ {ω | 4 / r ^ 2 < optimalUnitLifetime B ω} =
      μ {ω | 2 * optimalProcessError B 1 ω < r} := by
  have he := (identDistrib_optimalUnitLifetime_inverse_square hB).measure_mem_eq
    (s := Ioi (4 / r ^ 2)) measurableSet_Ioi
  calc
    _ = μ {ω | 4 / r ^ 2 < optimalProcessError B 1 ω ^ (-2 : ℝ)} := he
    _ = _ := by
      apply measure_congr
      filter_upwards [optimalProcessError_unit_positive_ae hB] with ω hω
      apply propext
      change (4 / r ^ 2 < optimalProcessError B 1 ω ^ (-2 : ℝ)) ↔ _
      rw [Real.rpow_neg hω.le, Real.rpow_two, inv_eq_one_div,
        div_lt_div_iff₀ (sq_pos_of_pos hr) (sq_pos_of_pos hω)]
      have hs := sq_lt_sq₀ (show 0 ≤ 2 * optimalProcessError B 1 ω by positivity) hr.le
      convert! hs using 1
      ring_nf

/-- This is the probability on the left side of Proposition A.2, before identifying
the continuous kernel on its right side. -/
theorem measure_optimalUnitLifetime_gt_scaled (hB : IsBrownianReal B μ)
    {T : ℝ} (hT : 0 < T) :
    μ {ω | 4 * T < optimalUnitLifetime B ω} =
      μ {ω | 2 * optimalProcessError B 1 ω < 1 / Real.sqrt T} := by
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hh := measure_optimalUnitLifetime_gt_inverse_width hB (div_pos zero_lt_one hs)
  have he : 4 / (1 / Real.sqrt T) ^ 2 = 4 * T := by
    rw [div_pow, one_pow, div_div_eq_mul_div, div_one, Real.sq_sqrt hT.le]
  rwa [he] at hh

end BrownianAffine
