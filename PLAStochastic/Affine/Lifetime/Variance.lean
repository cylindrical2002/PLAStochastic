import PLAStochastic.Affine.Lifetime.Nondegeneracy
import PLAStochastic.Affine.Lifetime.UnitMoments
import Mathlib.Probability.Moments.Variance

/-!
# Positive variance and standardized moments of the actual Brownian lifetimes

The variance here is the variance of the constructed lifetime random variable.
Its strict positivity follows from the proved nondegeneracy and finite second
moment, rather than being a supplied scale parameter.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace BrownianAffine

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem anchoredUnitLifetime_not_ae_constant (hB : IsBrownianReal B μ) (c : ℝ) :
    ¬ anchoredUnitLifetime B =ᵐ[μ] fun _ => c := by
  intro hconst
  apply anchoredProcessLifetime_not_ae_constant hB zero_lt_one (ENNReal.ofReal c)
  filter_upwards [hconst, anchoredProcessLifetime_ae_ne_top hB] with ω hc hf
  calc
    anchoredProcessLifetime B 1 ω = ENNReal.ofReal (anchoredUnitLifetime B ω) :=
      (ENNReal.ofReal_toReal hf).symm
    _ = ENNReal.ofReal c := congrArg ENNReal.ofReal hc

theorem optimalUnitLifetime_not_ae_constant (hB : IsBrownianReal B μ) (c : ℝ) :
    ¬ optimalUnitLifetime B =ᵐ[μ] fun _ => c := by
  intro hconst
  apply optimalProcessLifetime_not_ae_constant hB zero_lt_one (ENNReal.ofReal c)
  filter_upwards [hconst, optimalProcessLifetime_ae_ne_top hB] with ω hc hf
  calc
    optimalProcessLifetime B 1 ω = ENNReal.ofReal (optimalUnitLifetime B ω) :=
      (ENNReal.ofReal_toReal hf).symm
    _ = ENNReal.ofReal c := congrArg ENNReal.ofReal hc

theorem anchoredUnitLifetime_variance_positive (hB : IsBrownianReal B μ) :
    0 < variance (anchoredUnitLifetime B) μ := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  apply lt_of_le_of_ne (variance_nonneg _ _)
  intro hz
  exact anchoredUnitLifetime_not_ae_constant hB _
    (ae_eq_integral_of_variance_eq_zero (anchoredUnitLifetime_memLp hB 2 (by norm_num)) hz.symm)

theorem optimalUnitLifetime_variance_positive (hB : IsBrownianReal B μ) :
    0 < variance (optimalUnitLifetime B) μ := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  apply lt_of_le_of_ne (variance_nonneg _ _)
  intro hz
  exact optimalUnitLifetime_not_ae_constant hB _
    (ae_eq_integral_of_variance_eq_zero (optimalUnitLifetime_memLp hB 2 (by norm_num)) hz.symm)

theorem anchoredUnitLifetime_variance_eq_raw (hB : IsBrownianReal B μ) :
    variance (anchoredUnitLifetime B) μ =
      (∫ ω, anchoredUnitLifetime B ω ^ 2 ∂μ) - (∫ ω, anchoredUnitLifetime B ω ∂μ) ^ 2 := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  exact variance_eq_sub (anchoredUnitLifetime_memLp hB 2 (by norm_num))

theorem optimalUnitLifetime_variance_eq_raw (hB : IsBrownianReal B μ) :
    variance (optimalUnitLifetime B) μ =
      (∫ ω, optimalUnitLifetime B ω ^ 2 ∂μ) - (∫ ω, optimalUnitLifetime B ω ∂μ) ^ 2 := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  exact variance_eq_sub (optimalUnitLifetime_memLp hB 2 (by norm_num))

theorem anchoredUnitLifetime_standardized_absolute_third (hB : IsBrownianReal B μ) :
    let X := anchoredUnitLifetime B
    let κ := ∫ ω, X ω ∂μ
    let V := variance X μ
    (∫ ω, |X ω - κ| ^ 3 ∂μ) / V ^ (3 / 2 : ℝ) =
      ((∫ ω, X ω ^ 3 ∂μ) - 3 * κ * (∫ ω, X ω ^ 2 ∂μ) + 2 * κ ^ 3) / V ^ (3 / 2 : ℝ) +
        2 * (∫ ω, max (κ - X ω) 0 ^ 3 ∂μ) / V ^ (3 / 2 : ℝ) := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  exact standardized_absolute_third_central (anchoredUnitLifetime_memLp hB 3 (by norm_num))
    (anchoredUnitLifetime_variance_positive hB)

theorem optimalUnitLifetime_standardized_absolute_third (hB : IsBrownianReal B μ) :
    let X := optimalUnitLifetime B
    let κ := ∫ ω, X ω ∂μ
    let V := variance X μ
    (∫ ω, |X ω - κ| ^ 3 ∂μ) / V ^ (3 / 2 : ℝ) =
      ((∫ ω, X ω ^ 3 ∂μ) - 3 * κ * (∫ ω, X ω ^ 2 ∂μ) + 2 * κ ^ 3) / V ^ (3 / 2 : ℝ) +
        2 * (∫ ω, max (κ - X ω) 0 ^ 3 ∂μ) / V ^ (3 / 2 : ℝ) := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  exact standardized_absolute_third_central (optimalUnitLifetime_memLp hB 3 (by norm_num))
    (optimalUnitLifetime_variance_positive hB)

theorem anchoredUnitLifetime_standardized_absolute_third_survival (hB : IsBrownianReal B μ) :
    let X := anchoredUnitLifetime B
    let κ := ∫ ω, X ω ∂μ
    let V := variance X μ
    (∫ ω, |X ω - κ| ^ 3 ∂μ) / V ^ (3 / 2 : ℝ) =
      ((∫ ω, X ω ^ 3 ∂μ) - 3 * κ * (∫ ω, X ω ^ 2 ∂μ) + 4 * κ ^ 3 -
        6 * (∫ t in 0..κ, (κ - t) ^ 2 * μ.real {ω | t < X ω})) / V ^ (3 / 2 : ℝ) := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  exact standardized_absolute_third_central_survival
    (anchoredUnitLifetime_memLp hB 3 (by norm_num))
    (Filter.Eventually.of_forall (anchoredUnitLifetime_nonnegative B))
    (anchoredUnitLifetime_variance_positive hB)

theorem optimalUnitLifetime_standardized_absolute_third_survival (hB : IsBrownianReal B μ) :
    let X := optimalUnitLifetime B
    let κ := ∫ ω, X ω ∂μ
    let V := variance X μ
    (∫ ω, |X ω - κ| ^ 3 ∂μ) / V ^ (3 / 2 : ℝ) =
      ((∫ ω, X ω ^ 3 ∂μ) - 3 * κ * (∫ ω, X ω ^ 2 ∂μ) + 4 * κ ^ 3 -
        6 * (∫ t in 0..κ, (κ - t) ^ 2 * μ.real {ω | t < X ω})) / V ^ (3 / 2 : ℝ) := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  exact standardized_absolute_third_central_survival
    (optimalUnitLifetime_memLp hB 3 (by norm_num))
    (Filter.Eventually.of_forall (optimalUnitLifetime_nonnegative B))
    (optimalUnitLifetime_variance_positive hB)

end BrownianAffine
