import PLAStochastic.Affine.Lifetime.GeometricTail
import PLAStochastic.ForMathlib.MeasureTheory.Integral.GeometricTailIntegrability
import PLAStochastic.ForMathlib.Probability.Moments.AbsoluteThirdCentralSurvival

/-!
# Moments of the actual unit-tolerance Brownian lifetimes

The geometric tail comes from the independent Gaussian blocks, rather than an
integrability hypothesis. Infinity is proved null before real representatives are
used. Both unstandardized absolute-third-moment identities are instantiated at the
actual lifetimes and their actual means. Variance positivity is a separate result.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace BrownianAffine

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

private theorem blockRatio_lt_one : gaussianBlockPass.toReal < 1 := by
  have h := ENNReal.toReal_strict_mono (by simp : (1 : ℝ≥0∞) ≠ ∞)
    gaussianBlockPass_lt_one
  simpa only [ENNReal.toReal_one] using h

/-- The real representative of the actual anchored lifetime at tolerance one. -/
def anchoredUnitLifetime (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ :=
  (anchoredProcessLifetime B 1 ω).toReal

theorem anchoredProcessLifetime_geometricTail (hB : IsBrownianReal B μ) :
    GeometricTail16 μ (anchoredProcessLifetime B 1) gaussianBlockPass.toReal :=
  geometricTail16_of_ennreal gaussianBlockPass_lt_one
    (anchoredProcessLifetime_probability_le hB)

/-- The extended lifetime is finite almost surely; `toReal ∞ = 0` is not used to infer this. -/
theorem anchoredProcessLifetime_ae_ne_top (hB : IsBrownianReal B μ) :
    ∀ᵐ ω ∂μ, anchoredProcessLifetime B 1 ω ≠ ∞ :=
  (anchoredProcessLifetime_geometricTail hB).ae_ne_top ENNReal.toReal_nonneg blockRatio_lt_one

theorem aemeasurable_anchoredUnitLifetime (hB : IsBrownianReal B μ) :
    AEMeasurable (anchoredUnitLifetime B) μ :=
  (aemeasurable_anchoredProcessLifetime hB 1).ennreal_toReal

omit [MeasurableSpace Ω] in
theorem anchoredUnitLifetime_nonnegative (B : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    0 ≤ anchoredUnitLifetime B ω := ENNReal.toReal_nonneg

theorem anchoredUnitLifetime_positive_ae (hB : IsBrownianReal B μ) :
    ∀ᵐ ω ∂μ, 0 < anchoredUnitLifetime B ω := by
  filter_upwards [anchoredProcessLifetime_pos_ae hB (by norm_num : (0 : ℝ) < 1),
    anchoredProcessLifetime_ae_ne_top hB] with ω hp hf
  exact ENNReal.toReal_pos hp.ne' hf

/-- A positive exponential rate, and hence a whole neighborhood of rates, is integrable. -/
theorem anchoredUnitLifetime_exp_neighborhood (hB : IsBrownianReal B μ) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ t : ℝ, |t| ≤ θ →
      Integrable (fun ω => Real.exp (t * anchoredUnitLifetime B ω)) μ :=
  (anchoredProcessLifetime_geometricTail hB).exists_integrable_exp_neighborhood
    (aemeasurable_anchoredProcessLifetime hB 1) ENNReal.toReal_nonneg blockRatio_lt_one

theorem anchoredUnitLifetime_memLp (hB : IsBrownianReal B μ) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (anchoredUnitLifetime B) p μ :=
  (anchoredProcessLifetime_geometricTail hB).memLp_toReal
    (aemeasurable_anchoredProcessLifetime hB 1) ENNReal.toReal_nonneg blockRatio_lt_one p hp

theorem anchoredUnitLifetime_integrable_rpow (hB : IsBrownianReal B μ) {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun ω => anchoredUnitLifetime B ω ^ p) μ :=
  (anchoredProcessLifetime_geometricTail hB).integrable_rpow_toReal
    (aemeasurable_anchoredProcessLifetime hB 1) ENNReal.toReal_nonneg blockRatio_lt_one hp

theorem anchoredUnitLifetime_integrable_pow (hB : IsBrownianReal B μ) (n : ℕ) :
    Integrable (fun ω => anchoredUnitLifetime B ω ^ n) μ :=
  (anchoredProcessLifetime_geometricTail hB).integrable_pow_toReal
    (aemeasurable_anchoredProcessLifetime hB 1) ENNReal.toReal_nonneg blockRatio_lt_one n

theorem anchoredUnitLifetime_integrable (hB : IsBrownianReal B μ) : Integrable (anchoredUnitLifetime B) μ := by
  simpa only [pow_one] using anchoredUnitLifetime_integrable_pow hB 1

theorem anchoredUnitLifetime_mean_nonnegative (B : ℝ≥0 → Ω → ℝ) :
    0 ≤ ∫ ω, anchoredUnitLifetime B ω ∂μ := integral_nonneg (anchoredUnitLifetime_nonnegative B)

/-- Appendix A.1, first formula, for the actual anchored lifetime and its mean. -/
theorem anchoredUnitLifetime_absolute_third_central (hB : IsBrownianReal B μ) :
    (∫ ω, |anchoredUnitLifetime B ω - ∫ z, anchoredUnitLifetime B z ∂μ| ^ 3 ∂μ) =
      (∫ ω, anchoredUnitLifetime B ω ^ 3 ∂μ) -
        3 * (∫ ω, anchoredUnitLifetime B ω ∂μ) * (∫ ω, anchoredUnitLifetime B ω ^ 2 ∂μ) +
        2 * (∫ ω, anchoredUnitLifetime B ω ∂μ) ^ 3 +
        2 * (∫ ω, max ((∫ z, anchoredUnitLifetime B z ∂μ) - anchoredUnitLifetime B ω) 0 ^ 3 ∂μ) := by
  let : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  exact integral_absolute_third_central (anchoredUnitLifetime_memLp hB 3 (by norm_num))

/-- Appendix A.1, survival-integral formula, with no extra lifetime moment assumptions. -/
theorem anchoredUnitLifetime_absolute_third_central_survival (hB : IsBrownianReal B μ) :
    (∫ ω, |anchoredUnitLifetime B ω - ∫ z, anchoredUnitLifetime B z ∂μ| ^ 3 ∂μ) =
      (∫ ω, anchoredUnitLifetime B ω ^ 3 ∂μ) -
        3 * (∫ ω, anchoredUnitLifetime B ω ∂μ) * (∫ ω, anchoredUnitLifetime B ω ^ 2 ∂μ) +
        4 * (∫ ω, anchoredUnitLifetime B ω ∂μ) ^ 3 -
        6 * (∫ t in 0..(∫ z, anchoredUnitLifetime B z ∂μ),
          ((∫ z, anchoredUnitLifetime B z ∂μ) - t) ^ 2 * μ.real {ω | t < anchoredUnitLifetime B ω}) := by
  let : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  exact integral_absolute_third_central_survival (anchoredUnitLifetime_memLp hB 3 (by norm_num))
    (Eventually.of_forall (anchoredUnitLifetime_nonnegative B))

/-- The real representative of the actual optimal lifetime at tolerance one. -/
def optimalUnitLifetime (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ :=
  (optimalProcessLifetime B 1 ω).toReal

theorem optimalProcessLifetime_geometricTail (hB : IsBrownianReal B μ) :
    GeometricTail16 μ (optimalProcessLifetime B 1) gaussianBlockPass.toReal :=
  geometricTail16_of_ennreal gaussianBlockPass_lt_one
    (optimalProcessLifetime_probability_le hB)

/-- The extended lifetime is finite almost surely; `toReal ∞ = 0` is not used to infer this. -/
theorem optimalProcessLifetime_ae_ne_top (hB : IsBrownianReal B μ) :
    ∀ᵐ ω ∂μ, optimalProcessLifetime B 1 ω ≠ ∞ :=
  (optimalProcessLifetime_geometricTail hB).ae_ne_top ENNReal.toReal_nonneg blockRatio_lt_one

theorem aemeasurable_optimalUnitLifetime (hB : IsBrownianReal B μ) :
    AEMeasurable (optimalUnitLifetime B) μ :=
  (aemeasurable_optimalProcessLifetime hB 1).ennreal_toReal

omit [MeasurableSpace Ω] in
theorem optimalUnitLifetime_nonnegative (B : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    0 ≤ optimalUnitLifetime B ω := ENNReal.toReal_nonneg

theorem optimalUnitLifetime_positive_ae (hB : IsBrownianReal B μ) :
    ∀ᵐ ω ∂μ, 0 < optimalUnitLifetime B ω := by
  filter_upwards [optimalProcessLifetime_ae_ne_top hB] with ω hf
  exact ENNReal.toReal_pos (optimalProcessLifetime_pos B (by norm_num : (0 : ℝ) < 1) ω).ne' hf

/-- A positive exponential rate, and hence a whole neighborhood of rates, is integrable. -/
theorem optimalUnitLifetime_exp_neighborhood (hB : IsBrownianReal B μ) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ t : ℝ, |t| ≤ θ →
      Integrable (fun ω => Real.exp (t * optimalUnitLifetime B ω)) μ :=
  (optimalProcessLifetime_geometricTail hB).exists_integrable_exp_neighborhood
    (aemeasurable_optimalProcessLifetime hB 1) ENNReal.toReal_nonneg blockRatio_lt_one

theorem optimalUnitLifetime_memLp (hB : IsBrownianReal B μ) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (optimalUnitLifetime B) p μ :=
  (optimalProcessLifetime_geometricTail hB).memLp_toReal
    (aemeasurable_optimalProcessLifetime hB 1) ENNReal.toReal_nonneg blockRatio_lt_one p hp

theorem optimalUnitLifetime_integrable_rpow (hB : IsBrownianReal B μ) {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun ω => optimalUnitLifetime B ω ^ p) μ :=
  (optimalProcessLifetime_geometricTail hB).integrable_rpow_toReal
    (aemeasurable_optimalProcessLifetime hB 1) ENNReal.toReal_nonneg blockRatio_lt_one hp

theorem optimalUnitLifetime_integrable_pow (hB : IsBrownianReal B μ) (n : ℕ) :
    Integrable (fun ω => optimalUnitLifetime B ω ^ n) μ :=
  (optimalProcessLifetime_geometricTail hB).integrable_pow_toReal
    (aemeasurable_optimalProcessLifetime hB 1) ENNReal.toReal_nonneg blockRatio_lt_one n

theorem optimalUnitLifetime_integrable (hB : IsBrownianReal B μ) : Integrable (optimalUnitLifetime B) μ := by
  simpa only [pow_one] using optimalUnitLifetime_integrable_pow hB 1

theorem optimalUnitLifetime_mean_nonnegative (B : ℝ≥0 → Ω → ℝ) :
    0 ≤ ∫ ω, optimalUnitLifetime B ω ∂μ := integral_nonneg (optimalUnitLifetime_nonnegative B)

/-- Appendix A.1, first formula, for the actual optimal lifetime and its mean. -/
theorem optimalUnitLifetime_absolute_third_central (hB : IsBrownianReal B μ) :
    (∫ ω, |optimalUnitLifetime B ω - ∫ z, optimalUnitLifetime B z ∂μ| ^ 3 ∂μ) =
      (∫ ω, optimalUnitLifetime B ω ^ 3 ∂μ) -
        3 * (∫ ω, optimalUnitLifetime B ω ∂μ) * (∫ ω, optimalUnitLifetime B ω ^ 2 ∂μ) +
        2 * (∫ ω, optimalUnitLifetime B ω ∂μ) ^ 3 +
        2 * (∫ ω, max ((∫ z, optimalUnitLifetime B z ∂μ) - optimalUnitLifetime B ω) 0 ^ 3 ∂μ) := by
  let : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  exact integral_absolute_third_central (optimalUnitLifetime_memLp hB 3 (by norm_num))

/-- Appendix A.1, survival-integral formula, with no extra lifetime moment assumptions. -/
theorem optimalUnitLifetime_absolute_third_central_survival (hB : IsBrownianReal B μ) :
    (∫ ω, |optimalUnitLifetime B ω - ∫ z, optimalUnitLifetime B z ∂μ| ^ 3 ∂μ) =
      (∫ ω, optimalUnitLifetime B ω ^ 3 ∂μ) -
        3 * (∫ ω, optimalUnitLifetime B ω ∂μ) * (∫ ω, optimalUnitLifetime B ω ^ 2 ∂μ) +
        4 * (∫ ω, optimalUnitLifetime B ω ∂μ) ^ 3 -
        6 * (∫ t in 0..(∫ z, optimalUnitLifetime B z ∂μ),
          ((∫ z, optimalUnitLifetime B z ∂μ) - t) ^ 2 * μ.real {ω | t < optimalUnitLifetime B ω}) := by
  let : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  exact integral_absolute_third_central_survival (optimalUnitLifetime_memLp hB 3 (by norm_num))
    (Eventually.of_forall (optimalUnitLifetime_nonnegative B))

end

end BrownianAffine
