import PLAStochastic.Affine.Extrema.UniqueExtrema

/-!
# The optimal moment formula with actual extremal times

The numerator is the distance between actual attained maximizing and minimizing
times. Their equality almost surely with envelope derivatives transfers both
the proved moment identity and integrability. No global measurability of an
arbitrary tie-breaking choice is assumed.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace BrownianAffine

def extremaWeight (q : ℝ) (g : Path 1) : ℝ :=
  |(upperTime g 0 : ℝ) - (lowerTime g 0 : ℝ)| / slopeRange g 0 ^ (2 * q + 1)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

def brownianExtremaIntegrand (q : ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ :=
  Real.exp (B 1 ω ^ 2 / 2) * extremaWeight q (unitPath (processPath B ω) 1)

theorem brownian_slopeWeight_eq_extremaWeight_ae (hB : IsBrownianReal B μ) (q : ℝ) :
    (fun ω => slopeWeight q (unitPath (processPath B ω) 1)) =ᵐ[μ]
      (fun ω => extremaWeight q (unitPath (processPath B ω) 1)) := by
  filter_upwards [brownian_slopeRange_deriv_eq_extremal_times_ae hB 0] with ω hω
  unfold slopeWeight extremaWeight
  rw [hω, abs_sub_comm]

theorem brownian_slopeIntegrand_eq_extremaIntegrand_ae (hB : IsBrownianReal B μ) (q : ℝ) :
    brownianSlopeIntegrand q B =ᵐ[μ] brownianExtremaIntegrand q B := by
  filter_upwards [brownian_slopeWeight_eq_extremaWeight_ae hB q] with ω hω
  unfold brownianSlopeIntegrand brownianExtremaIntegrand
  rw [hω]

theorem aemeasurable_brownianExtremaIntegrand (hB : IsBrownianReal B μ) (q : ℝ) :
    AEMeasurable (brownianExtremaIntegrand q B) μ :=
  (aemeasurable_brownianSlopeIntegrand hB q).congr
    (brownian_slopeIntegrand_eq_extremaIntegrand_ae hB q)

/-- The exponential/extremal-time integrand is integrable for every positive real moment order. -/
theorem integrable_brownianExtremaIntegrand (hB : IsBrownianReal B μ)
    {q : ℝ} (hq : 0 < q) : Integrable (brownianExtremaIntegrand q B) μ :=
  (integrable_brownianSlopeIntegrand hB hq).congr
    (brownian_slopeIntegrand_eq_extremaIntegrand_ae hB q)

/-- The manuscript's ordinary-Brownian moment identity with actual extremal times. -/
theorem optimalUnitLifetime_moment_extremal_times (hB : IsBrownianReal B μ)
    {q : ℝ} (hq : 0 < q) :
    (∫ ω, optimalUnitLifetime B ω ^ q ∂μ) =
      (2 : ℝ) ^ (2 * q) * q * Real.sqrt (2 * Real.pi) *
        ∫ ω, Real.exp (B 1 ω ^ 2 / 2) *
          |(upperTime (unitPath (processPath B ω) 1) 0 : ℝ) -
            (lowerTime (unitPath (processPath B ω) 1) 0 : ℝ)| /
          slopeRange (unitPath (processPath B ω) 1) 0 ^ (2 * q + 1) ∂μ := by
  rw [optimalUnitLifetime_moment_slope_integral hB hq,
    integral_congr_ae (brownian_slopeIntegrand_eq_extremaIntegrand_ae hB q)]
  simp only [brownianExtremaIntegrand, extremaWeight, mul_div_assoc]

end BrownianAffine
