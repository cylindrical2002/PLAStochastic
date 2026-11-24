import PLAStochastic.Affine.Moments.Optimal.Width.SurvivalExtrema
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-! # Identification of the actual optimal-range CDF almost everywhere

Disintegration of the proved physical extremum density yields the true range
CDF for almost every positive width, without an assumed density hypothesis.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- The positive physical kernel includes its genuine time-space support. -/
def optimalSurvivalPhysicalDensity (p : ExtremaVector) : ℝ≥0∞ :=
  optimalMomentDomain.indicator (fun p =>
    ENNReal.ofReal (orderedExtremaDensity (optimalMomentCoordinates p)) *
      optimalExtremaSurvivalWeight (fun _ => 1) (optimalMomentCoordinates p)) p

def optimalSurvivalWidthKernelENN (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ y : ℝ × ℝ × ℝ × ℝ, optimalSurvivalPhysicalDensity (r, y)

theorem measurable_optimalSurvivalPhysicalDensity : Measurable optimalSurvivalPhysicalDensity :=
  (((measurable_orderedExtremaDensity.comp continuous_optimalMomentCoordinates.measurable).ennreal_ofReal).mul
    ((measurable_optimalExtremaSurvivalWeight measurable_const).comp
      continuous_optimalMomentCoordinates.measurable)).indicator measurableSet_optimalMomentDomain

theorem measurable_optimalSurvivalWidthKernelENN : Measurable optimalSurvivalWidthKernelENN :=
  measurable_optimalSurvivalPhysicalDensity.lintegral_prod_right'

theorem optimalExtremaSurvivalWeight_coordinates (h : ℝ → ℝ≥0∞) (p : ExtremaVector) :
    optimalExtremaSurvivalWeight h (optimalMomentCoordinates p) =
      optimalExtremaSurvivalWeight (fun _ => 1) (optimalMomentCoordinates p) * h p.1 := by
  simp only [optimalExtremaSurvivalWeight, optimalMomentCoordinates, mul_one]
  rw [show p.1 - p.2.1 - -p.2.1 = p.1 by ring]

theorem optimalSurvivalPhysicalDensity_test (h : ℝ → ℝ≥0∞) (p : ExtremaVector) :
    optimalMomentDomain.indicator (fun p => ENNReal.ofReal
      (orderedExtremaDensity (optimalMomentCoordinates p)) *
        optimalExtremaSurvivalWeight h (optimalMomentCoordinates p)) p =
      optimalSurvivalPhysicalDensity p * h p.1 := by
  classical
  by_cases hp : p ∈ optimalMomentDomain
  · simp only [optimalSurvivalPhysicalDensity, indicator_of_mem hp]
    rw [optimalExtremaSurvivalWeight_coordinates h, mul_assoc]
  · simp only [optimalSurvivalPhysicalDensity, indicator_of_notMem hp, zero_mul]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem measurable_optimalRangeCDF (B : ℝ≥0 → Ω → ℝ) (μ : Measure Ω) :
    Measurable (fun r : ℝ => μ {ω | 2 * optimalProcessError B 1 ω < r}) := by
  apply Monotone.measurable
  intro r s hrs
  exact measure_mono (fun _ hω => hω.trans_le hrs)

/-- Every nonnegative Borel test agrees with the width kernel. -/
theorem optimal_range_cdf_test_width (hB : IsBrownianReal B μ)
    {h : ℝ → ℝ≥0∞} (hh : Measurable h) :
    (∫⁻ r : ℝ, h r * μ {ω | 2 * optimalProcessError B 1 ω < r}) =
      ∫⁻ r : ℝ, h r * optimalSurvivalWidthKernelENN r := by
  rw [optimal_range_cdf_test_physical_density hB hh,
    ← lintegral_indicator measurableSet_optimalMomentDomain]
  simp_rw [optimalSurvivalPhysicalDensity_test]
  change (∫⁻ p : ExtremaVector, optimalSurvivalPhysicalDensity p * h p.1 ∂volume.prod volume) = _
  have hm : Measurable (fun p : ExtremaVector => optimalSurvivalPhysicalDensity p * h p.1) :=
    measurable_optimalSurvivalPhysicalDensity.mul (hh.comp measurable_fst)
  rw [lintegral_prod _ hm.aemeasurable]
  apply lintegral_congr
  intro r
  simp_rw [mul_comm (optimalSurvivalPhysicalDensity (r, _)) (h r)]
  exact lintegral_const_mul (h r)
    (measurable_optimalSurvivalPhysicalDensity.comp measurable_prodMk_left)

/-- This almost-everywhere conclusion is obtained from the actual Brownian law.
Continuity is needed separately to promote it to all positive widths. -/
theorem optimal_range_cdf_eq_width_ae (hB : IsBrownianReal B μ) :
    (fun r : ℝ => μ {ω | 2 * optimalProcessError B 1 ω < r}) =ᵐ[volume]
      optimalSurvivalWidthKernelENN := by
  apply ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
    (measurable_optimalRangeCDF B μ) measurable_optimalSurvivalWidthKernelENN
  intro s hs _
  have hh := optimal_range_cdf_test_width hB ((measurable_const (a := (1 : ℝ≥0∞))).indicator hs)
  have h₁ (r : ℝ) : s.indicator (fun _ => (1 : ℝ≥0∞)) r *
      μ {ω | 2 * optimalProcessError B 1 ω < r} =
      s.indicator (fun r => μ {ω | 2 * optimalProcessError B 1 ω < r}) r := by
    by_cases hr : r ∈ s <;> simp [hr]
  have h₂ (r : ℝ) : s.indicator (fun _ => (1 : ℝ≥0∞)) r * optimalSurvivalWidthKernelENN r =
      s.indicator optimalSurvivalWidthKernelENN r := by
    by_cases hr : r ∈ s <;> simp [hr]
  simpa only [h₁, h₂, lintegral_indicator hs] using! hh

end BrownianAffine
