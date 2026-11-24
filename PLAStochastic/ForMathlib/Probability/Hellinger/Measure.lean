import PLAStochastic.ForMathlib.Probability.Hellinger.Restriction
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# From a Hellinger density to its actual probability measure

The measure is `withDensity` of the given function. Event masses and expectation
formulas below identify the density-level quantities with this measure.
-/

set_option autoImplicit false

namespace ProbabilityTheory.HellingerDensity

noncomputable section

open MeasureTheory Set
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

def toMeasure (p : HellingerDensity μ) : Measure α :=
  μ.withDensity (fun x => ENNReal.ofReal (p.density x))

instance toMeasure_isProbability (p : HellingerDensity μ) : IsProbabilityMeasure p.toMeasure := by
  constructor
  rw [toMeasure, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal p.integrable (ae_of_all _ p.nonneg),
    p.integral_eq_one]
  norm_num

theorem integral_toMeasure (p : HellingerDensity μ) (φ : α → ℝ) :
    (∫ x, φ x ∂p.toMeasure) = ∫ x, p.density x * φ x ∂μ := by
  rw [toMeasure, integral_withDensity_eq_integral_toReal_smul
    (p.measurable.ennreal_ofReal) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (p.nonneg _), smul_eq_mul]

theorem mass_eq_measureReal (p : HellingerDensity μ) {s : Set α} (hs : MeasurableSet s) :
    p.mass s = p.toMeasure.real s := by
  rw [mass, ← integral_indicator hs]
  have h := integral_toMeasure p (s.indicator fun _ => (1 : ℝ))
  rw [integral_indicator hs, setIntegral_const] at h
  simp only [smul_eq_mul, mul_one] at h
  rw [h]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    by_cases hx : x ∈ s
    · simp [indicator_of_mem hx]
    · simp [indicator_of_notMem hx]

end

end ProbabilityTheory.HellingerDensity
