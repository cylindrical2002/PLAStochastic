import PLAStochastic.Affine.Lifetime.BrownianProcess
import PLAStochastic.Affine.Error.BrownianScaling
import PLAStochastic.ForMathlib.Probability.FirstExceedance.ClosedTailLaw

/-!
# Brownian approximation lifetime laws

The actual lifetime has the inverse-square unit-time error law. This follows
from the proved closed-tail characterization and Brownian scaling. Neither
finiteness nor an atomlessness assumption is needed: infinity is retained.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace BrownianAffine

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The anchored lifetime at any positive tolerance has its actual inverse-error law. -/
theorem identDistrib_anchoredLifetime_inverse_error (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 < ε) :
    IdentDistrib (anchoredProcessLifetime B ε)
      (fun ω => (ENNReal.ofReal ε) ^ 2 / (ENNReal.ofReal (anchoredProcessError B 1 ω)) ^ 2)
      μ μ := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hright : AEMeasurable
      (fun ω => (ENNReal.ofReal ε) ^ 2 / (ENNReal.ofReal (anchoredProcessError B 1 ω)) ^ 2) μ :=
    (by fun_prop : Measurable (fun d : ℝ => (ENNReal.ofReal ε) ^ 2 / (ENNReal.ofReal d) ^ 2)).comp_aemeasurable
      (aemeasurable_anchoredProcessError hB 1)
  apply identDistrib_of_nnreal_closed_tails (aemeasurable_anchoredProcessLifetime hB ε) hright
  intro t
  by_cases ht : t = 0
  · simp [ht]
  · calc
      μ {ω | (t : ℝ≥0∞) ≤ anchoredProcessLifetime B ε ω} =
          μ {ω | anchoredProcessError B t ω ≤ ε} := by
        apply measure_congr
        filter_upwards [anchoredProcessLifetime_closed_tails hB hε.le] with ω hω
        exact propext (hω t)
      _ = μ {ω | Real.sqrt (t : ℝ) * anchoredProcessError B 1 ω ≤ ε} :=
        (identDistrib_anchoredProcessError_time hB ht).measure_mem_eq measurableSet_Iic
      _ = μ {ω | (t : ℝ≥0∞) ≤
          (ENNReal.ofReal ε) ^ 2 / (ENNReal.ofReal (anchoredProcessError B 1 ω)) ^ 2} := by
        congr 1
        ext ω
        exact (le_scaled_inverse_square_iff t
          (anchoredTimeError_nonneg (processPath B ω) 1) hε).symm

theorem identDistrib_optimalLifetime_inverse_error (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 < ε) :
    IdentDistrib (optimalProcessLifetime B ε)
      (fun ω => (ENNReal.ofReal ε) ^ 2 / (ENNReal.ofReal (optimalProcessError B 1 ω)) ^ 2)
      μ μ := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hright : AEMeasurable
      (fun ω => (ENNReal.ofReal ε) ^ 2 / (ENNReal.ofReal (optimalProcessError B 1 ω)) ^ 2) μ :=
    (by fun_prop : Measurable (fun d : ℝ => (ENNReal.ofReal ε) ^ 2 / (ENNReal.ofReal d) ^ 2)).comp_aemeasurable
      (aemeasurable_optimalProcessError hB 1)
  apply identDistrib_of_nnreal_closed_tails (aemeasurable_optimalProcessLifetime hB ε) hright
  intro t
  by_cases ht : t = 0
  · simp [ht]
  · calc
      μ {ω | (t : ℝ≥0∞) ≤ optimalProcessLifetime B ε ω} =
          μ {ω | optimalProcessError B t ω ≤ ε} := by
        congr 1
        ext ω
        exact optimalProcessLifetime_closed_tails B hε.le ω t
      _ = μ {ω | Real.sqrt (t : ℝ) * optimalProcessError B 1 ω ≤ ε} :=
        (identDistrib_optimalProcessError_time hB ht).measure_mem_eq measurableSet_Iic
      _ = μ {ω | (t : ℝ≥0∞) ≤
          (ENNReal.ofReal ε) ^ 2 / (ENNReal.ofReal (optimalProcessError B 1 ω)) ^ 2} := by
        congr 1
        ext ω
        exact (le_scaled_inverse_square_iff t
          (optimalTimeError_nonneg (processPath B ω) 1) hε).symm

/-- The unit-tolerance formula in the manuscript, retaining possible infinite values. -/
theorem identDistrib_anchoredLifetime_unit (hB : IsBrownianReal B μ) :
    IdentDistrib (anchoredProcessLifetime B 1)
      (fun ω => ((ENNReal.ofReal (anchoredProcessError B 1 ω)) ^ 2)⁻¹) μ μ := by
  simpa only [ENNReal.ofReal_one, one_pow, one_div] using
    identDistrib_anchoredLifetime_inverse_error hB (ε := 1) zero_lt_one

theorem identDistrib_optimalLifetime_unit (hB : IsBrownianReal B μ) :
    IdentDistrib (optimalProcessLifetime B 1)
      (fun ω => ((ENNReal.ofReal (optimalProcessError B 1 ω)) ^ 2)⁻¹) μ μ := by
  simpa only [ENNReal.ofReal_one, one_pow, one_div] using
    identDistrib_optimalLifetime_inverse_error hB (ε := 1) zero_lt_one

theorem identDistrib_anchoredLifetime_tolerance (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 < ε) :
    IdentDistrib (anchoredProcessLifetime B ε)
      (fun ω => (ENNReal.ofReal ε) ^ 2 * anchoredProcessLifetime B 1 ω) μ μ := by
  have hs := (identDistrib_anchoredLifetime_unit hB).comp
    (by fun_prop : Measurable (fun x : ℝ≥0∞ => (ENNReal.ofReal ε) ^ 2 * x))
  have hi := identDistrib_anchoredLifetime_inverse_error hB hε
  simpa only [div_eq_mul_inv, Function.comp_def] using hi.trans hs.symm

theorem identDistrib_optimalLifetime_tolerance (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 < ε) :
    IdentDistrib (optimalProcessLifetime B ε)
      (fun ω => (ENNReal.ofReal ε) ^ 2 * optimalProcessLifetime B 1 ω) μ μ := by
  have hs := (identDistrib_optimalLifetime_unit hB).comp
    (by fun_prop : Measurable (fun x : ℝ≥0∞ => (ENNReal.ofReal ε) ^ 2 * x))
  have hi := identDistrib_optimalLifetime_inverse_error hB hε
  simpa only [div_eq_mul_inv, Function.comp_def] using hi.trans hs.symm

end

end BrownianAffine
