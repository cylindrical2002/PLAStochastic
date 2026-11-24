import PLAStochastic.Affine.Lifetime.BrownianProcess
import PLAStochastic.Affine.Lifetime.GaussianBlocks

/-!
# Geometric closed tails of the actual Brownian lifetimes

The lifetime events are reduced to the proved approximation-error events.
The Gaussian probability on the right comes from independent Brownian increments.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace BrownianAffine

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem anchoredProcessLifetime_probability_le (hB : IsBrownianReal B μ) (n : ℕ) :
    μ {ω | (16 : ℝ≥0∞) * n ≤ anchoredProcessLifetime B 1 ω} ≤ gaussianBlockPass ^ n := by
  have heq : μ {ω | (16 : ℝ≥0∞) * n ≤ anchoredProcessLifetime B 1 ω} =
      μ {ω | anchoredProcessError B (16 * n) ω ≤ 1} := by
    apply measure_congr
    filter_upwards [anchoredProcessLifetime_closed_tails hB (by norm_num : (0 : ℝ) ≤ 1)]
      with ω hω
    apply propext
    simpa only [ENNReal.coe_mul, ENNReal.coe_natCast, ENNReal.coe_ofNat] using! hω (16 * n)
  rw [heq]
  exact anchoredProcessError_probability_le hB n

theorem optimalProcessLifetime_probability_le (hB : IsBrownianReal B μ) (n : ℕ) :
    μ {ω | (16 : ℝ≥0∞) * n ≤ optimalProcessLifetime B 1 ω} ≤ gaussianBlockPass ^ n := by
  have heq : {ω | (16 : ℝ≥0∞) * n ≤ optimalProcessLifetime B 1 ω} =
      {ω | optimalProcessError B (16 * n) ω ≤ 1} := by
    ext ω
    simpa only [ENNReal.coe_mul, ENNReal.coe_natCast, ENNReal.coe_ofNat] using!
      optimalProcessLifetime_closed_tails B (by norm_num : (0 : ℝ) ≤ 1) ω (16 * n)
  rw [heq]
  exact optimalProcessError_probability_le hB n

end BrownianAffine
