import PLAStochastic.Affine.Sampled.GeometricTail
import PLAStochastic.ForMathlib.MeasureTheory.Integral.GeometricTailUniformIntegrability
import PLAStochastic.Affine.Lifetime.ToleranceMoments

/-!
# Uniform integrability and mean convergence of actual sampled lifetimes

The common geometric tail is supplied by actual disjoint Brownian grid blocks.
It is not an integrability hypothesis. The limiting expectation is the true
anchored Brownian lifetime expectation; no explicit zeta value is asserted here.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace BrownianAffine

theorem gaussianBlockPassRadius_toReal_lt_one (R : ℝ) :
    (gaussianBlockPassRadius R).toReal < 1 := by
  have h := ENNReal.toReal_strict_mono (by simp : (1 : ℝ≥0∞) ≠ ∞)
    (gaussianBlockPassRadius_lt_one R)
  simpa only [ENNReal.toReal_one] using h

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- Actual small-mesh lifetimes are almost surely finite before real representatives are taken. -/
theorem finiteMeshProcessLifetime_ae_ne_top (hB : IsBrownianReal B μ)
    {h : ℝ≥0} (hh : h ≠ 0) (hh₁ : h ≤ 1) (ε : ℝ) :
    ∀ᵐ ω ∂μ, finiteMeshProcessLifetime B h ε ω ≠ ∞ :=
  (finiteMeshProcessLifetime_geometricTail hB hh hh₁ ε).ae_ne_top
    ENNReal.toReal_nonneg (gaussianBlockPassRadius_toReal_lt_one (2 * ε))

/-- A common proved tail bound makes every family of actual meshes in (0,1] uniformly integrable. -/
theorem finiteMeshProcessLifetime_uniformIntegrable (hB : IsBrownianReal B μ) (ε : ℝ)
    {ι : Type*} {h : ι → ℝ≥0} (hh : ∀ i, h i ≠ 0) (hh₁ : ∀ i, h i ≤ 1) :
    UniformIntegrable (fun i ω => (finiteMeshProcessLifetime B (h i) ε ω).toReal) 1 μ := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  exact uniformIntegrable_toReal_of_geometricTail16
    (fun i => aemeasurable_finiteMeshProcessLifetime hB (h i) (hh i) ε)
    (fun i => finiteMeshProcessLifetime_geometricTail hB (hh i) (hh₁ i) ε)
    ENNReal.toReal_nonneg (gaussianBlockPassRadius_toReal_lt_one (2 * ε))

/-- Actual Brownian sampled lifetimes converge in mean as a positive mesh sequence tends to zero. -/
theorem finiteMeshProcessLifetime_mean_convergence (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 < ε) {h : ℕ → ℝ≥0}
    (hh : ∀ n, h n ≠ 0) (hh₁ : ∀ n, h n ≤ 1)
    (hconv : Tendsto (fun n => (h n : ℝ)) atTop (𝓝 0)) :
    Integrable (fun ω => (anchoredProcessLifetime B ε ω).toReal) μ ∧
      Tendsto (fun n => ∫ ω, (finiteMeshProcessLifetime B (h n) ε ω).toReal ∂μ) atTop
        (𝓝 (∫ ω, (anchoredProcessLifetime B ε ω).toReal ∂μ)) := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  exact tendsto_integral_toReal_of_geometricTail16
    (fun n => aemeasurable_finiteMeshProcessLifetime hB (h n) (hh n) ε)
    (fun n => finiteMeshProcessLifetime_geometricTail hB (hh n) (hh₁ n) ε)
    ENNReal.toReal_nonneg (gaussianBlockPassRadius_toReal_lt_one (2 * ε))
    (anchoredProcessLifetime_tolerance_ae_ne_top hB hε)
    (Eventually.of_forall (finiteMeshProcessLifetime_tendsto ε hh hconv))

end BrownianAffine
