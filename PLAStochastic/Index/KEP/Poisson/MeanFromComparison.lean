import PLAStochastic.Index.KEP.Poisson.PositiveMoments
import PLAStochastic.ForMathlib.Probability.Hellinger.ExponentialMean

/-!
# The original Poisson child mean near the true reference law

Actual child exponential moments pay the second-moment observable bound.
A sufficiently small Hellinger error then supplies the mean-two budget
needed by the conditional parent cumulant.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory

theorem kepPoisson_mean_le_two_of_comparison {f : ℝ → ℝ}
    {flo fhi L eps n theta B r : ℝ} (hf : KepIntensityProfile f flo fhi L)
    (hn : 0 < n) (htheta : 0 < theta) (j : ℕ) (hm : 0 ≤ kepReferenceSpan eps j)
    (hchild : ∀ x, Integrable (fun z => Real.exp (theta * z)) (kepPoissonLayerMeasure hf eps n x j) ∧
      ∫ z, Real.exp (theta * z) ∂kepPoissonLayerMeasure hf eps n x j ≤ B)
    (hpos : ∀ᵐ z ∂(kepReferenceLaw eps j : Measure ℝ), 0 ≤ z)
    (hi : Integrable (fun z => Real.exp (theta * z)) (kepReferenceLaw eps j : Measure ℝ))
    (hmgf : ∫ z, Real.exp (theta * z) ∂(kepReferenceLaw eps j : Measure ℝ) ≤ B)
    (hmean : ∫ z, z ∂(kepReferenceLaw eps j : Measure ℝ) ≤ 1)
    (herr : ∀ x, measureHellinger (kepPoissonLayerMeasure hf eps n x j) (kepReferenceLaw eps j) ≤ r)
    (hsmall : r * Real.sqrt (8 * B / theta ^ 2) ≤ 1) :
    ∀ x, Integrable (fun z : ℝ => z) (kepPoissonLayerMeasure hf eps n x j) ∧
      ∫ z, z ∂kepPoissonLayerMeasure hf eps n x j ≤ 2 := by
  intro x
  obtain ⟨hX, hb⟩ := measureHellinger_mean_le_of_exponential
    (kepPoissonLayerMeasure hf eps n x j) (kepReferenceLaw eps j : Measure ℝ) htheta
    (kepPoissonLayerMeasure_ae_nonneg hf hn x j hm) hpos (hchild x).1 hi (hchild x).2 hmgf hmean
  refine ⟨hX, ?_⟩
  have h := mul_le_mul_of_nonneg_right (herr x) (Real.sqrt_nonneg (8 * B / theta ^ 2))
  linarith

end

end PGM
