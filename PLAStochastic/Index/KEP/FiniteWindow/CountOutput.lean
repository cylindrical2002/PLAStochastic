import PLAStochastic.Index.KEP.FiniteWindow.CountKernel
import PLAStochastic.ForMathlib.Probability.Hellinger.Kernel

/-!
# Count comparison for arbitrary conditional configurations and outputs

The common conditional law can be any Markov kernel, with no density hypothesis.
Attaching a full configuration and applying one common measurable tree output
therefore pays the count error only once. Identification of the conditional
configuration kernel for the actual remaining samples is still required.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

theorem kep_window_count_measure_hellinger_le (n : ℕ) (p : unitInterval)
    (hp : (p : ℝ) ≤ 1 / 2) :
    measureHellinger (binomial n p) (poissonMeasure (binomialPoissonRate n p)) ≤ (p : ℝ) := by
  have h := measureHellinger_le_density (binomialCountDensity n p) (poissonCountDensity n p)
  change measureHellinger (HellingerDensity.ofNatProbability (binomial n p)).toMeasure
    (HellingerDensity.ofNatProbability (poissonMeasure (binomialPoissonRate n p))).toMeasure ≤ _ at h
  simp only [HellingerDensity.ofNatProbability_toMeasure] at h
  exact h.trans (hellinger_binomial_poisson_le_all n p hp)

theorem kep_window_joint_kernel_hellinger_le (n : ℕ) (p : unitInterval)
    (hp : (p : ℝ) ≤ 1 / 2) (κ : Kernel ℕ α) [IsMarkovKernel κ] :
    measureHellinger (binomial n p ⊗ₘ κ)
      (poissonMeasure (binomialPoissonRate n p) ⊗ₘ κ) ≤ (p : ℝ) := by
  rw [measureHellinger_compProd_eq]
  exact kep_window_count_measure_hellinger_le n p hp

theorem kep_window_kernel_hellinger_le (n : ℕ) (p : unitInterval)
    (hp : (p : ℝ) ≤ 1 / 2) (κ : Kernel ℕ α) [IsMarkovKernel κ] :
    measureHellinger (κ ∘ₘ binomial n p)
      (κ ∘ₘ poissonMeasure (binomialPoissonRate n p)) ≤ (p : ℝ) :=
  (measureHellinger_comp_le _ _ κ).trans (kep_window_count_measure_hellinger_le n p hp)

theorem kep_window_output_hellinger_le (n : ℕ) (p : unitInterval)
    (hp : (p : ℝ) ≤ 1 / 2) (κ : Kernel ℕ α) [IsMarkovKernel κ]
    {F : ℕ × α → β} (hF : Measurable F) :
    let : IsProbabilityMeasure ((binomial n p ⊗ₘ κ).map F) :=
      Measure.isProbabilityMeasure_map hF.aemeasurable
    let : IsProbabilityMeasure ((poissonMeasure (binomialPoissonRate n p) ⊗ₘ κ).map F) :=
      Measure.isProbabilityMeasure_map hF.aemeasurable
    measureHellinger ((binomial n p ⊗ₘ κ).map F)
      ((poissonMeasure (binomialPoissonRate n p) ⊗ₘ κ).map F) ≤ (p : ℝ) :=
  (measureHellinger_compProd_map_le _ _ κ hF).trans
    (kep_window_count_measure_hellinger_le n p hp)

end

end PGM
