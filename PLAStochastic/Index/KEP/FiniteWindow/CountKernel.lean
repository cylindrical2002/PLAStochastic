import PLAStochastic.ForMathlib.Probability.Distributions.BinomialPoisson
import PLAStochastic.ForMathlib.Probability.Hellinger.Marginal

/-!
# Finite-window count comparison through a common conditional kernel

The count laws are the actual binomial and Poisson measures. Attaching the same
conditional position density preserves their distance; forgetting the count
contracts it. The statements hold for any jointly measurable conditional family.
They do not yet identify the family with the full endpoint leading tree.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]

theorem kep_window_joint_hellinger_le (n : ℕ) (p : unitInterval)
    (hp : (p : ℝ) ≤ 1 / 2) (k : ℕ → HellingerDensity μ)
    (hk : Measurable (fun z : ℕ × α => (k z.1).density z.2)) :
    ((binomialCountDensity n p).joint k hk).hellinger
      ((poissonCountDensity n p).joint k hk) ≤ (p : ℝ) := by
  rw [HellingerDensity.hellinger_joint_same]
  exact hellinger_binomial_poisson_le_all n p hp

theorem kep_window_common_kernel_hellinger_le (n : ℕ) (p : unitInterval)
    (hp : (p : ℝ) ≤ 1 / 2) (k : ℕ → HellingerDensity μ)
    (hk : Measurable (fun z : ℕ × α => (k z.1).density z.2)) :
    ((binomialCountDensity n p).joint k hk).marginalRight.hellinger
      ((poissonCountDensity n p).joint k hk).marginalRight ≤ (p : ℝ) := by
  exact (HellingerDensity.hellinger_common_kernel_le _ _ k hk).trans
    (hellinger_binomial_poisson_le_all n p hp)

end

end PGM
