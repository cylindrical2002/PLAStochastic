import PLAStochastic.ForMathlib.Probability.Hellinger.KernelMeasureBudget
import PLAStochastic.ForMathlib.Probability.Hellinger.Kernel

/-!
# Finite iteration of actual Markov-kernel Hellinger budgets

The kernels may change at every step and the state may contain the whole
observed path. Each conditional budget is integrated under both actual past
laws. The exact sums therefore preserve active-state and physical-state
moment weights, with no independence assumption on stopping decisions.
-/

set_option autoImplicit false

namespace ProbabilityTheory

noncomputable section

open MeasureTheory Finset

variable {α : Type*} [MeasurableSpace α]

def kernelIterateLaw (kappa : ℕ → Kernel α α) (P : Measure α) : ℕ → Measure α
  | 0 => P
  | n + 1 => kappa n ∘ₘ kernelIterateLaw kappa P n

instance isProbabilityMeasure_kernelIterateLaw (kappa : ℕ → Kernel α α)
    (P : Measure α) [IsProbabilityMeasure P] [∀ n, IsMarkovKernel (kappa n)] (n : ℕ) :
    IsProbabilityMeasure (kernelIterateLaw kappa P n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure P)
  | succ n ih =>
    let : IsProbabilityMeasure (kernelIterateLaw kappa P n) := ih
    exact inferInstanceAs (IsProbabilityMeasure (kappa n ∘ₘ kernelIterateLaw kappa P n))

theorem measureHellinger_comp_sq_le_budget
    [MeasurableSpace.CountableOrCountablyGenerated α α]
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (kappa lam : Kernel α α) [IsMarkovKernel kappa] [IsMarkovKernel lam]
    {B : α → ℝ} (hP : Integrable B P) (hQ : Integrable B Q)
    (hcond : ∀ x, measureHellinger (kappa x) (lam x) ^ 2 ≤ B x) :
    measureHellinger (kappa ∘ₘ P) (lam ∘ₘ Q) ^ 2 ≤ measureHellinger P Q ^ 2 +
      ((∫ x, B x ∂P) + ∫ x, B x ∂Q) / 2 := by
  have h := measureHellinger_map (P ⊗ₘ kappa) (Q ⊗ₘ lam) measurable_snd
  have hPmap : (P ⊗ₘ kappa).map Prod.snd = kappa ∘ₘ P := Measure.snd_compProd P kappa
  have hQmap : (Q ⊗ₘ lam).map Prod.snd = lam ∘ₘ Q := Measure.snd_compProd Q lam
  simp only [hPmap, hQmap] at h
  have hs := pow_le_pow_left₀ (measureHellinger_nonneg (kappa ∘ₘ P) (lam ∘ₘ Q)) h 2
  exact hs.trans (measureHellinger_compProd_sq_le_budget P Q kappa lam hP hQ hcond)

theorem measureHellinger_kernelIterate_sq_le
    [MeasurableSpace.CountableOrCountablyGenerated α α]
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (kappa lam : ℕ → Kernel α α)
    [∀ n, IsMarkovKernel (kappa n)] [∀ n, IsMarkovKernel (lam n)]
    (B : ℕ → α → ℝ)
    (hP : ∀ n, Integrable (B n) (kernelIterateLaw kappa P n))
    (hQ : ∀ n, Integrable (B n) (kernelIterateLaw lam Q n))
    (hcond : ∀ n x, measureHellinger (kappa n x) (lam n x) ^ 2 ≤ B n x) (N : ℕ) :
    measureHellinger (kernelIterateLaw kappa P N) (kernelIterateLaw lam Q N) ^ 2 ≤
      measureHellinger P Q ^ 2 +
        (∑ n ∈ range N, ((∫ x, B n x ∂kernelIterateLaw kappa P n) +
          ∫ x, B n x ∂kernelIterateLaw lam Q n)) / 2 := by
  induction N with
  | zero => simp only [kernelIterateLaw, range_zero, sum_empty, zero_div, add_zero, le_refl]
  | succ N ih =>
    have hs := measureHellinger_comp_sq_le_budget
      (kernelIterateLaw kappa P N) (kernelIterateLaw lam Q N)
      (kappa N) (lam N) (hP N) (hQ N) (hcond N)
    change measureHellinger (kappa N ∘ₘ kernelIterateLaw kappa P N)
      (lam N ∘ₘ kernelIterateLaw lam Q N) ^ 2 ≤ _
    rw [sum_range_succ]
    linarith only [hs, ih]

end

end ProbabilityTheory
