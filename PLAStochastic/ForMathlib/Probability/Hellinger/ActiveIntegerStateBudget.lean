import PLAStochastic.ForMathlib.Probability.Hellinger.IntegerStateBudget

/-!
# Active-state integer-moment budgets for actual stopped kernel iterations

The conditional error vanishes on absorbed states. The constant perturbation
is paid only by active probabilities; the state perturbation is paid only by
active second moments. Both observed-state laws are retained in the exact chain.
-/

set_option autoImplicit false

namespace ProbabilityTheory

noncomputable section

open MeasureTheory Set Finset

variable {α : Type*} [MeasurableSpace α]

theorem integral_active_integer_budget (mu : Measure α) [IsProbabilityMeasure mu]
    {S : α → ℝ} (hi : Integrable (fun x => S x ^ 2) mu)
    {s : Set α} (hs : MeasurableSet s) (r b : ℝ) :
    Integrable (s.indicator (fun x => 2 * r ^ 2 + 4 * b ^ 2 * (1 + S x ^ 2))) mu ∧
      ∫ x, s.indicator (fun x => 2 * r ^ 2 + 4 * b ^ 2 * (1 + S x ^ 2)) x ∂mu =
        2 * r ^ 2 * mu.real s +
          4 * b ^ 2 * (mu.real s + ∫ x, s.indicator (fun x => S x ^ 2) x ∂mu) := by
  have hunit : Integrable (s.indicator (fun _ : α => (1 : ℝ))) mu :=
    (integrable_const _).indicator hs
  have hstate : Integrable (s.indicator (fun x => S x ^ 2)) mu := hi.indicator hs
  have hsum : Integrable
      (fun x => s.indicator (fun _ : α => (1 : ℝ)) x +
        s.indicator (fun x => S x ^ 2) x) mu := hunit.add hstate
  have he : s.indicator (fun x => 2 * r ^ 2 + 4 * b ^ 2 * (1 + S x ^ 2)) =
      fun x => 2 * r ^ 2 * s.indicator (fun _ : α => (1 : ℝ)) x +
        4 * b ^ 2 * (s.indicator (fun _ : α => (1 : ℝ)) x +
          s.indicator (fun x => S x ^ 2) x) := by
    funext x
    by_cases hx : x ∈ s
    · simp only [indicator_of_mem hx, mul_one]
    · simp only [indicator_of_notMem hx, mul_zero, add_zero]
  refine ⟨he ▸ (hunit.const_mul _).add (hsum.const_mul _), ?_⟩
  rw [he, integral_add
    (f := fun x => 2 * r ^ 2 * s.indicator (fun _ : α => (1 : ℝ)) x)
    (g := fun x => 4 * b ^ 2 * (s.indicator (fun _ : α => (1 : ℝ)) x +
      s.indicator (fun x => S x ^ 2) x)) (hunit.const_mul _) (hsum.const_mul _),
    integral_const_mul (2 * r ^ 2), integral_const_mul (4 * b ^ 2),
    integral_add (f := s.indicator (fun _ : α => (1 : ℝ)))
      (g := s.indicator (fun x => S x ^ 2)) hunit hstate,
    integral_indicator_const 1 hs, smul_eq_mul, mul_one]

theorem measureHellinger_kernelIterate_active_integer_state_budget
    [MeasurableSpace.CountableOrCountablyGenerated α α]
    (P : Measure α) [IsProbabilityMeasure P]
    (kappa lam : ℕ → Kernel α α)
    [∀ i, IsMarkovKernel (kappa i)] [∀ i, IsMarkovKernel (lam i)]
    (s : ℕ → Set α) (hs : ∀ i, MeasurableSet (s i)) (S : ℕ → α → ℝ)
    {r b a A W : ℝ} (hr : 0 ≤ r) (hb : 0 ≤ b) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hiP : ∀ i, Integrable (fun x => S i x ^ 2) (kernelIterateLaw kappa P i))
    (hiQ : ∀ i, Integrable (fun x => S i x ^ 2) (kernelIterateLaw lam P i))
    (hcond : ∀ i x, measureHellinger (kappa i x) (lam i x) ≤
      (s i).indicator (fun x => r + b * |S i x| ^ a) x)
    (N : ℕ)
    (hPA : ∑ i ∈ range N, (kernelIterateLaw kappa P i).real (s i) ≤ A)
    (hQA : ∑ i ∈ range N, (kernelIterateLaw lam P i).real (s i) ≤ A)
    (hPW : ∑ i ∈ range N, ∫ x, (s i).indicator (fun x => S i x ^ 2) x
      ∂kernelIterateLaw kappa P i ≤ W)
    (hQW : ∑ i ∈ range N, ∫ x, (s i).indicator (fun x => S i x ^ 2) x
      ∂kernelIterateLaw lam P i ≤ W) :
    measureHellinger (kernelIterateLaw kappa P N) (kernelIterateLaw lam P N) ^ 2 ≤
      2 * r ^ 2 * A + 4 * b ^ 2 * (A + W) := by
  let B : ℕ → α → ℝ := fun i => (s i).indicator
    (fun x => 2 * r ^ 2 + 4 * b ^ 2 * (1 + S i x ^ 2))
  have hBP (i : ℕ) := integral_active_integer_budget
    (kernelIterateLaw kappa P i) (hiP i) (hs i) r b
  have hBQ (i : ℕ) := integral_active_integer_budget
    (kernelIterateLaw lam P i) (hiQ i) (hs i) r b
  have hBC (i : ℕ) (x : α) :
      measureHellinger (kappa i x) (lam i x) ^ 2 ≤ B i x := by
    by_cases hx : x ∈ s i
    · have hc := hcond i x
      simp only [indicator_of_mem hx] at hc
      simpa only [B, indicator_of_mem hx] using
        sq_le_integer_state_budget (measureHellinger_nonneg _ _) hr hb ha ha1 hc
    · have hc := hcond i x
      simp only [indicator_of_notMem hx] at hc
      have he : measureHellinger (kappa i x) (lam i x) = 0 :=
        le_antisymm hc (measureHellinger_nonneg _ _)
      simp only [B, indicator_of_notMem hx, he, zero_pow two_ne_zero, le_refl]
  have hSP : ∑ i ∈ range N, ∫ x, B i x ∂kernelIterateLaw kappa P i ≤
      2 * r ^ 2 * A + 4 * b ^ 2 * (A + W) := by
    dsimp only [B]
    simp_rw [(hBP _).2]
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_add_distrib]
    gcongr
  have hSQ : ∑ i ∈ range N, ∫ x, B i x ∂kernelIterateLaw lam P i ≤
      2 * r ^ 2 * A + 4 * b ^ 2 * (A + W) := by
    dsimp only [B]
    simp_rw [(hBQ _).2]
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_add_distrib]
    gcongr
  have h := measureHellinger_kernelIterate_sq_le P P kappa lam B
    (fun i => (hBP i).1) (fun i => (hBQ i).1) hBC N
  simp only [measureHellinger_refl, zero_pow two_ne_zero, zero_add, sum_add_distrib] at h
  linarith only [h, hSP, hSQ]

end

end ProbabilityTheory
