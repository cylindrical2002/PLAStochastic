import PLAStochastic.ForMathlib.Probability.Hellinger.SequenceKernel

/-!
# Integer-moment payment of a sublinear state perturbation

A state power of exponent at most one is paid by its first and second integer
moments. The exact Markov chain budget then gives a cubic finite-horizon cost,
without assuming independence of the conditional increments.
-/

set_option autoImplicit false

namespace ProbabilityTheory

noncomputable section

open MeasureTheory Finset

theorem abs_rpow_le_one_add_abs (s : ℝ) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    |s| ^ a ≤ 1 + |s| := by
  by_cases hs : |s| ≤ 1
  · exact (Real.rpow_le_one (abs_nonneg s) hs ha).trans (le_add_of_nonneg_right (abs_nonneg s))
  · exact (Real.rpow_le_self_of_one_le (le_of_not_ge hs) ha1).trans
      (le_add_of_nonneg_left zero_le_one)

theorem sq_le_integer_state_budget {h r b s a : ℝ}
    (hh : 0 ≤ h) (_hr : 0 ≤ r) (hb : 0 ≤ b) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hbound : h ≤ r + b * |s| ^ a) :
    h ^ 2 ≤ 2 * r ^ 2 + 4 * b ^ 2 * (1 + s ^ 2) := by
  have hlin : h ≤ r + b * (1 + |s|) :=
    hbound.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (abs_rpow_le_one_add_abs s ha ha1) hb))
  have hsq := pow_le_pow_left₀ hh hlin 2
  have hcs : (r + b * (1 + |s|)) ^ 2 ≤ 2 * r ^ 2 + 2 * (b * (1 + |s|)) ^ 2 := by
    nlinarith [sq_nonneg (r - b * (1 + |s|))]
  have hstate : (1 + |s|) ^ 2 ≤ 2 * (1 + s ^ 2) := by
    nlinarith [sq_abs s, sq_nonneg (1 - |s|)]
  have hmul := mul_le_mul_of_nonneg_left hstate (by positivity : 0 ≤ 2 * b ^ 2)
  nlinarith only [hsq, hcs, hmul]

variable {α : Type*} [MeasurableSpace α]

theorem measureHellinger_kernelIterate_integer_state_budget
    [MeasurableSpace.CountableOrCountablyGenerated α α]
    (P : Measure α) [IsProbabilityMeasure P]
    (kappa lam : ℕ → Kernel α α)
    [∀ i, IsMarkovKernel (kappa i)] [∀ i, IsMarkovKernel (lam i)]
    (S : ℕ → α → ℝ) {r b K a : ℝ}
    (hr : 0 ≤ r) (hb : 0 ≤ b) (hK : 0 ≤ K) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hiP : ∀ i, Integrable (fun x => S i x ^ 2) (kernelIterateLaw kappa P i))
    (hiQ : ∀ i, Integrable (fun x => S i x ^ 2) (kernelIterateLaw lam P i))
    (hP : ∀ i, ∫ x, S i x ^ 2 ∂kernelIterateLaw kappa P i ≤ K * (i : ℝ) ^ 2)
    (hQ : ∀ i, ∫ x, S i x ^ 2 ∂kernelIterateLaw lam P i ≤ K * (i : ℝ) ^ 2)
    (hcond : ∀ i x, measureHellinger (kappa i x) (lam i x) ≤ r + b * |S i x| ^ a)
    (N : ℕ) :
    measureHellinger (kernelIterateLaw kappa P N) (kernelIterateLaw lam P N) ^ 2 ≤
      2 * (N : ℝ) * r ^ 2 + 4 * b ^ 2 * ((N : ℝ) + K * (N : ℝ) ^ 3) := by
  let B : ℕ → α → ℝ := fun i x => 2 * r ^ 2 + 4 * b ^ 2 * (1 + S i x ^ 2)
  have hBP (i : ℕ) : Integrable (B i) (kernelIterateLaw kappa P i) :=
    (integrable_const _).add (((integrable_const (1 : ℝ)).add (hiP i)).const_mul _)
  have hBQ (i : ℕ) : Integrable (B i) (kernelIterateLaw lam P i) :=
    (integrable_const _).add (((integrable_const (1 : ℝ)).add (hiQ i)).const_mul _)
  have hBcond (i : ℕ) (x : α) :
      measureHellinger (kappa i x) (lam i x) ^ 2 ≤ B i x :=
    sq_le_integer_state_budget (measureHellinger_nonneg _ _) hr hb ha ha1 (hcond i x)
  have hIP (i : ℕ) : ∫ x, B i x ∂kernelIterateLaw kappa P i ≤
      2 * r ^ 2 + 4 * b ^ 2 * (1 + K * (i : ℝ) ^ 2) := by
    dsimp only [B]
    have hunit : Integrable (fun x => 1 + S i x ^ 2) (kernelIterateLaw kappa P i) :=
      (integrable_const (1 : ℝ)).add (hiP i)
    have hdom : Integrable (fun x => 4 * b ^ 2 * (1 + S i x ^ 2))
        (kernelIterateLaw kappa P i) := hunit.const_mul _
    rw [integral_add (f := fun _ : α => 2 * r ^ 2)
        (g := fun x => 4 * b ^ 2 * (1 + S i x ^ 2)) (integrable_const _) hdom,
      integral_const_mul (4 * b ^ 2) (fun x => 1 + S i x ^ 2),
      integral_add (f := fun _ : α => 1) (g := fun x => S i x ^ 2)
        (integrable_const (1 : ℝ)) (hiP i)]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    gcongr
    exact hP i
  have hIQ (i : ℕ) : ∫ x, B i x ∂kernelIterateLaw lam P i ≤
      2 * r ^ 2 + 4 * b ^ 2 * (1 + K * (i : ℝ) ^ 2) := by
    dsimp only [B]
    have hunit : Integrable (fun x => 1 + S i x ^ 2) (kernelIterateLaw lam P i) :=
      (integrable_const (1 : ℝ)).add (hiQ i)
    have hdom : Integrable (fun x => 4 * b ^ 2 * (1 + S i x ^ 2))
        (kernelIterateLaw lam P i) := hunit.const_mul _
    rw [integral_add (f := fun _ : α => 2 * r ^ 2)
        (g := fun x => 4 * b ^ 2 * (1 + S i x ^ 2)) (integrable_const _) hdom,
      integral_const_mul (4 * b ^ 2) (fun x => 1 + S i x ^ 2),
      integral_add (f := fun _ : α => 1) (g := fun x => S i x ^ 2)
        (integrable_const (1 : ℝ)) (hiQ i)]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    gcongr
    exact hQ i
  have hc := measureHellinger_kernelIterate_sq_le P P kappa lam B hBP hBQ hBcond N
  simp only [measureHellinger_refl, zero_pow two_ne_zero, zero_add] at hc
  calc
    _ ≤ (∑ i ∈ range N, ((∫ x, B i x ∂kernelIterateLaw kappa P i) +
        ∫ x, B i x ∂kernelIterateLaw lam P i)) / 2 := hc
    _ ≤ (∑ _i ∈ range N, 2 * (2 * r ^ 2 + 4 * b ^ 2 * (1 + K * (N : ℝ) ^ 2))) / 2 := by
      gcongr with i hi
      have hin : (i : ℝ) ≤ N := Nat.cast_le.mpr (mem_range.mp hi).le
      have hb' : 2 * r ^ 2 + 4 * b ^ 2 * (1 + K * (i : ℝ) ^ 2) ≤
          2 * r ^ 2 + 4 * b ^ 2 * (1 + K * (N : ℝ) ^ 2) := by gcongr
      linarith only [hIP i, hIQ i, hb']
    _ = _ := by simp only [sum_const, card_range, nsmul_eq_mul]; ring

end

end ProbabilityTheory
