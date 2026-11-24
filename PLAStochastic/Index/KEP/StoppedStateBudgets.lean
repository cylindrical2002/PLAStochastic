import PLAStochastic.Index.KEP.StoppedStateMoments
import PLAStochastic.ForMathlib.Probability.StoppedSum.PolynomialTailSums
import PLAStochastic.ForMathlib.Probability.Hellinger.ActiveIntegerStateBudget

/-!
# Uniform active-state budgets for the original stopped gap path

Actual geometric tails pay active mass linearly in the block length.
Full-path fourth moments pay active second moments cubically. The paid
absorbing chain therefore has a uniform bound at every deterministic truncation.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset

theorem stopped_prefix_active_budgets (P : Measure (ℕ → ℝ)) [IsProbabilityMeasure P]
    (hpos : ∀ᵐ g ∂P, ∀ i, 0 ≤ g i) (eps : ℝ) (M : ℕ) (hM : 1 ≤ M)
    {q C : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hC : 0 ≤ C)
    (hi2 : ∀ i, Integrable (fun g => gapKeys g i ^ 2) P)
    (hi4 : ∀ i, Integrable (fun g => gapKeys g i ^ 4) P)
    (hm4 : ∀ i, ∫ g, gapKeys g i ^ 4 ∂P ≤ C * (i : ℝ) ^ 4)
    (htail : ∀ k, P.real {g | ((k * M : ℕ) : ℕ∞) < gapSegLen eps g} ≤ q ^ k) :
    (∀ i, Integrable (fun g => gapKeys g i ^ 2) (P.map (kepStoppedPrefix eps i))) ∧
      ∀ N,
        (∑ i ∈ range N, (P.map (kepStoppedPrefix eps i)).real
          {g | (i : ℕ∞) < gapSegLen eps g} ≤ (M : ℝ) / (1 - q)) ∧
        (∑ i ∈ range N, ∫ g, {g | (i : ℕ∞) < gapSegLen eps g}.indicator
          (fun g => gapKeys g i ^ 2) g ∂P.map (kepStoppedPrefix eps i) ≤
            Real.sqrt C * (2 / (1 - Real.sqrt q) ^ 3 * (M : ℝ) ^ 3)) := by
  have hstateI (i : ℕ) : Integrable (fun g => gapKeys g i ^ 2)
      (P.map (kepStoppedPrefix eps i)) := by
    simpa only [id_eq] using
      (stopped_prefix_state_power_budget P (X := id) measurable_id hpos eps i 2
        (hi2 i) le_rfl).1
  have hmass (i : ℕ) : (P.map (kepStoppedPrefix eps i)).real
      {g | (i : ℕ∞) < gapSegLen eps g} =
        P.real {g | (i : ℕ∞) < gapSegLen eps g} := by
    simpa only [id_eq] using stopped_prefix_state_active_mass P (X := id) measurable_id eps i
  have hactive (i : ℕ) :
      ∫ g, {g | (i : ℕ∞) < gapSegLen eps g}.indicator (fun g => gapKeys g i ^ 2) g
        ∂P.map (kepStoppedPrefix eps i) ≤
          Real.sqrt C * ((i : ℝ) ^ 2 * Real.sqrt (P.real {g | (i : ℕ∞) < gapSegLen eps g})) := by
    have h := stopped_prefix_state_active_second_moment P (X := id) measurable_id eps i (hi4 i)
    simp only [id_eq] at h
    have hr : Real.sqrt (∫ g, gapKeys g i ^ 4 ∂P) ≤ Real.sqrt C * (i : ℝ) ^ 2 := by
      have he : C * (i : ℝ) ^ 4 = (Real.sqrt C * (i : ℝ) ^ 2) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hC]
        ring
      have hroot := Real.sqrt_le_sqrt (hm4 i)
      rw [he, Real.sqrt_sq (by positivity)] at hroot
      exact hroot
    have hb := mul_le_mul_of_nonneg_right hr
      (Real.sqrt_nonneg (P.real {g | (i : ℕ∞) < gapSegLen eps g}))
    exact h.trans (by simpa only [mul_assoc] using hb)
  refine ⟨hstateI, fun N => ⟨?_, ?_⟩⟩
  · simp_rw [hmass]
    exact sum_stopping_tail_le_geometric_blocks hM hq0 hq1 htail N
  · obtain ⟨hSummable, hsum⟩ := tsum_sq_mul_sqrt_tail_le hM hq0 hq1 htail
    calc
      _ ≤ ∑ i ∈ range N, Real.sqrt C *
          ((i : ℝ) ^ 2 * Real.sqrt (P.real {g | (i : ℕ∞) < gapSegLen eps g})) :=
        sum_le_sum (fun i _ => hactive i)
      _ = Real.sqrt C * ∑ i ∈ range N,
          (i : ℝ) ^ 2 * Real.sqrt (P.real {g | (i : ℕ∞) < gapSegLen eps g}) := by rw [mul_sum]
      _ ≤ Real.sqrt C * ∑' i : ℕ,
          (i : ℝ) ^ 2 * Real.sqrt (P.real {g | (i : ℕ∞) < gapSegLen eps g}) := by
        gcongr
        exact hSummable.sum_le_tsum (range N) (fun i _ => by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg C)

theorem measureHellinger_absorbing_prefixes_of_path_budgets
    (P Q : Measure (ℕ → ℝ)) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPpos : ∀ᵐ g ∂P, ∀ i, 0 ≤ g i) (hQpos : ∀ᵐ g ∂Q, ∀ i, 0 ≤ g i)
    (eps : ℝ) (M : ℕ) (hM : 1 ≤ M)
    (kappa lam : ℕ → Kernel (ℕ → ℝ) (ℕ → ℝ))
    [∀ i, IsMarkovKernel (kappa i)] [∀ i, IsMarkovKernel (lam i)]
    (hPlaw : ∀ i, kernelIterateLaw kappa (Measure.dirac (fun _ => 0)) i =
      P.map (kepStoppedPrefix eps i))
    (hQlaw : ∀ i, kernelIterateLaw lam (Measure.dirac (fun _ => 0)) i =
      Q.map (kepStoppedPrefix eps i))
    {r b q C : ℝ} (hr : 0 ≤ r) (hb : 0 ≤ b) (hq0 : 0 ≤ q) (hq1 : q < 1) (hC : 0 ≤ C)
    (hPi2 : ∀ i, Integrable (fun g => gapKeys g i ^ 2) P)
    (hQi2 : ∀ i, Integrable (fun g => gapKeys g i ^ 2) Q)
    (hPi4 : ∀ i, Integrable (fun g => gapKeys g i ^ 4) P)
    (hQi4 : ∀ i, Integrable (fun g => gapKeys g i ^ 4) Q)
    (hPm4 : ∀ i, ∫ g, gapKeys g i ^ 4 ∂P ≤ C * (i : ℝ) ^ 4)
    (hQm4 : ∀ i, ∫ g, gapKeys g i ^ 4 ∂Q ≤ C * (i : ℝ) ^ 4)
    (hPtail : ∀ k, P.real {g | ((k * M : ℕ) : ℕ∞) < gapSegLen eps g} ≤ q ^ k)
    (hQtail : ∀ k, Q.real {g | ((k * M : ℕ) : ℕ∞) < gapSegLen eps g} ≤ q ^ k)
    (hstep : ∀ i g, measureHellinger (kappa i g) (lam i g) ≤
      {g | (i : ℕ∞) < gapSegLen eps g}.indicator
        (fun g => r + b * |gapKeys g i| ^ (2 / 3 : ℝ)) g) (N : ℕ) :
    measureHellinger (kernelIterateLaw kappa (Measure.dirac (fun _ => 0)) N)
      (kernelIterateLaw lam (Measure.dirac (fun _ => 0)) N) ^ 2 ≤
        2 * r ^ 2 * ((M : ℝ) / (1 - q)) +
          4 * b ^ 2 * ((M : ℝ) / (1 - q) +
            Real.sqrt C * (2 / (1 - Real.sqrt q) ^ 3 * (M : ℝ) ^ 3)) := by
  have hP := stopped_prefix_active_budgets P hPpos eps M hM hq0 hq1 hC hPi2 hPi4 hPm4 hPtail
  have hQ := stopped_prefix_active_budgets Q hQpos eps M hM hq0 hq1 hC hQi2 hQi4 hQm4 hQtail
  apply measureHellinger_kernelIterate_active_integer_state_budget
    (Measure.dirac (fun _ : ℕ => (0 : ℝ))) kappa lam
    (fun i => {g | (i : ℕ∞) < gapSegLen eps g})
    (fun i => (isStoppingRule_gapSegLen eps).measurableSet_lt i)
    (fun i g => gapKeys g i) hr hb (by norm_num : 0 ≤ (2 / 3 : ℝ)) (by norm_num)
    (fun i => by rw [hPlaw]; exact hP.1 i)
    (fun i => by rw [hQlaw]; exact hQ.1 i) hstep N
  · simpa only [hPlaw] using (hP.2 N).1
  · simpa only [hQlaw] using (hQ.2 N).1
  · simpa only [hPlaw] using (hP.2 N).2
  · simpa only [hQlaw] using (hQ.2 N).2

end

end PGM
