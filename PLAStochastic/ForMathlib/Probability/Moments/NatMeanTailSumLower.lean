import PLAStochastic.ForMathlib.Probability.Process.CappedStopping.Mean

/-! # Partial tail sums bound the mean from below

For a natural-valued random variable the truncation at `n` is the sum of the
first `n` tail indicators, so every finite tail partial sum is at most the mean.
This is the lower-bound companion of the head-plus-weighted-tail estimate. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem min_eq_sum_indicator (K n : ℕ) :
    ((min n K : ℕ) : ℝ) = ∑ j ∈ Finset.range n, (if j < K then (1 : ℝ) else 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ← ih]
      by_cases h : n < K
      · rw [if_pos h]
        have hm : ((min (n+1) K : ℕ) : ℝ) = ((min n K : ℕ) : ℝ)+1 := by
          have hn : min (n+1) K = min n K+1 := by omega
          exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) hn
        exact hm
      · rw [if_neg h, add_zero]
        have hn : min (n+1) K = min n K := by omega
        exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) hn

/-- Every finite tail partial sum is dominated by the mean. -/
theorem sum_tail_le_integral_natCast [IsProbabilityMeasure μ]
    {K : Ω → ℕ} (hK : Measurable K) (hKi : Integrable (fun ω => (K ω : ℝ)) μ) (n : ℕ) :
    (∑ j ∈ Finset.range n, μ.real {ω | j < K ω}) ≤ ∫ ω, (K ω : ℝ) ∂μ := by
  have hms : ∀ j : ℕ, MeasurableSet {ω | j < K ω} := fun j =>
    measurableSet_lt measurable_const hK
  have hmm : Measurable (fun ω => ((min n (K ω) : ℕ) : ℝ)) :=
    measurable_from_nat.comp (measurable_const.min hK)
  have hmin : Integrable (fun ω => ((min n (K ω) : ℕ) : ℝ)) μ := by
    apply hKi.mono' hmm.aestronglyMeasurable
    refine ae_of_all _ fun ω => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact Nat.cast_le.mpr (min_le_right n (K ω))
  have hsum : (∫ ω, ((min n (K ω) : ℕ) : ℝ) ∂μ) =
      ∑ j ∈ Finset.range n, μ.real {ω | j < K ω} := by
    have he : (fun ω => ((min n (K ω) : ℕ) : ℝ)) =
        fun ω => ∑ j ∈ Finset.range n, Set.indicator {ω | j < K ω} (fun _ => (1 : ℝ)) ω := by
      funext ω
      rw [min_eq_sum_indicator (K ω) n]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : j < K ω
      · simp [hj]
      · simp [hj]
    rw [he, integral_finsetSum _ (fun j _ => (integrable_const (1 : ℝ)).indicator (hms j))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_indicator (hms j)]
    simp [Measure.real]
  rw [← hsum]
  refine integral_mono hmin hKi (fun ω => ?_)
  exact Nat.cast_le.mpr (min_le_right n (K ω))

end SwingRepair
