import PLAStochastic.Swing.StationaryLimit.LeadingCoefficient.LimitRewardBounds

/-! A small algebraic bridge from the `farCut` estimates to the compact cutoff
used in `IntegralTransferHypothesis`. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
namespace LeadingCoefficient
set_option maxHeartbeats 1000000

variable {Ω : Type*} [MeasurableSpace Ω]
variable {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-- The compact-cutoff remainder is exactly the nonnegative far-cutoff
contribution, hence it is bounded by the corresponding tail set integral. -/
theorem marginLeadingReward_compactCutoff_remainder_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hνabs : Integrable (fun r : ℝ => |r|) ν) {C : ℝ} (hC : 0 ≤ C) :
    |(∫ r, marginLeadingReward X μ r * compactCutoff C r ∂ν) -
      ∫ r, marginLeadingReward X μ r ∂ν| ≤
      ∫ r in {r : ℝ | C < |r|}, marginLeadingReward X μ r ∂ν := by
  let f : ℝ → ℝ := marginLeadingReward X μ
  have hf := marginLeadingReward_integrable_of_abs_integrable hX hi hG hνabs
  have hcomp : Integrable (fun r => f r * compactCutoff C r) ν :=
    hf.mul_bdd (μ := ν) (compactCutoff_continuous C).measurable.aestronglyMeasurable
      (ae_of_all _ (fun r => by
        rw [Real.norm_eq_abs, abs_of_nonneg (compactCutoff_nonneg C r)]
        exact compactCutoff_le_one C r))
  have hfar : Integrable (fun r => f r * KernelLimit.farCut C r) ν :=
    hf.mul_bdd (μ := ν) (KernelLimit.continuous_farCut C).measurable.aestronglyMeasurable
      (ae_of_all _ (fun r => by
        rw [Real.norm_eq_abs, abs_of_nonneg (KernelLimit.farCut_nonneg C r)]
        exact KernelLimit.farCut_le_one C r))
  have hdecomp : (∫ r, f r * compactCutoff C r ∂ν) - ∫ r, f r ∂ν =
      -(∫ r, f r * KernelLimit.farCut C r ∂ν) := by
    have heq : (fun r => f r * compactCutoff C r +
        f r * KernelLimit.farCut C r) = f := by
      funext r
      unfold compactCutoff
      ring
    have hi_eq : (∫ r, f r * compactCutoff C r ∂ν) +
        ∫ r, f r * KernelLimit.farCut C r ∂ν = ∫ r, f r ∂ν := by
      rw [← integral_add hcomp hfar]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun r => by rw [heq]))
    linarith
  rw [hdecomp, abs_neg]
  have hnon : 0 ≤ ∫ r, f r * KernelLimit.farCut C r ∂ν := by
    apply integral_nonneg
    intro r
    exact mul_nonneg (marginLeadingReward_nonneg hX hi hG) (KernelLimit.farCut_nonneg C r)
  rw [abs_of_nonneg hnon]
  exact marginLeadingReward_farCut_integral_le hX hi hG hνabs hC

/-- The limit-law half of the compact cutoff transfer can therefore be made
arbitrarily small from absolute continuity and the first-moment bound. -/
theorem exists_marginLeadingReward_compactCutoff_remainder_lt
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hνabs : Integrable (fun r : ℝ => |r|) ν)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      |(∫ r, marginLeadingReward X μ r * compactCutoff C r ∂ν) -
        ∫ r, marginLeadingReward X μ r ∂ν| < ε := by
  obtain ⟨C, hC, htail⟩ := exists_marginLeadingReward_far_cutoff
    hX hi hG hνabs hε
  refine ⟨C, hC, ?_⟩
  exact lt_of_le_of_lt
    (marginLeadingReward_compactCutoff_remainder_le hX hi hG hνabs hC) htail

/-- Finite-budget analogue: the stationary normalized frozen mean has a
uniform second-moment tail, which controls its compact-cutoff remainder. -/
theorem normalizedFrozenMean_compactCutoff_remainder_le
    [SFinite μ] (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E C : ℝ}
    (hE : stationaryScaleThreshold ≤ E) (hC : 1 ≤ C)
    {π : Measure ℝ} [IsProbabilityMeasure π]
    (hπ : (nativeRestartKernel X μ E).Invariant π) :
    |(∫ r, normalizedFrozenMean X μ E r * compactCutoff C r ∂
        (stationaryMarginLaw E π)) -
      ∫ r, normalizedFrozenMean X μ E r ∂(stationaryMarginLaw E π)| ≤
      (4 * frozenUniformMeanConstant / C) * stationaryMarginMomentBound 2 := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hEone : Real.exp 1 ≤ E := by
    exact (le_max_right _ _).trans ((le_max_left _ _).trans hE)
  have hE1 : 1 ≤ E := by
    have h1 : (1 : ℝ) ≤ Real.exp 1 := by norm_num
    exact h1.trans hEone
  let ν : Measure ℝ := stationaryMarginLaw E π
  let f : ℝ → ℝ := normalizedFrozenMean X μ E
  let : IsProbabilityMeasure ν := isProbabilityMeasure_stationaryMarginLaw E π
  have hf : Integrable f ν := by
    simpa [f, ν] using normalizedFrozenMean_integrable_stationaryMarginLaw
      (X := X) (μ := μ) hX hi hG hE hπ
  have hcomp : Integrable (fun r => f r * compactCutoff C r) ν :=
    hf.mul_bdd (μ := ν) (compactCutoff_continuous C).measurable.aestronglyMeasurable
      (ae_of_all _ (fun r => by
        rw [Real.norm_eq_abs, abs_of_nonneg (compactCutoff_nonneg C r)]
        exact compactCutoff_le_one C r))
  have hfar : Integrable (fun r => f r * KernelLimit.farCut C r) ν :=
    hf.mul_bdd (μ := ν) (KernelLimit.continuous_farCut C).measurable.aestronglyMeasurable
      (ae_of_all _ (fun r => by
        rw [Real.norm_eq_abs, abs_of_nonneg (KernelLimit.farCut_nonneg C r)]
        exact KernelLimit.farCut_le_one C r))
  have hdecomp : (∫ r, f r * compactCutoff C r ∂ν) - ∫ r, f r ∂ν =
      -(∫ r, f r * KernelLimit.farCut C r ∂ν) := by
    have heq : (fun r => f r * compactCutoff C r +
        f r * KernelLimit.farCut C r) = f := by
      funext r
      unfold compactCutoff
      ring
    have hi_eq : (∫ r, f r * compactCutoff C r ∂ν) +
        ∫ r, f r * KernelLimit.farCut C r ∂ν = ∫ r, f r ∂ν := by
      rw [← integral_add hcomp hfar]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun r => by rw [heq]))
    linarith
  rw [hdecomp, abs_neg]
  have hnon : 0 ≤ ∫ r, f r * KernelLimit.farCut C r ∂ν := by
    apply integral_nonneg
    intro r
    exact mul_nonneg (normalizedFrozenMean_nonneg hX hi hG hE1)
      (KernelLimit.farCut_nonneg C r)
  rw [abs_of_nonneg hnon]
  let S : Set ℝ := {r : ℝ | C < |r|}
  have hS : MeasurableSet S := KernelLimit.measurableSet_abs_gt C
  have hset : Integrable (S.indicator f) ν := hf.indicator hS
  have hpoint : ∀ r, f r * KernelLimit.farCut C r ≤ S.indicator f r := by
    intro r
    by_cases hr : r ∈ S
    · rw [Set.indicator_of_mem hr]
      exact mul_le_of_le_one_right (normalizedFrozenMean_nonneg hX hi hG hE1)
        (KernelLimit.farCut_le_one C r)
    · rw [Set.indicator_of_notMem hr]
      have hz : KernelLimit.farCut C r = 0 :=
        KernelLimit.farCut_eq_zero (le_of_not_gt hr)
      simp [hz]
  have hfar_le : (∫ r, f r * KernelLimit.farCut C r ∂ν) ≤
      ∫ r in S, f r ∂ν := by
    calc
      (∫ r, f r * KernelLimit.farCut C r ∂ν) ≤
          ∫ r, S.indicator f r ∂ν := integral_mono hfar hset hpoint
      _ = ∫ r in S, f r ∂ν := by rw [integral_indicator hS]
  have htail := normalizedFrozenMean_setIntegral_abs_gt_le
    (X := X) (μ := μ) hX hi hG hE hC hπ
  exact le_trans hfar_le htail

end LeadingCoefficient
end SwingRepair
