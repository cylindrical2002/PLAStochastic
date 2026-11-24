import PLAStochastic.Swing.StationaryLimit.PrefixCrossing.Support

/-!
# Uniform-budget substitute-to-kernel estimate

The affine budget event is now a genuine state-local certificate.  This
wrapper performs the remaining bookkeeping in one place: a uniform renewal
expansion supplies the reflected-fibre estimate, the budget supplies the
positive level threshold, and the two cutoff complements pay the exceptional
mass.  No global support assertion for the prefix-state law is used.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {Ω : Type*} [MeasurableSpace Ω]

theorem prefixCrossingSubstitute_integral_sub_swingMarginKernel_of_uniform_budget_event
    {X : ℕ → Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hGau : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (E r : ℝ) (J : ℕ)
    {f : ℝ → ℝ} {K B η δ M Cenv q α β b₀ : ℝ}
    (hf : Measurable f)
    (hB : 0 ≤ B) (hη : 0 < η)
    (hδ : 0 < δ) (hδM : δ ≤ M) (hM : 0 ≤ M)
    (hCenv : 0 ≤ Cenv) (hq : 0 ≤ q)
    (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hfB : ∀ y, |f y| ≤ B)
    (hJ : 1 ≤ J) (hr : |r| ≤ K)
    (hbudget :
      41 * K + 69 * Cenv + 69 * q * (J : ℝ) +
          14 * M * (J : ℝ) + 7 * M + 21 * q ≤ E)
    (hb₀pos : 0 < b₀) (hb₀E : b₀ ≤ E)
    (hfibre : ∀ a ∈ Icc δ M, ∀ b, b₀ ≤ b →
      |gaussianWalkReflectedReward X μ f a b -
        swingOvershootReward X μ f a| ≤ η)
    (hαbad : μ.real (swingEarlySlopeGood X K δ M (J - 1))ᶜ ≤ α)
    (hβbad : μ.real
      (gaussianNegativeCarryAffineEnvelopeEvent X (2 * q) Cenv)ᶜ ≤ β) :
    |(∫ ω, f (prefixCrossingSubstitute X E r J ω) ∂μ) -
        ∫ y, f y ∂(swingMarginKernel X μ r)| ≤
      η + 4 * B * (α + β) := by
  let G : Set Ω := prefixCrossingUniformBudgetEvent X E r J K δ M Cenv q
  have hGmeas : MeasurableSet G := by
    exact prefixCrossingUniformBudgetEvent_measurableSet hX E r J K δ M Cenv q
  have hbad : μ.real Gᶜ ≤ α + β := by
    exact prefixCrossingUniformBudgetEvent_compl_measure_le_of_components
      (μ := μ) E r J hαbad hβbad
  have hstate : ∀ ω, ω ∈ G →
      prefixCrossingSlope X r J ω ∈ Icc δ M ∧
        b₀ ≤ prefixCrossingLevel X E r J ω := by
    intro ω hω
    have hsupport := prefixCrossingUniformBudgetEvent_subset_parameter_support
      (X := X) E r J hJ hδ hM hr hCenv hq hbudget hω
    exact ⟨hsupport.1, hb₀E.trans hsupport.2⟩
  have hSlope : ∀ᵐ ω ∂μ, ω ∈ G →
      prefixCrossingSlope X r J ω = swingLimitingSlope X r ω := by
    filter_upwards [] with ω
    intro hωG
    have hG' : ω ∈ swingEarlySlopeGood X K δ M (J - 1) :=
      (show ω ∈ G from hωG).1
    have hloc := swingEarlySlope_localization
      (X := X) (K₀ := K) (δ := δ) (M := M) (J := J - 1)
      hδ hG' hr
    rw [prefixCrossingSlope_eq_early (X := X) (r := r) (J := J) hJ,
      hloc.1]
  exact prefixCrossingSubstitute_integral_sub_swingMarginKernel_of_state_event
    (X := X) (μ := μ) hX hi hGau E r J hf
    (B := B) (η := η) (q := α + β) (δ := δ) (M := M) (b₀ := b₀)
    hB hη.le (add_nonneg hα hβ) hδ hδM hb₀pos hfB hfibre
    (G := G) hGmeas hbad hstate hSlope

end SwingRepair
