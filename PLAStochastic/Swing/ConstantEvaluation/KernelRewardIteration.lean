import PLAStochastic.Swing.ConstantEvaluation.GaussianEvaluation
import PLAStochastic.Swing.StationaryLimit.MarginLawAndLeadingCoefficient

/-! # Theorem I.1 (`thm:constantcontraction`) for the actual limit law

`SlopeEvaluationGaussian` proves the evaluation bound for every invariant probability `ν`
of the margin kernel whose slope law `λ = ν𝖠` has a first moment.  Theorem 4.3
(`theorem_4_3_swing_gaussian`) produces the unique invariant law `ν_∞` as the weak limit of
the actual stationary margin laws, and the first absolute moment of that limit is a theorem
(`limit_margin_first_moment_of_actual_sq_moments`), so `λ` has a first moment
(`slopeStationaryLaw_first_moment_integrable`).  This file records the combined statement:
the constant `γ_Swing` computed by Theorem 4.3 is approximated geometrically by the iterates
`(T^m h)(a₀)` at any slope `a₀ > 0`, with the explicit rate `3/4`, the explicit Lipschitz
constant `L_h`, and the moment `∫ b dλ + a₀`.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SwingRepair
open Fluctuation LeadingCoefficient SlopeEvaluation

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-- The slope law `λ = ν_∞𝖠` of the actual limit law has a first moment. -/
theorem slopeStationaryLaw_first_moment_of_weak_limit [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {budget : ι → ℝ} (hbudget : ∀ i, stationaryScaleThreshold ≤ budget i)
    {ν : ProbabilityMeasure ℝ}
    (hweak : Tendsto (fun i => nativeStationaryMarginProb X μ (budget i)) l (𝓝 ν)) :
    Integrable (fun b : ℝ => b) (slopeStationaryLaw X μ (ν : Measure ℝ)) := by
  have hνabs : Integrable (fun r : ℝ => |r|) (ν : Measure ℝ) :=
    limit_margin_first_moment_of_actual_sq_moments (X := X) (μ := μ) hX hi hG hbudget
      (nativeStationaryFamily_isProbabilityMeasure X μ budget)
      (nativeStationaryFamily_invariant hX hi hG hbudget) hweak
  exact slopeStationaryLaw_first_moment_integrable hX hi hG hνabs

/-- **Theorem I.1 for the actual limit law.**  Under the hypotheses of Theorem 4.3 there is a
unique invariant probability `ν_∞` of the margin kernel; its leading coefficient
`γ_Swing = stationaryLeadingCoefficient X μ ν_∞` is the limit of the normalised segment means;
`λ = ν_∞𝖠` has a first moment; and for every `a₀ > 0` and `m`,

`|(T^m h)(a₀) - γ_Swing| ≤ (3/4)^m L_h (∫ b dλ + a₀)`,

while the even iterates of `h` are monotone and the odd ones antitone on `(0, ∞)`. -/
theorem theorem_I1_swing_gaussian [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {budget : ι → ℝ} (hbudget : ∀ i, stationaryScaleThreshold ≤ budget i)
    (hbudget_top : Tendsto budget l atTop) :
    ∃ ν : ProbabilityMeasure ℝ,
      (swingMarginKernel X μ).Invariant (ν : Measure ℝ) ∧
      (∀ ν' : Measure ℝ, IsProbabilityMeasure ν' →
        (swingMarginKernel X μ).Invariant ν' → ν' = (ν : Measure ℝ)) ∧
      Tendsto
        (fun i => nativeStationarySegmentMean X μ (budget i) /
          (budget i * Real.log (budget i))) l
        (𝓝 (stationaryLeadingCoefficient X μ (ν : Measure ℝ))) ∧
      Integrable (fun b : ℝ => b) (slopeStationaryLaw X μ (ν : Measure ℝ)) ∧
      (∀ a₀ : ℝ, 0 < a₀ → ∀ m : ℕ,
        |(act (swingSlopeChainKernel X μ))^[m] (slopeReward X μ) a₀ -
            stationaryLeadingCoefficient X μ (ν : Measure ℝ)| ≤
          (3 / 4 : ℝ) ^ m * slopeRewardLipschitz *
            ((∫ b, b ∂slopeStationaryLaw X μ (ν : Measure ℝ)) + a₀)) ∧
      (∀ m : ℕ,
        MonotoneOn ((act (swingSlopeChainKernel X μ))^[2 * m] (slopeReward X μ)) (Ioi 0) ∧
        AntitoneOn ((act (swingSlopeChainKernel X μ))^[2 * m + 1] (slopeReward X μ)) (Ioi 0)) := by
  obtain ⟨ν, hinv, huniq, _, _, hweak, hmean, _, _, _, _⟩ :=
    theorem_4_3_swing_gaussian hX hi hG hbudget hbudget_top
  have hmom := slopeStationaryLaw_first_moment_of_weak_limit hX hi hG hbudget hweak
  refine ⟨ν, hinv, huniq, hmean, hmom, ?_, slope_iterates_bracket_monotone hX hi hG⟩
  intro a₀ ha₀ m
  exact slope_evaluation_bound_moment hX hi hG hinv hmom ha₀ m

end SwingRepair
