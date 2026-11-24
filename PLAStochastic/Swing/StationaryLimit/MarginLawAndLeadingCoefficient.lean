import PLAStochastic.Swing.StationaryLimit.AssemblyFromOvershootProvider
import PLAStochastic.Swing.Ladder.Blackwell.UniformWindowLimit

/-! # Theorem 4.3, unconditional

`Theorem43Complete` exposes the paper conclusions of Theorem 4.3 against a
single named provider.  `UniformBlackwell` proves the weakest of those
providers, `UniformRenewalWindowLimit X μ`, from the unit Gaussian
independent increments alone.  This file joins the two: the only hypotheses
left are the model hypotheses (`hX`, `hi`, `hG`) and the budget filter of
Theorem 4.2.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
namespace LeadingCoefficient

variable {Ω : Type*} [MeasurableSpace Ω]
variable {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/--
**Theorem 4.3 (Swing), unconditional.**

Hypotheses: unit Gaussian independent increments and a budget filter above the
Theorem 4.2 threshold tending to `+∞`.  No renewal provider is assumed; the
uniform Blackwell renewal theorem for the Gaussian ladder family is
`uniformRenewalWindowLimit_gaussian`.

Conclusions, all for the same `ν`:

1. `ν` is invariant for the limiting margin kernel `K`, and is the *unique*
   invariant probability;
2. `ν` and Lebesgue measure are mutually absolutely continuous;
3. the actual reflected-margin laws `ν_E` converge weakly to `ν`;
4. `C_E/(E log E) → γ` with `γ = stationaryLeadingCoefficient`;
5. `γ = 4 ∫_{(0,∞)} V dν`;
6. `V` is integrable on `(0,∞)` against `ν` and `γ` has an explicit finite
   upper bound;
7. `0 < γ`.
-/
theorem theorem_4_3_swing_gaussian [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {budget : ι → ℝ} (hbudget : ∀ i, stationaryScaleThreshold ≤ budget i)
    (hbudget_top : Tendsto budget l atTop) :
    ∃ ν : ProbabilityMeasure ℝ,
      (swingMarginKernel X μ).Invariant (ν : Measure ℝ) ∧
      (∀ ν' : Measure ℝ, IsProbabilityMeasure ν' →
        (swingMarginKernel X μ).Invariant ν' → ν' = (ν : Measure ℝ)) ∧
      (ν : Measure ℝ) ≪ volume ∧ (volume : Measure ℝ) ≪ (ν : Measure ℝ) ∧
      Tendsto (fun i => nativeStationaryMarginProb X μ (budget i)) l (𝓝 ν) ∧
      Tendsto
        (fun i => nativeStationarySegmentMean X μ (budget i) /
          (budget i * Real.log (budget i))) l
        (𝓝 (stationaryLeadingCoefficient X μ (ν : Measure ℝ))) ∧
      stationaryLeadingCoefficient X μ (ν : Measure ℝ) =
        4 * ∫ r in Ioi (0 : ℝ), gaussianRenewalPotential X μ r ∂(ν : Measure ℝ) ∧
      IntegrableOn (gaussianRenewalPotential X μ) (Ioi (0 : ℝ)) (ν : Measure ℝ) ∧
      stationaryLeadingCoefficient X μ (ν : Measure ℝ) ≤
        4 * (gaussianExcessExpMomentBound 2 + ∫ r, |r| ∂(ν : Measure ℝ)) ∧
      0 < stationaryLeadingCoefficient X μ (ν : Measure ℝ) :=
  theorem_4_3_swing_of_renewal_window hX hi hG hbudget hbudget_top
    (uniformRenewalWindowLimit_gaussian hX hi hG)

/-- The uniform overshoot-tail provider, now a theorem. -/
theorem uniformOvershootTailLimit_gaussian
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    UniformOvershootTailLimit X μ :=
  uniformOvershootTailLimit_of_windowLimit hX hi hG (uniformRenewalWindowLimit_gaussian hX hi hG)

end LeadingCoefficient
end SwingRepair
