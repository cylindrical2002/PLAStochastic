import PLAStochastic.Swing.StationaryLimit.MarginKernel.FiniteBudget
import PLAStochastic.Swing.StationaryLimit.MarginKernel.InvariantExistence
import PLAStochastic.Swing.StationaryLimit.PrefixCrossing.LocalErrorBridge

/-! # Theorem 4.3 with the actual finite-budget margin kernel

`LimitingMarginExistence` proves the invariant-law transfer for an abstract
family of finite-budget kernels.  This file instantiates that family with the
kernel obtained from the native constrained-SSE restart map.  Consequently the
only analytic input left at this layer is the compact-uniform convergence of
the actual finite kernel to the limiting kernel; Markovness and invariance are
proved from the pathwise reflection quotient.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {Ω : Type*} [MeasurableSpace Ω]

theorem theorem_4_3_margin_weak_limit_native
    {X : ℕ → Ω → ℝ} {μ : Measure Ω} [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {budget : ι → ℝ} (hbudget : ∀ i, stationaryScaleThreshold ≤ budget i)
    {πs : ι → Measure ℝ} (hπP : ∀ i, IsProbabilityMeasure (πs i))
    (hπinv : ∀ i, (nativeRestartKernel X μ (budget i)).Invariant (πs i))
    (hunif : ∀ (f : ℝ → ℝ) (L B : ℝ), KernelLimit.IsBddLip f L B →
      ∀ (C ε : ℝ), 0 < ε →
        ∀ᶠ i in l, ∀ r : ℝ, |r| ≤ C →
          |(∫ y, f y ∂(nativeFiniteMarginKernel X μ (budget i) r)) -
            (∫ y, f y ∂(swingMarginKernel X μ r))| ≤ ε) :
    ∃ ν : ProbabilityMeasure ℝ,
      (swingMarginKernel X μ).Invariant (ν : Measure ℝ) ∧
        (ν : Measure ℝ) ≪ volume ∧ (volume : Measure ℝ) ≪ (ν : Measure ℝ) ∧
        Tendsto (fun i => stationaryMarginProb (budget i) (πs i) (hπP i)) l (𝓝 ν) ∧
        ∀ ν' : Measure ℝ, IsProbabilityMeasure ν' →
          (swingMarginKernel X μ).Invariant ν' → ν' = (ν : Measure ℝ) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hKE : ∀ i, IsMarkovKernel (nativeFiniteMarginKernel X μ (budget i)) := by
    intro i
    exact nativeFiniteMarginKernel_isMarkov hX (budget i)
  have hmarginv : ∀ i,
      (nativeFiniteMarginKernel X μ (budget i)).Invariant
        (stationaryMarginLaw (budget i) (πs i)) := by
    intro i
    exact nativeFiniteMarginLaw_invariant hX hi hG (show 0 < budget i by
      have hthr : (0 : ℝ) < stationaryScaleThreshold := by
        have hexp : (0 : ℝ) < Real.exp (2 * stationaryAbsorptionConstant) :=
          Real.exp_pos _
        exact lt_of_lt_of_le hexp (le_max_right _ _)
      exact lt_of_lt_of_le hthr (hbudget i)) (hπinv i)
  exact theorem_4_3_margin_weak_limit_actual hX hi hG hbudget hπP hπinv
    hKE hmarginv hunif

/-! A paper-facing entry point for the finite-to-substitute reduction.  The
compact-uniform kernel estimate is no longer passed as an opaque `hunif`:
the caller supplies the bad-event and substitute-law estimates separately via
`nativeFiniteMarginKernel_compact_uniform_of_randomBridge`. -/

theorem theorem_4_3_margin_weak_limit_native_of_randomBridge
    {X : ℕ → Ω → ℝ} {μ : Measure Ω} [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {budget : ι → ℝ} (hbudget : ∀ i, stationaryScaleThreshold ≤ budget i)
    {πs : ι → Measure ℝ} (hπP : ∀ i, IsProbabilityMeasure (πs i))
    (hπinv : ∀ i, (nativeRestartKernel X μ (budget i)).Invariant (πs i))
    (hinputs : ∀ (f : ℝ → ℝ) (L B : ℝ), KernelLimit.IsBddLip f L B →
      ∀ (C ε : ℝ), 0 < ε →
      ∃ J : ℕ, ∃ δ : ℝ,
        1 ≤ J ∧ 0 ≤ δ ∧ 2 * B * δ ≤ ε / 2 ∧
        ∀ᶠ i in l, ∀ r : ℝ, |r| ≤ C →
          0 ≤ budget i ∧
          μ.real (prefixCrossingLowerBridgeEventRandom X (budget i) r J)ᶜ ≤ δ ∧
          |(∫ ω, f (prefixCrossingSubstitute X (budget i) r J ω) ∂μ) -
            ∫ y, f y ∂(swingMarginKernel X μ r)| ≤ ε / 2) :
    ∃ ν : ProbabilityMeasure ℝ,
        (swingMarginKernel X μ).Invariant (ν : Measure ℝ) ∧
        (ν : Measure ℝ) ≪ volume ∧ (volume : Measure ℝ) ≪ (ν : Measure ℝ) ∧
        Tendsto (fun i => stationaryMarginProb (budget i) (πs i) (hπP i)) l (𝓝 ν) ∧
        ∀ ν' : Measure ℝ, IsProbabilityMeasure ν' →
          (swingMarginKernel X μ).Invariant ν' → ν' = (ν : Measure ℝ) := by
  apply theorem_4_3_margin_weak_limit_native hX hi hG hbudget hπP hπinv
  exact nativeFiniteMarginKernel_compact_uniform_of_randomBridge
    (X := X) (μ := μ) (budget := budget) hX hi hinputs

end SwingRepair
