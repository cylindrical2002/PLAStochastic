import PLAStochastic.Swing.StationaryLimit.LeadingCoefficient.ExplicitGamma
import PLAStochastic.Swing.StationaryLimit.LeadingCoefficient.CompactAnnulus
import PLAStochastic.Swing.StationaryScale.InvariantLawFamily
import PLAStochastic.Swing.StationaryLimit.PrefixCrossing.UniformInputs
import PLAStochastic.Swing.Ladder.Blackwell.OvershootProvider
import PLAStochastic.Swing.Ladder.Blackwell.WindowProvider

/-! # Theorem 4.3 assembled at the actual stationary family

This file removes the last *bookkeeping* hypotheses from the Theorem 4.3
chain.  Earlier entry points asked the caller for

* an abstract family `πs` of finite-budget stationary laws,
* proofs `hπP` that each member is a probability measure,
* proofs `hπinv` that each member is invariant for the actual restart kernel,
* the compact-uniform kernel inputs `hinputs`, and
* the leading-coefficient transfer `htransfer`.

All five are now produced internally: `πs` is the canonical
`nativeStationaryLaw` of `NativeStationaryFamily`, `hinputs` comes from
`exists_eventually_prefixCrossing_hinputs_of_uniform_renewal`, and the
transfer is `leadingCoefficient_integralTransfer_actual`.  The single
remaining hypothesis is the uniform overshoot provider
`UniformOvershootEquilibriumLimit` — equivalently, via
`uniformOvershootEquilibriumLimit_of_uniform_renewal`, the uniform
ladder-renewal expansion.  It is a genuine named assumption and is *not*
proved here.

The terminal theorem exposes the four paper conclusions against one and the
same limit law: uniqueness, Lebesgue equivalence, the weak limit of the actual
reflected-margin laws, and the leading-coefficient limit together with the
explicit value `γ = 4 ∫_{(0,∞)} V dν`, its integrability, its finite upper
bound and its strict positivity.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
namespace LeadingCoefficient
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

variable {Ω : Type*} [MeasurableSpace Ω]
variable {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-- `π_E` is a probability measure for every budget. -/
theorem nativeStationaryFamily_isProbabilityMeasure
    (X : ℕ → Ω → ℝ) (μ : Measure Ω) {ι : Type*} (budget : ι → ℝ) :
    ∀ i, IsProbabilityMeasure (nativeStationaryLaw X μ (budget i)) :=
  fun i => nativeStationaryLaw_isProbabilityMeasure X μ (budget i)

/-- The budget threshold of Theorem 4.2 is positive, so the stationary family
is invariant at every admissible budget. -/
theorem stationaryScaleThreshold_pos : (0 : ℝ) < stationaryScaleThreshold := by
  have hexp : (0 : ℝ) < Real.exp (2 * stationaryAbsorptionConstant) := Real.exp_pos _
  exact lt_of_lt_of_le hexp (le_max_right _ _)

theorem nativeStationaryFamily_invariant
    (hX : ∀ k, Measurable (X k)) (hi : iIndepFun X μ)
    (hG : ∀ k, μ.map (X k) = gaussianReal 0 1)
    {ι : Type*} {budget : ι → ℝ}
    (hbudget : ∀ i, stationaryScaleThreshold ≤ budget i) :
    ∀ i, (nativeRestartKernel X μ (budget i)).Invariant
      (nativeStationaryLaw X μ (budget i)) :=
  fun i => nativeStationaryLaw_invariant hX hi hG
    (lt_of_lt_of_le stationaryScaleThreshold_pos (hbudget i))

/-- The actual reflected-margin law `ν_E = π_E ∘ (y ↦ E - |y|)⁻¹`. -/
def nativeStationaryMarginProb (X : ℕ → Ω → ℝ) (μ : Measure Ω) (E : ℝ) :
    ProbabilityMeasure ℝ :=
  stationaryMarginProb E (nativeStationaryLaw X μ E)
    (nativeStationaryLaw_isProbabilityMeasure X μ E)

/-- `C_E`: the stationary segment mean of the actual restart chain. -/
def nativeStationarySegmentMean (X : ℕ → Ω → ℝ) (μ : Measure Ω) (E : ℝ) : ℝ :=
  ∫ x, nativeRestartMean X μ E x ∂(nativeStationaryLaw X μ E)

/-! ### The terminal theorem -/

/--
**Theorem 4.3 at the actual stationary family.**

Hypotheses: unit Gaussian independent increments, a budget filter above the
Theorem 4.2 threshold tending to `+∞`, and the uniform ladder-renewal
provider `hrenew`.  Nothing about the stationary laws, the finite margin
kernels or the integral transfer is assumed.

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
theorem theorem_4_3_swing_of_uniform_overshoot [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {budget : ι → ℝ} (hbudget : ∀ i, stationaryScaleThreshold ≤ budget i)
    (hbudget_top : Tendsto budget l atTop)
    (hover : UniformOvershootEquilibriumLimit X μ) :
    ∃ ν : ProbabilityMeasure ℝ,
      -- (1) invariance and uniqueness
      (swingMarginKernel X μ).Invariant (ν : Measure ℝ) ∧
      (∀ ν' : Measure ℝ, IsProbabilityMeasure ν' →
        (swingMarginKernel X μ).Invariant ν' → ν' = (ν : Measure ℝ)) ∧
      -- (2) Lebesgue equivalence
      (ν : Measure ℝ) ≪ volume ∧ (volume : Measure ℝ) ≪ (ν : Measure ℝ) ∧
      -- (3) the actual margin laws converge weakly
      Tendsto (fun i => nativeStationaryMarginProb X μ (budget i)) l (𝓝 ν) ∧
      -- (4) the leading-coefficient limit
      Tendsto
        (fun i => nativeStationarySegmentMean X μ (budget i) /
          (budget i * Real.log (budget i))) l
        (𝓝 (stationaryLeadingCoefficient X μ (ν : Measure ℝ))) ∧
      -- (5) the explicit value
      stationaryLeadingCoefficient X μ (ν : Measure ℝ) =
        4 * ∫ r in Ioi (0 : ℝ), gaussianRenewalPotential X μ r ∂(ν : Measure ℝ) ∧
      -- (6) integrability and an explicit finite bound
      IntegrableOn (gaussianRenewalPotential X μ) (Ioi (0 : ℝ)) (ν : Measure ℝ) ∧
      stationaryLeadingCoefficient X μ (ν : Measure ℝ) ≤
        4 * (gaussianExcessExpMomentBound 2 + ∫ r, |r| ∂(ν : Measure ℝ)) ∧
      -- (7) strict positivity
      0 < stationaryLeadingCoefficient X μ (ν : Measure ℝ) := by
  let _ : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  set πs : ι → Measure ℝ := fun i => nativeStationaryLaw X μ (budget i) with hπs
  have hπP : ∀ i, IsProbabilityMeasure (πs i) :=
    nativeStationaryFamily_isProbabilityMeasure X μ budget
  have hπinv : ∀ i, (nativeRestartKernel X μ (budget i)).Invariant (πs i) :=
    nativeStationaryFamily_invariant hX hi hG hbudget
  have hinputs : ∀ (f : ℝ → ℝ) (L B : ℝ), KernelLimit.IsBddLip f L B →
      ∀ (C ε : ℝ), 0 < ε →
        ∃ J : ℕ, ∃ δ : ℝ,
          1 ≤ J ∧ 0 ≤ δ ∧ 2 * B * δ ≤ ε / 2 ∧
          ∀ᶠ i in l, ∀ r : ℝ, |r| ≤ C →
            0 ≤ budget i ∧
            μ.real (prefixCrossingLowerBridgeEventRandom X (budget i) r J)ᶜ ≤ δ ∧
            |(∫ ω, f (prefixCrossingSubstitute X (budget i) r J ω) ∂μ) -
              ∫ y, f y ∂(swingMarginKernel X μ r)| ≤ ε / 2 := by
    intro f L B hf C ε hε
    obtain ⟨J, δ, hJ, hδ, hsplit, hev⟩ :=
      exists_eventually_prefixCrossing_hinputs_of_uniform_overshoot
        (X := X) (μ := μ) hX hi hG hbudget_top hover f L B hf
        (K := max C 0) (le_max_right _ _) hε
    refine ⟨J, δ, hJ, hδ, hsplit, ?_⟩
    filter_upwards [hev] with i hi'
    intro r hr
    exact hi' r (hr.trans (le_max_left _ _))
  obtain ⟨ν, hinv, hac, hca, hweak, huniq⟩ :=
    theorem_4_3_margin_weak_limit_native_of_randomBridge
      (X := X) (μ := μ) hX hi hG hbudget hπP hπinv hinputs
  -- the leading-coefficient limit at the same `ν`
  have htransfer := leadingCoefficient_integralTransfer_actual
    (X := X) (μ := μ) hX hi hG hbudget hbudget_top hπP hπinv hweak hac
  have hbridge : ∀ i,
      (∫ x, nativeRestartMean X μ (budget i) x ∂(πs i)) /
          (budget i * Real.log (budget i)) =
        ∫ r, normalizedFrozenMean X μ (budget i) r ∂
          (stationaryMarginLaw (budget i) (πs i)) := by
    intro i
    let _ : IsProbabilityMeasure (πs i) := hπP i
    exact nativeRestart_normalizedMean_eq_margin_integral hX hi hG
  have hmean := theorem_4_3_leading_coefficient_actual
    (X := X) (μ := μ) (hπP := hπP) hweak hbridge htransfer
  -- the first absolute moment of the limit law
  have hνabs : Integrable (fun r : ℝ => |r|) (ν : Measure ℝ) :=
    limit_margin_first_moment_of_actual_sq_moments
      (X := X) (μ := μ) hX hi hG hbudget hπP hπinv hweak
  refine ⟨ν, hinv, huniq, hac, hca, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hweak
  · exact hmean
  · exact stationaryLeadingCoefficient_eq X μ (ν : Measure ℝ)
  · exact gaussianRenewalPotential_integrableOn_Ioi hX hi hG hνabs
  · exact stationaryLeadingCoefficient_le hX hi hG hνabs
  · exact stationaryLeadingCoefficient_pos hX hi hG hνabs hca

/-- The same terminal theorem with the *scalar* overshoot-tail provider.  This
is the weakest of the three equivalent-strength entry points and the one a
coupling proof should target. -/
theorem theorem_4_3_swing_of_overshoot_tail [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {budget : ι → ℝ} (hbudget : ∀ i, stationaryScaleThreshold ≤ budget i)
    (hbudget_top : Tendsto budget l atTop)
    (htail : UniformOvershootTailLimit X μ) :
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
  theorem_4_3_swing_of_uniform_overshoot hX hi hG hbudget hbudget_top
    (uniformOvershootEquilibriumLimit_of_tail_limit hX hi hG htail)

/-- The same terminal theorem with the **bare uniform Blackwell** provider:
only `U_a((b-x,b]) → x/μ_a`, uniformly over the drift strip and over window
lengths in a compact range, is assumed.  Neither the Blanchet--Glynn constant
term nor its exponential rate appears. -/
theorem theorem_4_3_swing_of_renewal_window [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {budget : ι → ℝ} (hbudget : ∀ i, stationaryScaleThreshold ≤ budget i)
    (hbudget_top : Tendsto budget l atTop)
    (hwin : UniformRenewalWindowLimit X μ) :
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
  theorem_4_3_swing_of_overshoot_tail hX hi hG hbudget hbudget_top
    (uniformOvershootTailLimit_of_windowLimit hX hi hG hwin)

/-- The same terminal theorem with the Blanchet--Glynn renewal expansion as
the provider.  It is strictly stronger as a hypothesis, by
`uniformOvershootEquilibriumLimit_of_uniform_renewal`. -/
theorem theorem_4_3_swing [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {budget : ι → ℝ} (hbudget : ∀ i, stationaryScaleThreshold ≤ budget i)
    (hbudget_top : Tendsto budget l atTop)
    (hrenew : ∀ {δ M : ℝ}, 0 < δ → 0 ≤ M →
      ∃ Cexp c : ℝ,
        UniformLadderRenewalExpansion
          (gaussianAscendingLadderLaw X μ) (Icc δ M) Cexp c) :
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
  theorem_4_3_swing_of_uniform_overshoot hX hi hG hbudget hbudget_top
    (uniformOvershootEquilibriumLimit_of_uniform_renewal hX hi hG hrenew)

end LeadingCoefficient
end SwingRepair
