import PLAStochastic.Swing.Transient.LaterSegmentLogOrder
import PLAStochastic.Swing.Transient.Brackets.ParityBrackets

/-! # Segment coefficients from a first-restart entrance limit

If the first-restart margin laws `ρ_{1,E} = Law(R_{1,E})` converge weakly to `ρ` as `E → ∞`,
then every later segment has an exact normalized mean:

`E L_{m+3,E} / (E log E) → c_{m+3} = ∫ T^m h d(ρ𝖠)`.

The Lean segment index is shifted by one (`nativeRecordingDurationNat X E (m+2)` is the
paper's `L_{m+3,E}`), so the paper's `c_k = α₂ T^{k-3} h` with `α₂ = ρ𝖠` is
`slopeIterateCoefficient X μ α₂ (k - 3)`. The proof applies the mean passage along the
identity budget `max E E₀` and rewrites `∫ v d(ρK^{m+1})` by the slope algebra.

When moreover `T(0, ·) ≤ α₂` against monotone slope tests, the parity brackets and the `W₁`
error bound for slope laws apply to these actual coefficients.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SwingRepair
open LeadingCoefficient KernelLimit SlopeEvaluation

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-- **Exact segment coefficients.**  If `ρ_{1,E} ⇒ ρ`, then for every `m`,
`E L_{m+3,E} / (E log E) → ∫ T^m h d(ρ𝖠)`. -/
theorem transientNormalizedMean_tendsto_of_marginLimit [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {ρ : ProbabilityMeasure ℝ}
    (hρ : let _ : IsProbabilityMeasure μ := hi.isProbabilityMeasure
      Tendsto (fun E : ℝ => nativeTransientMarginProb μ hX E 1) atTop (𝓝 ρ)) (m : ℕ) :
    Tendsto (fun E => transientNormalizedMean X μ E (m+2)) atTop
      (𝓝 (slopeIterateCoefficient X μ (slopeStationaryLaw X μ (ρ : Measure ℝ)) m)) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  let : IsMarkovKernel (swingMarginKernel X μ) := swingMarginKernel_isMarkov hX hi hG
  set budget : ℝ → ℝ := fun E => max E stationaryScaleThreshold with hbdef
  have hbudget : ∀ E, stationaryScaleThreshold ≤ budget E := fun E => le_max_right _ _
  have hbudget_top : Tendsto budget atTop atTop :=
    tendsto_atTop_mono (fun E => le_max_left E _) tendsto_id
  have hν : Tendsto (fun E => nativeTransientMarginProb μ hX (budget E) 1) atTop (𝓝 ρ) :=
    hρ.comp hbudget_top
  have hmean : Tendsto (fun E => (∫ ω, (nativeRecordingDurationNat X (budget E) (m+2) ω : ℝ) ∂μ) /
        (budget E * Real.log (budget E))) atTop
      (𝓝 (∫ r, marginLeadingReward X μ r ∂
        (compProbIter (swingMarginKernel X μ) (m+1) ρ : Measure ℝ))) :=
    nativeRecordingDurationNat_normalizedMean_tendsto hX hi hG hbudget hbudget_top hν m
  rw [compProbIter_coe, integral_marginLeadingReward_iterate_eq hX hi hG] at hmean
  refine hmean.congr' ?_
  filter_upwards [eventually_ge_atTop stationaryScaleThreshold] with E hE
  simp only [transientNormalizedMean, hbdef, max_eq_left hE]

/-- The entrance slope law `α₂ = ρ𝖠` of a first-restart limit has a first moment. -/
theorem slopeStationaryLaw_integrable_of_marginLimit [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {ρ : ProbabilityMeasure ℝ}
    (hρ : let _ : IsProbabilityMeasure μ := hi.isProbabilityMeasure
      Tendsto (fun E : ℝ => nativeTransientMarginProb μ hX E 1) atTop (𝓝 ρ)) :
    Integrable (fun b : ℝ => b) (slopeStationaryLaw X μ (ρ : Measure ℝ)) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  set budget : ℝ → ℝ := fun E => max E stationaryScaleThreshold with hbdef
  have hbudget : ∀ E, stationaryScaleThreshold ≤ budget E := fun E => le_max_right _ _
  have hbudget_top : Tendsto budget atTop atTop :=
    tendsto_atTop_mono (fun E => le_max_left E _) tendsto_id
  have hν : Tendsto (fun E => nativeTransientMarginProb μ hX (budget E) 1) atTop (𝓝 ρ) :=
    hρ.comp hbudget_top
  have hνabs := (limit_integral_le_of_forall_integral_le (g := fun x : ℝ => |x|) hν
    continuous_abs (fun x => abs_nonneg x)
    (fun E => (nativeTransientMarginLaw_abs_le hX hi hG (hbudget E) 0).1)
    (fun E => (nativeTransientMarginLaw_abs_le hX hi hG (hbudget E) 0).2)).1
  exact slopeStationaryLaw_first_moment_integrable hX hi hG hνabs

/-- **Actual-coefficient brackets from an entrance limit.**  If `ρ_{1,E} ⇒ ρ` and
`T(0, ·) ≤ α₂ = ρ𝖠` against monotone slope tests, then the actual coefficients
`c_{m+3} = lim E L_{m+3,E}/(E log E)` exist, the even ones decrease and the odd ones increase
to `γ_Swing`, which they bracket, and `|c_{m+3} - γ_Swing| ≤ L_h W₁(α₂, λ) (3/4)^m`. -/
theorem transient_coefficient_brackets_of_marginLimit [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {ρ : ProbabilityMeasure ℝ}
    (hρ : let _ : IsProbabilityMeasure μ := hi.isProbabilityMeasure
      Tendsto (fun E : ℝ => nativeTransientMarginProb μ hX E 1) atTop (𝓝 ρ))
    (hα0 : SlopeTestLE (swingSlopeChainKernel X μ 0) (slopeStationaryLaw X μ (ρ : Measure ℝ)))
    {νst : Measure ℝ} [IsProbabilityMeasure νst]
    (hinv : Kernel.Invariant (swingMarginKernel X μ) νst)
    (hmom : Integrable (fun b : ℝ => b) (slopeStationaryLaw X μ νst)) :
    let c := slopeIterateCoefficient X μ (slopeStationaryLaw X μ (ρ : Measure ℝ))
    let γ := stationaryLeadingCoefficient X μ νst
    (∀ m, Tendsto (fun E => transientNormalizedMean X μ E (m+2)) atTop (𝓝 (c m))) ∧
    (∀ m, c (2 * m + 2) ≤ c (2 * m)) ∧ (∀ m, c (2 * m + 1) ≤ c (2 * m + 3)) ∧
    Tendsto c atTop (𝓝 γ) ∧ (∀ m, γ ≤ c (2 * m)) ∧ (∀ m, c (2 * m + 1) ≤ γ) ∧
    ∀ m, |c m - γ| ≤ slopeRewardLipschitz *
      (wassersteinOne (slopeStationaryLaw X μ (ρ : Measure ℝ))
        (slopeStationaryLaw X μ νst)).toReal * (3 / 4 : ℝ) ^ m := by
  intro c γ
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hαP : IsProbabilityMeasure (slopeStationaryLaw X μ (ρ : Measure ℝ)) :=
    slopeStationaryLaw_isProbability hX _
  have hαS : slopeStationaryLaw X μ (ρ : Measure ℝ) (Ioi 0)ᶜ = 0 := by
    rw [compl_Ioi]; exact slopeStationaryLaw_Iic_zero hX hi hG _
  have hαm := slopeStationaryLaw_integrable_of_marginLimit hX hi hG hρ
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    slopeIterateCoefficient_parity_brackets hX hi hG hαS hαm hα0 hinv hmom
  exact ⟨transientNormalizedMean_tendsto_of_marginLimit hX hi hG hρ, h1, h2, h3, h4, h5,
    abs_slopeIterateCoefficient_sub_le hX hi hG hαS hαm hinv hmom⟩

end SwingRepair
