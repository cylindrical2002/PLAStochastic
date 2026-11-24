import PLAStochastic.Swing.SecondSegment.Coefficient.Transfer
import PLAStochastic.Swing.ConstantEvaluation.SlopeKernelReduction

/-! # The second-segment coefficient through the initial slope law

`second-coefficient.md`, C2.12 (E28 of the plan).  With the margin-to-slope
kernel `𝖠(r, da) = Law(A_r)` (`swingSlopeKernel`) and `α = ν𝖠`
(`slopeStationaryLaw`),

`∫ ℓ dν = 2 ∫ a⁻¹ α(da)`.

This is Fubini for the kernel composition: `∫ a⁻¹ 𝖠(r, da) = E[1/A_r] = ℓ(r)/2`
for every negative margin, and a law carried by `(-∞, 0)` that integrates `ℓ`
makes `a⁻¹` integrable against `ν𝖠`.  The same initial slope law `α` drives the
later segment coefficients, so the second coefficient needs no separate
constant.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-- `E[1/A_r] = ℓ(r)/2` for a negative margin. -/
theorem inv_swingLimitingSlope_integrable_and_integral
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {r : ℝ} (hr : r < 0) :
    Integrable (fun ω => (swingLimitingSlope X r ω)⁻¹) μ ∧
      (∫ ω, (swingLimitingSlope X r ω)⁻¹ ∂μ) = secondSegmentLimitKernel X μ r / 2 := by
  have heq : (fun ω => (swingLimitingSlope X r ω)⁻¹) =
      fun ω => 2 / swingLimitingSlope X r ω / 2 := by
    funext ω
    ring
  rw [heq]
  exact ⟨(two_div_swingLimitingSlope_integrable hX hi hG hr).div_const 2, integral_div _ _⟩

/-- `∫ a⁻¹ 𝖠(r, da) = ℓ(r)/2`, together with the integrability of `a⁻¹`. -/
theorem swingSlopeKernel_inv
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {r : ℝ} (hr : r < 0) :
    Integrable (fun a : ℝ => a⁻¹) (swingSlopeKernel X μ r) ∧
      (∫ a, a⁻¹ ∂swingSlopeKernel X μ r) = secondSegmentLimitKernel X μ r / 2 ∧
      (∫ a, ‖a⁻¹‖ ∂swingSlopeKernel X μ r) = secondSegmentLimitKernel X μ r / 2 := by
  have := hi.isProbabilityMeasure
  obtain ⟨hint, hval⟩ := inv_swingLimitingSlope_integrable_and_integral hX hi hG hr
  refine ⟨?_, ?_, ?_⟩
  · rw [swingSlopeKernel_eq_law hX r, swingLimitingSlopeLaw,
      integrable_map_measure measurable_inv.aestronglyMeasurable
        (swingLimitingSlope_measurable hX r).aemeasurable]
    exact hint
  · rw [swingSlopeKernel_integral hX r measurable_inv]
    exact hval
  · rw [swingSlopeKernel_integral hX r measurable_inv.norm, ← hval]
    refine integral_congr_ae ?_
    filter_upwards [swingLimitingSlope_pos_ae hX hi hG r] with ω hω
    exact Real.norm_of_nonneg (inv_nonneg.mpr hω.le)

/-- **C2.12.**  For a law carried by `(-∞, 0)` that integrates `ℓ`,
`∫ ℓ dρ = 2 ∫ a⁻¹ d(ρ𝖠)`, and `a⁻¹` is `ρ𝖠`-integrable. -/
theorem secondSegmentLimitKernel_integral_eq_slope
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    (hneg : ∀ᵐ r ∂ρ, r < 0) (hint : Integrable (secondSegmentLimitKernel X μ) ρ) :
    Integrable (fun a : ℝ => a⁻¹) (slopeStationaryLaw X μ ρ) ∧
      (∫ r, secondSegmentLimitKernel X μ r ∂ρ) =
        2 * ∫ a, a⁻¹ ∂(slopeStationaryLaw X μ ρ) := by
  have := hi.isProbabilityMeasure
  have hA := swingSlopeKernel_isMarkov (μ := μ) hX
  have hcompint : Integrable (fun a : ℝ => a⁻¹) (slopeStationaryLaw X μ ρ) := by
    rw [slopeStationaryLaw, Measure.integrable_comp_iff measurable_inv.aestronglyMeasurable]
    refine ⟨?_, ?_⟩
    · filter_upwards [hneg] with r hr
      exact (swingSlopeKernel_inv hX hi hG hr).1
    · refine (hint.div_const 2).congr ?_
      filter_upwards [hneg] with r hr
      exact ((swingSlopeKernel_inv hX hi hG hr).2.2).symm
  refine ⟨hcompint, ?_⟩
  rw [slopeStationaryLaw, KernelLimit.integral_comp_eq hcompint]
  rw [integral_congr_ae (hneg.mono fun r hr => (swingSlopeKernel_inv hX hi hG hr).2.1),
    integral_div]
  ring

/-- **E28.**  Along every filter on which the first-margin laws converge to `ν`,
the second-segment coefficient is twice the mean inverse slope under `ν𝖠`. -/
theorem secondSegment_coefficient_eq_slope
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {ι : Type*} {l : Filter ι} [l.NeBot] {budget : ι → ℝ}
    (hbudget_top : Tendsto budget l atTop) {ν : ProbabilityMeasure ℝ}
    (hν : let _ : IsProbabilityMeasure μ := hi.isProbabilityMeasure
      Tendsto (fun i => nativeTransientMarginProb μ hX (budget i) 1) l (𝓝 ν)) :
    Integrable (fun a : ℝ => a⁻¹) (slopeStationaryLaw X μ (ν : Measure ℝ)) ∧
      (∫ r, secondSegmentLimitKernel X μ r ∂(ν : Measure ℝ)) =
        2 * ∫ a, a⁻¹ ∂(slopeStationaryLaw X μ (ν : Measure ℝ)) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hν' : Tendsto (fun i => nativeTransientMarginProb μ hX (budget i) 1) l (𝓝 ν) := hν
  obtain ⟨-, -, hint, -⟩ := secondSegment_entranceLimit_properties hX hi hG hbudget_top hν
  exact secondSegmentLimitKernel_integral_eq_slope hX hi hG
    (firstMarginLimit_ae_neg hX hi hG hbudget_top hν') hint

/-- C2.1 read through the slope law: `E L_{2,E}/E → 2 ∫ a⁻¹ d(ν𝖠)`. -/
theorem secondSegment_normalizedMean_tendsto_slope
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {ι : Type*} {l : Filter ι} [l.NeBot] {budget : ι → ℝ}
    (hbudget_top : Tendsto budget l atTop) {ν : ProbabilityMeasure ℝ}
    (hν : let _ : IsProbabilityMeasure μ := hi.isProbabilityMeasure
      Tendsto (fun i => nativeTransientMarginProb μ hX (budget i) 1) l (𝓝 ν)) :
    Tendsto (fun i => (∫ ω, (nativeRecordingDurationNat X (budget i) 1 ω : ℝ) ∂μ) / budget i) l
      (𝓝 (2 * ∫ a, a⁻¹ ∂(slopeStationaryLaw X μ (ν : Measure ℝ)))) := by
  rw [← (secondSegment_coefficient_eq_slope hX hi hG hbudget_top hν).2]
  exact secondSegment_normalizedMean_tendsto hX hi hG hbudget_top hν

end SwingRepair
