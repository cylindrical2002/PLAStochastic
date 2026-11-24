import PLAStochastic.Swing.Entrance.Limit
import PLAStochastic.Swing.Transient.Coefficients.EntranceOrder
import PLAStochastic.Swing.SecondSegment.Coefficient.SlopeForm

/-! # Exact transient segment coefficients of the native Swing filter

With the first-restart entrance law `ρ = θ Law(-O) + (1 - θ) Law(-(U + O))` and its slope law
`α₂ = ρ𝖠`:

* **S-SCALE (exact constants).**  `E L_{2,E} / E → κ₂ = 2 ∫ a⁻¹ α₂(da) > 0`, and for every
  `k ≥ 3`, `E L_{k,E} / (E log E) → c_k = α₂ T^{k-3} h > 0`.
* **S-BRACKET (actual coefficients).**  With `γ_Swing` the stationary leading coefficient of the
  unique invariant margin law and `λ` its slope law, the even-offset coefficients
  `c_3 ≥ c_5 ≥ ⋯` decrease and the odd-offset ones `c_4 ≤ c_6 ≤ ⋯` increase to `γ_Swing`, which
  they bracket, and `|c_k - γ_Swing| ≤ L_h W₁(α₂, λ) (3/4)^{k-3}`.

The Lean segment index is shifted by one: `nativeRecordingDurationNat X E j` is the paper's
`L_{j+1,E}`, and `c_{m+3}` is `slopeIterateCoefficient X μ α₂ m`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace SwingRepair

noncomputable section

open LeadingCoefficient KernelLimit SlopeEvaluation

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-- **S-SCALE, exact constants.**  `E L_{2,E}/E → κ₂ = 2 ∫ a⁻¹ dα₂ > 0` and, for every `m`,
`E L_{m+3,E}/(E log E) → c_{m+3} = α₂ T^m h > 0`, where `α₂ = ρ𝖠` is the slope law of the
first-restart entrance law `ρ`. -/
theorem swing_transient_coefficients [SFinite μ] (hX : ∀ j, Measurable (X j))
    (hi : iIndepFun X μ) (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) :
    let α₂ := slopeStationaryLaw X μ (entranceLaw X μ)
    Tendsto (fun E => (∫ ω, (nativeRecordingDurationNat X E 1 ω : ℝ) ∂μ) / E) atTop
        (𝓝 (2 * ∫ a, a⁻¹ ∂α₂)) ∧
      0 < 2 * ∫ a, a⁻¹ ∂α₂ ∧
      ∀ m : ℕ, Tendsto (fun E => transientNormalizedMean X μ E (m + 2)) atTop
          (𝓝 (slopeIterateCoefficient X μ α₂ m)) ∧ 0 < slopeIterateCoefficient X μ α₂ m := by
  intro α₂
  set ρ : ProbabilityMeasure ℝ := ⟨entranceLaw X μ, entranceLaw_isProbabilityMeasure hX hi hG⟩
  have hρ := nativeTransientMarginProb_tendsto_entranceLaw hX hi hG
  have hκ := secondSegment_normalizedMean_tendsto_slope hX hi hG (ν := ρ) tendsto_id hρ
  obtain ⟨-, -, -, hpos⟩ := secondSegment_entranceLimit_properties hX hi hG (ν := ρ) tendsto_id hρ
  rw [(secondSegment_coefficient_eq_slope hX hi hG (ν := ρ) tendsto_id hρ).2] at hpos
  obtain ⟨_, -, -, -, -, hlim⟩ := theorem_4_4_swing_gaussian hX hi hG
  refine ⟨hκ, hpos, fun m => ⟨transientNormalizedMean_tendsto_of_marginLimit hX hi hG hρ m, ?_⟩⟩
  obtain ⟨⟨c, hc, hlow⟩, -, -⟩ := hlim m
  exact hc.trans_le (ge_of_tendsto (transientNormalizedMean_tendsto_of_marginLimit hX hi hG hρ m)
    hlow)

/-- **S-BRACKET for the actual coefficients.**  Let `ν_∞` be the unique invariant margin law,
`γ_Swing` its leading coefficient and `λ = ν_∞𝖠`. The actual coefficients
`c_{m+3} = α₂ T^m h` satisfy `c_{2m+2} ≤ c_{2m}`, `c_{2m+1} ≤ c_{2m+3}`, `c_m → γ_Swing`,
`c_{2m+1} ≤ γ_Swing ≤ c_{2m}` (offsets from `k = 3`), and
`|c_{m+3} - γ_Swing| ≤ L_h W₁(α₂, λ) (3/4)^m`. -/
theorem swing_transient_brackets [SFinite μ] (hX : ∀ j, Measurable (X j))
    (hi : iIndepFun X μ) (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) :
    ∃ ν : ProbabilityMeasure ℝ,
      (swingMarginKernel X μ).Invariant (ν : Measure ℝ) ∧
      (∀ ν' : Measure ℝ, IsProbabilityMeasure ν' →
        (swingMarginKernel X μ).Invariant ν' → ν' = (ν : Measure ℝ)) ∧
      let α₂ := slopeStationaryLaw X μ (entranceLaw X μ)
      let c := slopeIterateCoefficient X μ α₂
      let γ := stationaryLeadingCoefficient X μ (ν : Measure ℝ)
      (∀ m, Tendsto (fun E => transientNormalizedMean X μ E (m + 2)) atTop (𝓝 (c m))) ∧
      (∀ m, c (2 * m + 2) ≤ c (2 * m)) ∧ (∀ m, c (2 * m + 1) ≤ c (2 * m + 3)) ∧
      Tendsto c atTop (𝓝 γ) ∧ (∀ m, γ ≤ c (2 * m)) ∧ (∀ m, c (2 * m + 1) ≤ γ) ∧
      ∀ m, |c m - γ| ≤ slopeRewardLipschitz *
        (wassersteinOne α₂ (slopeStationaryLaw X μ (ν : Measure ℝ))).toReal * (3 / 4 : ℝ) ^ m := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  set budget : ℝ → ℝ := fun E => max E stationaryScaleThreshold with hbdef
  have hbudget : ∀ E, stationaryScaleThreshold ≤ budget E := fun E => le_max_right _ _
  have hbudget_top : Tendsto budget atTop atTop :=
    tendsto_atTop_mono (fun E => le_max_left E _) tendsto_id
  obtain ⟨ν, hinv, huniq, _, _, hweak, -, -, -, -, -⟩ :=
    theorem_4_3_swing_gaussian hX hi hG hbudget hbudget_top
  have hmom : Integrable (fun b : ℝ => b) (slopeStationaryLaw X μ (ν : Measure ℝ)) :=
    slopeStationaryLaw_first_moment_of_weak_limit hX hi hG hbudget hweak
  set ρ : ProbabilityMeasure ℝ := ⟨entranceLaw X μ, entranceLaw_isProbabilityMeasure hX hi hG⟩
  exact ⟨ν, hinv, huniq, transient_coefficient_brackets_of_marginLimit hX hi hG (ρ := ρ)
    (nativeTransientMarginProb_tendsto_entranceLaw hX hi hG) (slopeTestLE_zero_entranceLaw hX hi hG)
    hinv hmom⟩

end

end SwingRepair
