import PLAStochastic.Swing.FirstSegment.Recording
import PLAStochastic.Swing.Repair.SpanWeakLimit

/-!
# Gaussian mean and weak limits of the actual first native recording

The random duration below is defined from nativeStream output in
NativeFirstRecording, not from a surrogate stopping variable. Its exact
connection to firstRepairSpan provides measurability and the Brownian law.
An auxiliary continuous Brownian motion is explicit. The final constant here
is the true unit anchored lifetime integral, with no zeta evaluation asserted.
-/

noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Filter
open scoped NNReal ENNReal Topology
namespace SwingRepair

variable {Ξ : Type*} [MeasurableSpace Ξ] {ν : Measure Ξ}
variable {X : ℕ → Ξ → ℝ}

/-- The actual recording duration is measurable for every nonnegative budget. -/
theorem nativeFirstDuration_measurable (hX : ∀ n, Measurable (X n)) {E : ℝ} (hE : 0 ≤ E) :
    Measurable (nativeFirstDuration X E) := by
  have heq : nativeFirstDuration X E = fun ξ => firstRepairSpan X (2 * E) ξ - 1 :=
    funext (nativeFirstDuration_eq_span_sub_one X E hE)
  rw [heq]
  exact (measurable_from_nat : Measurable (fun n : ℕ => n - 1)).comp
    (firstRepairSpan_measurable hX (2 * E))

omit [MeasurableSpace Ξ] in
theorem nativeFirstDuration_cast_eq (X : ℕ → Ξ → ℝ) {E : ℝ} (hE : 0 ≤ E) (ξ : Ξ) :
    (nativeFirstDuration X E ξ : ℝ) = (firstRepairSpan X (2 * E) ξ : ℝ) - 1 := by
  rw [nativeFirstDuration_eq_span_sub_one X E hE ξ, Nat.cast_sub (show
    1 ≤ firstRepairSpan X (2 * E) ξ by unfold firstRepairSpan; omega), Nat.cast_one]

variable [IsProbabilityMeasure ν]

theorem nativeFirstDuration_integrable_gaussian (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X ν) (hG : ∀ n, ν.map (X n) = gaussianReal 0 1)
    {E : ℝ} (hE : 0 ≤ E) : Integrable (fun ξ => (nativeFirstDuration X E ξ : ℝ)) ν := by
  have hI := (firstRepairSpan_integrable_gaussian hX hi hG (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hE)).sub
    (integrable_const (1 : ℝ))
  exact hI.congr (Eventually.of_forall fun ξ => (nativeFirstDuration_cast_eq X hE ξ).symm)

theorem nativeFirstDuration_integral_eq (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X ν) (hG : ∀ n, ν.map (X n) = gaussianReal 0 1)
    {E : ℝ} (hE : 0 ≤ E) :
    (∫ ξ, (nativeFirstDuration X E ξ : ℝ) ∂ν) =
      (∫ ξ, (firstRepairSpan X (2 * E) ξ : ℝ) ∂ν) - 1 := by
  calc
    _ = ∫ ξ, ((firstRepairSpan X (2 * E) ξ : ℝ) - 1) ∂ν :=
      integral_congr_ae (Eventually.of_forall (nativeFirstDuration_cast_eq X hE))
    _ = _ := by
      rw [integral_sub (firstRepairSpan_integrable_gaussian hX hi hG
        (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hE)) (integrable_const (1 : ℝ))]
      simp

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The complete real-budget mean limit for the true first native recording. -/
theorem nativeFirstDuration_largeBudget_mean (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X ν) (hG : ∀ n, ν.map (X n) = gaussianReal 0 1)
    (hB : IsBrownianReal B μ) :
    Tendsto (fun E : ℝ => (∫ ξ, (nativeFirstDuration X E ξ : ℝ) ∂ν) / E ^ 2) atTop
      (𝓝 (∫ ω, anchoredUnitLifetime B ω ∂μ)) := by
  have htw : Tendsto (fun E : ℝ => 2 * E) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) tendsto_id
  have hK := (firstRepairSpan_largeBudget_mean_unit hX hi hG hB).comp htw
  have hscaled : Tendsto (fun E : ℝ =>
      4 * ((∫ ξ, (firstRepairSpan X (2 * E) ξ : ℝ) ∂ν) / (2 * E) ^ 2)) atTop
      (𝓝 (∫ ω, anchoredUnitLifetime B ω ∂μ)) := by
    convert hK.const_mul 4 using 1
    · rfl
    · congr 1
      ring
  have hsmall : Tendsto (fun E : ℝ => 1 / E ^ 2) atTop (𝓝 0) := by
    simpa only [one_div, inv_pow, zero_pow (by omega : 2 ≠ 0)] using
      (tendsto_inv_atTop_zero : Tendsto (fun E : ℝ => E⁻¹) atTop (𝓝 0)).pow 2
  have hlim := hscaled.sub hsmall
  simp only [sub_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with E hE
  rw [nativeFirstDuration_integral_eq hX hi hG (by linarith : 0 ≤ E)]
  field_simp
  ring

omit [IsProbabilityMeasure ν] in
/-- Exact law of the first actual native duration under Brownian mesh scaling. -/
theorem nativeFirstDuration_identDistrib_mesh (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X ν) (hG : ∀ n, ν.map (X n) = gaussianReal 0 1)
    (hB : IsBrownianReal B μ) {h : ℝ≥0} (hh : h ≠ 0) (hh₁ : h ≤ 1) :
    IdentDistrib (fun ξ => (h : ℝ) *
      (nativeFirstDuration X (1 / Real.sqrt (h : ℝ)) ξ : ℝ))
      (fun ω => (finiteMeshProcessLifetime B h 1 ω).toReal - (h : ℝ)) ν μ := by
  have hE : 0 ≤ 1 / Real.sqrt (h : ℝ) := div_nonneg zero_le_one (Real.sqrt_nonneg _)
  have hbase := (firstRepairSpan_identDistrib_mesh hX hi hG hB hh hh₁
    (by norm_num : (0 : ℝ) ≤ 1)).comp (measurable_id.sub_const (h : ℝ))
  have hb : 2 * (1 : ℝ) / Real.sqrt (h : ℝ) = 2 * (1 / Real.sqrt (h : ℝ)) := by ring
  simp only [Function.comp_def, id_eq, hb] at hbase
  convert hbase using 1
  funext ξ
  rw [nativeFirstDuration_cast_eq X hE]
  ring

omit [IsProbabilityMeasure ν] in
/-- The one-sample difference appears explicitly in the exact large-budget law. -/
theorem nativeFirstDuration_largeBudget_identDistrib (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X ν) (hG : ∀ n, ν.map (X n) = gaussianReal 0 1)
    (hB : IsBrownianReal B μ) {E : ℝ≥0} (hE : 1 ≤ E) :
    IdentDistrib (fun ξ => (nativeFirstDuration X E ξ : ℝ) / (E : ℝ) ^ 2)
      (fun ω => (finiteMeshProcessLifetime B (gaussianBudgetMesh E) 1 ω).toReal -
        (gaussianBudgetMesh E : ℝ)) ν μ := by
  have hbase := nativeFirstDuration_identDistrib_mesh hX hi hG hB
    (gaussianBudgetMesh_ne_zero hE) (gaussianBudgetMesh_le_one hE)
  have hb : 1 / Real.sqrt (gaussianBudgetMesh E : ℝ) = E := by
    rw [sqrt_gaussianBudgetMesh]
    simp
  rw [hb] at hbase
  convert hbase using 1
  funext ξ
  change (nativeFirstDuration X E ξ : ℝ) / (E : ℝ) ^ 2 =
    ((E : ℝ)⁻¹) ^ 2 * (nativeFirstDuration X E ξ : ℝ)
  rw [div_eq_mul_inv, inv_pow, mul_comm]

/-- The weak limit for the actual native duration, over all nonnegative budgets tending to infinity. -/
theorem nativeFirstDuration_largeBudget_tendstoInDistribution [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X ν)
    (hG : ∀ n, ν.map (X n) = gaussianReal 0 1) (hB : IsBrownianReal B μ) :
    TendstoInDistribution (fun E : ℝ≥0 => fun ξ =>
      (nativeFirstDuration X E ξ : ℝ) / (E : ℝ) ^ 2) atTop
      (anchoredUnitLifetime B) (fun _ => ν) μ := by
  let F : ℝ≥0 → ℝ≥0 := fun E => max E 1
  have hF : ∀ E, 1 ≤ F E := fun E => le_max_right E 1
  have hFconv : Tendsto (fun E => (F E : ℝ)) atTop atTop := by
    apply (NNReal.tendsto_coe_atTop.mpr tendsto_id).congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ≥0)] with E hE
    simp only [F, max_eq_left hE, id_eq]
  have hmesh := gaussianBudgetMesh_tendsto hFconv
  have hmeas (E : ℝ≥0) : AEMeasurable
      (fun ω => (finiteMeshProcessLifetime B (gaussianBudgetMesh (F E)) 1 ω).toReal -
        (gaussianBudgetMesh (F E) : ℝ)) μ :=
    (aemeasurable_finiteMeshProcessLifetime hB _
      (gaussianBudgetMesh_ne_zero (hF E)) 1).ennreal_toReal.sub_const _
  have hD : TendstoInDistribution
      (fun E : ℝ≥0 => fun ω =>
        (finiteMeshProcessLifetime B (gaussianBudgetMesh (F E)) 1 ω).toReal -
          (gaussianBudgetMesh (F E) : ℝ)) atTop (anchoredUnitLifetime B) (fun _ => μ) μ := by
    apply tendstoInDistribution_of_ae_tendsto hmeas
      (aemeasurable_anchoredProcessLifetime hB 1).ennreal_toReal
    filter_upwards [anchoredProcessLifetime_tolerance_ae_ne_top hB zero_lt_one] with ω hω
    have ht := (ENNReal.continuousAt_toReal hω).tendsto.comp
      (finiteMeshProcessLifetime_tendsto 1 (fun E => gaussianBudgetMesh_ne_zero (hF E)) hmesh ω)
    simpa only [sub_zero, anchoredUnitLifetime, Function.comp_def] using ht.sub hmesh
  refine ⟨fun E => ?_, hD.aemeasurable_limit, ?_⟩
  · exact ((measurable_from_nat : Measurable (fun n : ℕ => (n : ℝ))).comp
      (nativeFirstDuration_measurable hX E.coe_nonneg)).aemeasurable.div_const _
  · apply hD.tendsto.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ≥0)] with E hE
    apply Subtype.ext
    have hlaw := (nativeFirstDuration_largeBudget_identDistrib hX hi hG hB (hF E)).map_eq
    simpa only [F, max_eq_left hE] using hlaw.symm

end SwingRepair
