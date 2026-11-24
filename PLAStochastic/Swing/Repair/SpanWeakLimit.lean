import PLAStochastic.Swing.Repair.SpanLifetimeLaw
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# Weak limits of actual Gaussian repair spans

An auxiliary Brownian motion is explicitly supplied, and may live on a different
probability space. Exact increment-sequence laws connect the actual repair span
to Brownian meshes. The weak limit follows from the proved pathwise mesh limit.
No Brownian existence theorem or explicit evaluation of its mean is asserted.
-/

noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Filter
open scoped NNReal ENNReal Topology

namespace SwingRepair

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {B : ℝ≥0 → Ω → ℝ}

/-- The actual sampled Brownian lifetimes converge in distribution on every positive mesh family. -/
theorem finiteMeshLifetime_tendstoInDistribution (hB : IsBrownianReal B μ)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {h : ι → ℝ≥0}
    (hh : ∀ i, h i ≠ 0) {ε : ℝ} (hε : 0 < ε)
    (hconv : Tendsto (fun i => (h i : ℝ)) l (𝓝 0)) :
    TendstoInDistribution (fun i ω => (finiteMeshProcessLifetime B (h i) ε ω).toReal) l
      (fun ω => (anchoredProcessLifetime B ε ω).toReal) (fun _ => μ) μ := by
  apply tendstoInDistribution_of_ae_tendsto
    (fun i => (aemeasurable_finiteMeshProcessLifetime hB (h i) (hh i) ε).ennreal_toReal)
    (aemeasurable_anchoredProcessLifetime hB ε).ennreal_toReal
  filter_upwards [anchoredProcessLifetime_tolerance_ae_ne_top hB hε] with ω hω
  exact (ENNReal.continuousAt_toReal hω).tendsto.comp
    (finiteMeshProcessLifetime_tendsto ε hh hconv ω)

/-- The full real-budget weak limit of the actual Gaussian repair span. -/
theorem firstRepairSpan_largeBudget_tendstoInDistribution
    {Ξ : Type*} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
    {X : ℕ → Ξ → ℝ} (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X ν)
    (hG : ∀ n, ν.map (X n) = gaussianReal 0 1) (hB : IsBrownianReal B μ) :
    TendstoInDistribution (fun E : ℝ => fun ξ => (firstRepairSpan X E ξ : ℝ) / E ^ 2)
      atTop (fun ω => (anchoredProcessLifetime B (1 / 2) ω).toReal) (fun _ => ν) μ := by
  let F : ℝ → ℝ≥0 := fun E => ⟨max E 1, le_trans zero_le_one (le_max_right _ _)⟩
  have hF : ∀ E, 1 ≤ F E := fun E => le_max_right E 1
  have hFconv : Tendsto (fun E => (F E : ℝ)) atTop atTop := by
    apply tendsto_id.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with E hE
    exact (max_eq_left hE).symm
  have hD := finiteMeshLifetime_tendstoInDistribution hB
    (fun E => gaussianBudgetMesh_ne_zero (hF E)) (by norm_num : (0 : ℝ) < 1 / 2)
    (gaussianBudgetMesh_tendsto hFconv)
  refine ⟨fun E => ?_, hD.aemeasurable_limit, ?_⟩
  · exact ((measurable_from_nat : Measurable (fun n : ℕ => (n : ℝ))).comp
      (firstRepairSpan_measurable hX E)).aemeasurable.div_const _
  · apply hD.tendsto.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with E hE
    apply Subtype.ext
    have hlaw := (firstRepairSpan_largeBudget_identDistrib hX hi hG hB (hF E)).map_eq
    change ν.map (fun ξ => (firstRepairSpan X (max E 1) ξ : ℝ) / (max E 1) ^ 2) = _ at hlaw
    simpa only [max_eq_left hE] using hlaw.symm

/-- Brownian scaling gives the paper's weak limit K_E/E² ⇒ τ_an/4. -/
theorem firstRepairSpan_largeBudget_tendstoInDistribution_unit
    {Ξ : Type*} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
    {X : ℕ → Ξ → ℝ} (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X ν)
    (hG : ∀ n, ν.map (X n) = gaussianReal 0 1) (hB : IsBrownianReal B μ) :
    TendstoInDistribution (fun E : ℝ => fun ξ => (firstRepairSpan X E ξ : ℝ) / E ^ 2)
      atTop (fun ω => anchoredUnitLifetime B ω / 4) (fun _ => ν) μ := by
  have hD := firstRepairSpan_largeBudget_tendstoInDistribution hX hi hG hB
  have hlaw : IdentDistrib (fun ω => (anchoredProcessLifetime B (1 / 2) ω).toReal)
      (fun ω => anchoredUnitLifetime B ω / 4) μ μ := by
    convert identDistrib_anchoredLifetime_toReal_tolerance hB
      (by norm_num : (0 : ℝ) < 1 / 2) using 1
    funext ω
    ring
  refine ⟨hD.forall_aemeasurable, hlaw.aemeasurable_snd, ?_⟩
  convert! hD.tendsto using 2
  congr 1
  exact Subtype.ext hlaw.map_eq.symm

end SwingRepair
