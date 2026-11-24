import PLAStochastic.Swing.Repair.SpanLifetimeGeometry
import PLAStochastic.Affine.Sampled.MeanConvergence
import PLAStochastic.Brownian.PathLaw.MeshIncrements

/-!
# Actual Gaussian repair spans and Brownian sampled lifetimes

The full increment-sequence law is derived from iid Gaussian increments. The
span functional is the existing firstRepairSpan, and its agreement with the
sampled lifetime uses the actual prefix cones and the original extended first
rejection. No iid cycle, coupling, or uniform-integrability assertion is assumed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Filter
open scoped NNReal ENNReal Topology BigOperators

namespace SwingRepair

theorem cumulativeSamples_normalizedMesh {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (h : ℝ≥0)
    (ω : Ω) (hc : Continuous (B · ω)) (hz : B 0 ω = 0) (n : ℕ) :
    cumulativeSamples (normalizedMeshIncrement B h) n ω =
      processPath B ω ((n : ℝ) * h) / Real.sqrt (h : ℝ) := by
  unfold cumulativeSamples
  rw [sum_normalizedMeshIncrement, hz, sub_zero]
  congr 1
  simpa only [NNReal.coe_mul, NNReal.coe_natCast] using
    (processPath_apply_of_continuous hc ((n : ℝ≥0) * h)).symm

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The actual normalized Brownian increments yield the sampled lifetime pathwise a.e. -/
theorem normalizedMesh_span_eq_lifetime_ae (hB : IsBrownianReal B μ)
    {h : ℝ≥0} (hh : h ≠ 0) (hh₁ : h ≤ 1) {ε : ℝ} (hε : 0 ≤ ε) :
    (fun ω => (h : ℝ) * (firstRepairSpan (normalizedMeshIncrement B h)
      (2 * ε / Real.sqrt (h : ℝ)) ω : ℝ)) =ᵐ[μ]
      (fun ω => (finiteMeshProcessLifetime B h ε ω).toReal) := by
  have hp : 0 < (h : ℝ) := by exact_mod_cast (pos_of_ne_zero hh)
  have hc : 0 < Real.sqrt (h : ℝ) := Real.sqrt_pos.mpr hp
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero,
    finiteMeshProcessLifetime_ae_ne_top hB hh hh₁ ε] with ω hω hz hfinite
  have hf : processPath B ω 0 = 0 := (processPath_apply_of_continuous hω 0).trans hz
  have hsamples := cumulativeSamples_normalizedMesh B h ω hω hz
  have hr := firstRepairReject_ne_top_of_meshLifetime_ne_top
    (normalizedMeshIncrement B h) ω (processPath B ω) hf h hh hc hε hsamples hfinite
  have heq := finiteMeshLifetime_eq_mul_firstRepairSpan
    (normalizedMeshIncrement B h) ω (processPath B ω) hf h hh hc hε hsamples hr
  simpa only [finiteMeshProcessLifetime, ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_natCast] using
    (congrArg ENNReal.toReal heq).symm

/-- The actual Gaussian rejection span, after time rescaling, has the actual sampled lifetime law.
The original Gaussian sequence and the Brownian motion may live on different spaces. -/
theorem firstRepairSpan_identDistrib_mesh {Ξ : Type*} [MeasurableSpace Ξ] {ν : Measure Ξ}
    {X : ℕ → Ξ → ℝ} (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X ν)
    (hG : ∀ n, ν.map (X n) = gaussianReal 0 1) (hB : IsBrownianReal B μ)
    {h : ℝ≥0} (hh : h ≠ 0) (hh₁ : h ≤ 1) {ε : ℝ} (hε : 0 ≤ ε) :
    IdentDistrib (fun ξ => (h : ℝ) *
      (firstRepairSpan X (2 * ε / Real.sqrt (h : ℝ)) ξ : ℝ))
      (fun ω => (finiteMeshProcessLifetime B h ε ω).toReal) ν μ := by
  have hseq := identDistrib_gaussian_mesh_sequence (fun n => (hX n).aemeasurable)
    hi hG hB.toIsPreBrownianReal h hh
  have hm : Measurable (fun x : ℕ → ℝ => (h : ℝ) *
      (repairSequenceSpan (2 * ε / Real.sqrt (h : ℝ)) x : ℝ)) :=
    measurable_const.mul ((measurable_from_nat : Measurable (fun n : ℕ => (n : ℝ))).comp
      (repairSequenceSpan_measurable _))
  have hs : IdentDistrib (fun ξ => (h : ℝ) *
      (firstRepairSpan X (2 * ε / Real.sqrt (h : ℝ)) ξ : ℝ))
      (fun ω => (h : ℝ) * (firstRepairSpan (normalizedMeshIncrement B h)
        (2 * ε / Real.sqrt (h : ℝ)) ω : ℝ)) ν μ := by
    simpa only [Function.comp_def, repairSequenceSpan_sequence] using hseq.comp hm
  exact hs.trans (IdentDistrib.of_ae_eq hs.aemeasurable_snd
    (normalizedMesh_span_eq_lifetime_ae hB hh hh₁ hε))

/-- The actual Gaussian span means converge along any positive vanishing mesh family.
The tolerance 2ε/√h is the repair's final budget, not its internal half budget. -/
theorem firstRepairSpan_mesh_mean_convergence {Ξ : Type*} [MeasurableSpace Ξ] {ν : Measure Ξ}
    {X : ℕ → Ξ → ℝ} (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X ν)
    (hG : ∀ n, ν.map (X n) = gaussianReal 0 1) (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 < ε) {h : ℕ → ℝ≥0}
    (hh : ∀ n, h n ≠ 0) (hh₁ : ∀ n, h n ≤ 1)
    (hconv : Tendsto (fun n => (h n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ξ, (h n : ℝ) *
      (firstRepairSpan X (2 * ε / Real.sqrt (h n : ℝ)) ξ : ℝ) ∂ν) atTop
      (𝓝 (∫ ω, (anchoredProcessLifetime B ε ω).toReal ∂μ)) := by
  have heq (n : ℕ) := (firstRepairSpan_identDistrib_mesh hX hi hG hB (hh n) (hh₁ n) hε.le).integral_eq
  simp_rw [heq]
  exact (finiteMeshProcessLifetime_mean_convergence hB hε hh hh₁ hconv).2

/-- The exact Brownian mesh corresponding to a final Gaussian repair budget E. -/
def gaussianBudgetMesh (E : ℝ≥0) : ℝ≥0 := E⁻¹ ^ 2

theorem gaussianBudgetMesh_ne_zero {E : ℝ≥0} (hE : 1 ≤ E) : gaussianBudgetMesh E ≠ 0 := by
  apply pow_ne_zero
  exact inv_ne_zero (ne_of_gt (lt_of_lt_of_le (by norm_num) hE))

theorem gaussianBudgetMesh_le_one {E : ℝ≥0} (hE : 1 ≤ E) : gaussianBudgetMesh E ≤ 1 := by
  have hEr : (1 : ℝ) ≤ E := by exact_mod_cast hE
  have hi : (E : ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_iff_one_le_mul₀ (show 0 < (E : ℝ) by linarith)]
    simpa only [one_mul] using hEr
  change ((E : ℝ)⁻¹) ^ 2 ≤ 1
  have hn := inv_nonneg.mpr E.coe_nonneg
  nlinarith

theorem sqrt_gaussianBudgetMesh (E : ℝ≥0) : Real.sqrt (gaussianBudgetMesh E : ℝ) = (E : ℝ)⁻¹ := by
  change Real.sqrt (((E : ℝ)⁻¹) ^ 2) = (E : ℝ)⁻¹
  exact Real.sqrt_sq (inv_nonneg.mpr E.coe_nonneg)

theorem gaussianBudgetMesh_budget (E : ℝ≥0) :
    2 * (1 / 2 : ℝ) / Real.sqrt (gaussianBudgetMesh E : ℝ) = E := by
  rw [sqrt_gaussianBudgetMesh]
  norm_num [div_inv_eq_mul]

theorem gaussianBudgetMesh_tendsto {ι : Type*} {l : Filter ι} {E : ι → ℝ≥0}
    (hE : Tendsto (fun i => (E i : ℝ)) l atTop) :
    Tendsto (fun i => (gaussianBudgetMesh (E i) : ℝ)) l (𝓝 0) := by
  have hi := (tendsto_inv_atTop_zero.comp hE).pow 2
  simpa only [gaussianBudgetMesh, NNReal.coe_pow, NNReal.coe_inv, Function.comp_def, zero_pow (by omega : 2 ≠ 0)] using hi

/-- Exact large-budget law: K_E / E² is the sampled Brownian half-tolerance lifetime. -/
theorem firstRepairSpan_largeBudget_identDistrib {Ξ : Type*} [MeasurableSpace Ξ] {ν : Measure Ξ}
    {X : ℕ → Ξ → ℝ} (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X ν)
    (hG : ∀ n, ν.map (X n) = gaussianReal 0 1) (hB : IsBrownianReal B μ)
    {E : ℝ≥0} (hE : 1 ≤ E) :
    IdentDistrib (fun ξ => (firstRepairSpan X E ξ : ℝ) / (E : ℝ) ^ 2)
      (fun ω => (finiteMeshProcessLifetime B (gaussianBudgetMesh E) (1 / 2) ω).toReal) ν μ := by
  have hs := firstRepairSpan_identDistrib_mesh hX hi hG hB
    (gaussianBudgetMesh_ne_zero hE) (gaussianBudgetMesh_le_one hE) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [gaussianBudgetMesh_budget] at hs
  have heq : (fun ξ => (gaussianBudgetMesh E : ℝ) * (firstRepairSpan X E ξ : ℝ)) =
      (fun ξ => (firstRepairSpan X E ξ : ℝ) / (E : ℝ) ^ 2) := by
    funext ξ
    change ((E : ℝ)⁻¹) ^ 2 * (firstRepairSpan X E ξ : ℝ) = _
    rw [div_eq_mul_inv, inv_pow, mul_comm]
  rw [heq] at hs
  exact hs

/-- Arbitrary diverging budget sequences have the true anchored half-tolerance mean limit. -/
theorem firstRepairSpan_largeBudget_mean_sequence {Ξ : Type*} [MeasurableSpace Ξ] {ν : Measure Ξ}
    {X : ℕ → Ξ → ℝ} (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X ν)
    (hG : ∀ n, ν.map (X n) = gaussianReal 0 1) (hB : IsBrownianReal B μ)
    {E : ℕ → ℝ≥0} (hE : ∀ n, 1 ≤ E n) (hconv : Tendsto (fun n => (E n : ℝ)) atTop atTop) :
    Tendsto (fun n => (∫ ξ, (firstRepairSpan X (E n) ξ : ℝ) ∂ν) / (E n : ℝ) ^ 2) atTop
      (𝓝 (∫ ω, (anchoredProcessLifetime B (1 / 2) ω).toReal ∂μ)) := by
  have heq (n : ℕ) := (firstRepairSpan_largeBudget_identDistrib hX hi hG hB (hE n)).integral_eq
  simp only [integral_div] at heq
  simp_rw [heq]
  exact (finiteMeshProcessLifetime_mean_convergence hB (by norm_num : (0 : ℝ) < 1 / 2)
    (fun n => gaussianBudgetMesh_ne_zero (hE n))
    (fun n => gaussianBudgetMesh_le_one (hE n)) (gaussianBudgetMesh_tendsto hconv)).2

/-- The full real-budget limit, with an explicit auxiliary Brownian motion.
This identifies the limit with the true lifetime mean; it does not evaluate that mean. -/
theorem firstRepairSpan_largeBudget_mean {Ξ : Type*} [MeasurableSpace Ξ] {ν : Measure Ξ}
    {X : ℕ → Ξ → ℝ} (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X ν)
    (hG : ∀ n, ν.map (X n) = gaussianReal 0 1) (hB : IsBrownianReal B μ) :
    Tendsto (fun E : ℝ => (∫ ξ, (firstRepairSpan X E ξ : ℝ) ∂ν) / E ^ 2) atTop
      (𝓝 (∫ ω, (anchoredProcessLifetime B (1 / 2) ω).toReal ∂μ)) := by
  apply Filter.tendsto_iff_seq_tendsto.mpr
  intro E hconv
  have hlarge : ∀ᶠ n in atTop, 1 ≤ E n := hconv.eventually_ge_atTop 1
  let F : ℕ → ℝ≥0 := fun n => ⟨max (E n) 1, le_trans zero_le_one (le_max_right _ _)⟩
  have hF : ∀ n, 1 ≤ F n := fun n => le_max_right (E n) 1
  have hFconv : Tendsto (fun n => (F n : ℝ)) atTop atTop := by
    apply hconv.congr'
    filter_upwards [hlarge] with n hn
    exact (max_eq_left hn).symm
  apply (firstRepairSpan_largeBudget_mean_sequence hX hi hG hB hF hFconv).congr'
  filter_upwards [hlarge] with n hn
  change (∫ ξ, (firstRepairSpan X (max (E n) 1) ξ : ℝ) ∂ν) / (max (E n) 1) ^ 2 = _
  simp only [max_eq_left hn, Function.comp_def]

/-- Brownian scaling identifies the half-budget mean as one quarter of the unit mean. -/
theorem anchoredHalfLifetime_mean (hB : IsBrownianReal B μ) :
    (∫ ω, (anchoredProcessLifetime B (1 / 2) ω).toReal ∂μ) =
      (∫ ω, anchoredUnitLifetime B ω ∂μ) / 4 := by
  have hi := (identDistrib_anchoredLifetime_toReal_tolerance hB
    (by norm_num : (0 : ℝ) < 1 / 2)).integral_eq
  rw [integral_const_mul] at hi
  rw [hi]
  ring

/-- The actual repair span mean satisfies E[K_E]/E² → κ_an/4.
Here κ_an is the integral of the actual unit-tolerance Brownian anchored lifetime. -/
theorem firstRepairSpan_largeBudget_mean_unit {Ξ : Type*} [MeasurableSpace Ξ] {ν : Measure Ξ}
    {X : ℕ → Ξ → ℝ} (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X ν)
    (hG : ∀ n, ν.map (X n) = gaussianReal 0 1) (hB : IsBrownianReal B μ) :
    Tendsto (fun E : ℝ => (∫ ξ, (firstRepairSpan X E ξ : ℝ) ∂ν) / E ^ 2) atTop
      (𝓝 ((∫ ω, anchoredUnitLifetime B ω ∂μ) / 4)) := by
  rw [← anchoredHalfLifetime_mean hB]
  exact firstRepairSpan_largeBudget_mean hX hi hG hB

/-- The fixed-budget regenerative mean per output segment has large-budget coefficient κ_an/8. -/
theorem repairMeanPerSegment_largeBudget {Ξ : Type*} [MeasurableSpace Ξ] {ν : Measure Ξ}
    {X : ℕ → Ξ → ℝ} (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X ν)
    (hG : ∀ n, ν.map (X n) = gaussianReal 0 1) (hB : IsBrownianReal B μ) :
    Tendsto (fun E : ℝ => ((∫ ξ, (firstRepairSpan X E ξ : ℝ) ∂ν) / 2) / E ^ 2) atTop
      (𝓝 ((∫ ω, anchoredUnitLifetime B ω ∂μ) / 8)) := by
  convert (firstRepairSpan_largeBudget_mean_unit hX hi hG hB).div_const 2 using 1
  · funext E
    ring
  · congr 1
    ring

end SwingRepair
