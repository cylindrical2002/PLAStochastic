import PLAStochastic.Affine.Process.IntervalExit.ContactRegularity
import PLAStochastic.Brownian.Killed.Positivity

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

 theorem integral_killedBrownianMeasure_eq_kernel (hB : IsBrownianReal B μ)
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Icc 0 r) {T : ℝ≥0} (hT : 0 < T) (g : ℝ → ℝ) :
    (∫ z, g z ∂killedBrownianMeasure B μ x r T) =
      ∫ z in Icc (0 : ℝ) r, dirichletHeatKernel r T x z*g z := by
  rw [killedBrownianMeasure_eq_heatDensity hB hr hx hT]
  have he := integral_withDensity_eq_integral_toReal_smul
    (μ := volume.restrict (Icc (0 : ℝ) r)) (g := g)
    (f := fun z => ENNReal.ofReal (dirichletHeatKernel r T x z))
    (continuous_heatKernel_right hr hT x).measurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))
  calc
    _ = ∫ z in Icc (0 : ℝ) r, (ENNReal.ofReal (dirichletHeatKernel r T x z)).toReal • g z := he
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
      simp only [ENNReal.toReal_ofReal (dirichletHeatKernel_nonneg hB hr hx hT hz), smul_eq_mul]
 theorem intervalSurvival_endpoint_ae (hB : IsBrownianReal B μ)
    {r x : ℝ} (hx : x ∈ Icc 0 r) (T : ℝ≥0) :
    ∀ᵐ ω ∂μ, boundedIntervalExit B x r T ω = T → x+B T ω ∈ Icc 0 r := by
  have hmem := killedBrownianMeasure_ae_mem hB hx T
  have hm : AEMeasurable (fun ω => x+B T ω) μ := (hB.aemeasurable T).const_add x
  change ∀ᵐ z ∂(μ.restrict {ω | boundedIntervalExit B x r T ω = T}).map (fun ω => x+B T ω), z ∈ Icc 0 r at hmem
  have hmem' := (ae_map_iff hm.restrict (p := fun z => z ∈ Icc 0 r) measurableSet_Icc).mp hmem
  exact (ae_restrict_iff'₀ (nullMeasurableSet_intervalSurvival hB x r T)).mp hmem'

/-- The actual killed semigroup recovers every continuous function at each interior point
as positive reciprocal time steps tend to zero. -/
theorem tendsto_integral_heatKernel_reciprocalMesh (hB : IsBrownianReal B μ)
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) {g : ℝ → ℝ} (hg : Continuous g) :
    Tendsto (fun n => ∫ z in Icc (0 : ℝ) r, dirichletHeatKernel r (reciprocalMesh n) x z*g z)
      atTop (𝓝 (g x)) := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  let S : ℕ → Set Ω := fun n => {ω | boundedIntervalExit B x r (reciprocalMesh n) ω = reciprocalMesh n}
  let F : ℕ → Ω → ℝ := fun n => (S n).indicator (fun ω => g (x+B (reciprocalMesh n) ω))
  have hm (n : ℕ) : AEStronglyMeasurable (F n) μ :=
    ((hg.measurable.comp_aemeasurable ((hB.aemeasurable (reciprocalMesh n)).const_add x)).aestronglyMeasurable).indicator₀
      (nullMeasurableSet_intervalSurvival hB x r (reciprocalMesh n))
  obtain ⟨M,hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := r)).bddAbove_image hg.norm.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg (g x)).trans (hM ⟨x,⟨hx.1.le,hx.2.le⟩,rfl⟩)
  have hbound (n : ℕ) : ∀ᵐ ω ∂μ, ‖F n ω‖ ≤ M := by
    filter_upwards [intervalSurvival_endpoint_ae hB ⟨hx.1.le,hx.2.le⟩ (reciprocalMesh n)] with ω hω
    by_cases hs : ω ∈ S n
    · change ‖(S n).indicator (fun ω => g (x+B (reciprocalMesh n) ω)) ω‖ ≤ M
      rw [indicator_of_mem hs]
      exact hM ⟨x+B (reciprocalMesh n) ω,hω hs,rfl⟩
    · change ‖(S n).indicator (fun ω => g (x+B (reciprocalMesh n) ω)) ω‖ ≤ M
      rw [indicator_of_notMem hs, norm_zero]
      exact hM0
  have ht : ∀ᵐ ω ∂μ, Tendsto (fun n => F n ω) atTop (𝓝 (g x)) := by
    filter_upwards [hB.cont,hB.eval_zero_ae_eq_zero,
      boundedIntervalExit_eq_min_touch_ae hB hr hx,intervalTouchTime_ae_pos hB hr hx,
      intervalTouchTime_ae_ne_top hB x r] with ω hc h0 he hp hf
    obtain ⟨σ,hσ⟩ := WithTop.ne_top_iff_exists.mp hf
    have hσ0 : 0 < σ := by
      rw [← hσ] at hp
      change (0 : WithTop ℝ≥0) < (σ : WithTop ℝ≥0) at hp
      exact WithTop.coe_lt_coe.mp hp
    have hu : (intervalTouchTime B x r ω).untopD 0 = σ := by rw [← hσ]; rfl
    have hsurv : ∀ᶠ n in atTop, ω ∈ S n := by
      filter_upwards [reciprocalMesh_tendsto_zero.eventually (gt_mem_nhds hσ0)] with n hn
      change boundedIntervalExit B x r (reciprocalMesh n) ω = reciprocalMesh n
      rw [he, hu, min_eq_right hn.le]
    have hpath : Tendsto (fun n => g (x+B (reciprocalMesh n) ω)) atTop (𝓝 (g x)) := by
      have h := hg.continuousAt.tendsto.comp ((hc.continuousAt.tendsto.comp reciprocalMesh_tendsto_zero).const_add x)
      simpa only [h0, add_zero, Function.comp_def] using h
    apply hpath.congr'
    filter_upwards [hsurv] with n hn
    exact (indicator_of_mem hn (fun ω => g (x+B (reciprocalMesh n) ω))).symm
  have hlim := tendsto_integral_of_dominated_convergence (fun _ : Ω => M) hm (integrable_const M) hbound ht
  have heq (n : ℕ) : (∫ ω, F n ω ∂μ) =
      ∫ z in Icc (0 : ℝ) r, dirichletHeatKernel r (reciprocalMesh n) x z*g z := by
    rw [← integral_killedBrownianMeasure_eq_kernel hB hr ⟨hx.1.le,hx.2.le⟩ (reciprocalMesh_pos n)]
    unfold killedBrownianMeasure
    rw [integral_map ((hB.aemeasurable (reciprocalMesh n)).const_add x).restrict hg.aestronglyMeasurable,
      ← integral_indicator₀ (nullMeasurableSet_intervalSurvival hB x r (reciprocalMesh n))]
  simpa only [heq, integral_const, probReal_univ, one_smul] using hlim

end BrownianAffine
