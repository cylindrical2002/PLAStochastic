import PLAStochastic.Swing.DenseSampling.Rejection.LongOutputCover

/-! # The two localization errors vanish for the original Brownian paths -/
noncomputable section
open Classical
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

def nativeRejectionStateFailure (y : ℕ → ℝ) (γ : ℝ) (h : ℝ≥0) (n : ℕ) : ℝ :=
  if ∀ b ≤ n, nativeRejectionAt (fun j => (j : ℝ)*(h : ℝ)) y 1 b →
    nativeRejectionState (fun j => (j : ℝ)*(h : ℝ)) y 1 b ≤ 2*γ then 0 else 1

theorem nativeRejectionStateFailure_bounds (y : ℕ → ℝ) (γ : ℝ) (h : ℝ≥0) (n : ℕ) :
    0 ≤ nativeRejectionStateFailure y γ h n ∧ nativeRejectionStateFailure y γ h n ≤ 1 := by
  unfold nativeRejectionStateFailure
  split_ifs <;> norm_num

theorem measurable_nativeRejectionStateFailure (γ : ℝ) {h : ℝ≥0} (hh : 0 < h) (n : ℕ) :
    Measurable (fun y : ℕ → ℝ => nativeRejectionStateFailure y γ h n) := by
  have ht := strictMono_mesh_times (show (0 : ℝ) < h by exact_mod_cast hh)
  have hm : MeasurableSet {y : ℕ → ℝ | ∀ b ≤ n, nativeRejectionAt (fun j => (j : ℝ)*(h : ℝ)) y 1 b →
      nativeRejectionState (fun j => (j : ℝ)*(h : ℝ)) y 1 b ≤ 2*γ} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro b
    apply MeasurableSet.iInter
    intro _
    convert (measurableSet_nativeRejectionAt _ ht 1 b).compl.union
      (measurableSet_le (measurable_nativeRejectionState _ ht 1 b) (measurable_const (a := 2*γ))) using 1
    ext y
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq]
    tauto
  exact measurable_const.ite hm measurable_const

/-- Almost every original Brownian path puts every actual recording in the
chosen boundary layer, eventually in the mesh and uniformly over the horizon. -/
theorem ae_eventually_nativeRejectionStateFailure_zero {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    {T γ : ℝ} (hT : 0 ≤ T) (hγ : 0 < γ) {l : Filter ι} {h : ι → ℝ≥0}
    (hh : ∀ i, 0 < h i) (hconv : Tendsto (fun i => (h i : ℝ)) l (𝓝 0))
    {n : ι → ℕ} (hnT : ∀ i, (n i : ℝ)*(h i : ℝ) ≤ T) :
    ∀ᵐ ω ∂μ, ∀ᶠ i in l,
      nativeRejectionStateFailure (fun j => B ((j : ℝ≥0)*h i) ω) γ (h i) (n i) = 0 := by
  filter_upwards [hB.cont] with ω hc
  obtain ⟨δ, hδ, hs⟩ := exists_uniform_nativeRejectionState (processPath B ω) hT
    (by norm_num : (0 : ℝ) < 1) hγ
  filter_upwards [hconv.eventually (gt_mem_nhds hδ)] with i hi
  have hy : (fun j : ℕ => B ((j : ℝ≥0)*h i) ω) =
      (fun j : ℕ => processPath B ω ((j : ℝ)*(h i : ℝ))) := by
    funext j
    simpa only [NNReal.coe_mul, NNReal.coe_natCast] using!
      (processPath_apply_of_continuous hc ((j : ℝ≥0)*h i)).symm
  rw [hy]
  unfold nativeRejectionStateFailure
  rw [if_pos]
  intro b hb hr
  exact (hs (h i) (by exact_mod_cast hh i) hi b
    ((mul_le_mul_of_nonneg_right (by exact_mod_cast hb) (h i).coe_nonneg).trans (hnT i)) hr).le

/-- The probability cost of failing the boundary layer tends to zero; this is
proved independently of any maximum-duration convergence statement. -/
theorem integral_nativeRejectionStateFailure_tendsto_zero {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    {T γ : ℝ} (hT : 0 ≤ T) (hγ : 0 < γ) {l : Filter ι} [l.IsCountablyGenerated]
    {h : ι → ℝ≥0} (hh : ∀ i, 0 < h i) (hconv : Tendsto (fun i => (h i : ℝ)) l (𝓝 0))
    {n : ι → ℕ} (hnT : ∀ i, (n i : ℝ)*(h i : ℝ) ≤ T) :
    Tendsto (fun i => ∫ ω, nativeRejectionStateFailure
      (fun j => B ((j : ℝ≥0)*h i) ω) γ (h i) (n i) ∂μ) l (𝓝 0) := by
  let : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hm (i : ι) := ((measurable_nativeRejectionStateFailure γ (hh i) (n i)).comp_aemeasurable
    (aemeasurable_pi_lambda _ (fun j : ℕ => hB.aemeasurable ((j : ℝ≥0)*h i)))).aestronglyMeasurable
  have hb (i : ι) : ∀ᵐ ω ∂μ, ‖nativeRejectionStateFailure
      (fun j => B ((j : ℝ≥0)*h i) ω) γ (h i) (n i)‖ ≤ 1 := by
    apply ae_of_all
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (nativeRejectionStateFailure_bounds _ _ _ _).1]
    exact (nativeRejectionStateFailure_bounds _ _ _ _).2
  have hl := ae_eventually_nativeRejectionStateFailure_zero hB hT hγ hh hconv hnT
  have hd := tendsto_integral_filter_of_dominated_convergence (fun _ : Ω => (1 : ℝ))
    (Eventually.of_forall hm) (Eventually.of_forall hb) (integrable_const 1)
    (hl.mono (fun _ hω => tendsto_const_nhds.congr' (hω.mono (fun _ he => he.symm))))
  simpa only [integral_zero, Function.comp_def] using hd

def brownianNativeHeightFailure {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (T K : ℝ) (ω : Ω) : ℝ :=
  if ‖intervalPath (processPath B ω) T‖ ≤ K then 0 else 1

theorem brownianNativeHeightFailure_bounds {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (T K : ℝ) (ω : Ω) :
    0 ≤ brownianNativeHeightFailure B T K ω ∧ brownianNativeHeightFailure B T K ω ≤ 1 := by
  unfold brownianNativeHeightFailure
  split_ifs <;> norm_num

theorem aemeasurable_brownianNativeHeightFailure {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ) (T K : ℝ) :
    AEMeasurable (brownianNativeHeightFailure B T K) μ := by
  have hz := ((ContinuousMap.continuous_restrict (Icc (0 : ℝ) T)).measurable.comp_aemeasurable
    (aemeasurable_processPath hB)).norm
  have hf : Measurable (fun z : ℝ => if z ≤ K then (0 : ℝ) else 1) :=
    measurable_const.ite (measurableSet_le measurable_id measurable_const) measurable_const
  exact hf.comp_aemeasurable hz

/-- Compact Brownian path heights can be localized at an arbitrarily small
probability cost, without requiring a separate maximum tail estimate. -/
theorem integral_brownianNativeHeightFailure_tendsto_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ) (T : ℝ) :
    Tendsto (fun K : ℕ => ∫ ω, brownianNativeHeightFailure B T K ω ∂μ) atTop (𝓝 0) := by
  let : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hd := tendsto_integral_of_dominated_convergence (fun _ : Ω => (1 : ℝ))
    (fun K => (aemeasurable_brownianNativeHeightFailure hB T K).aestronglyMeasurable)
    (integrable_const 1) (fun K => ae_of_all _ (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (brownianNativeHeightFailure_bounds B T K ω).1]
      exact (brownianNativeHeightFailure_bounds B T K ω).2))
    (ae_of_all μ (fun ω => show Tendsto (fun K : ℕ => brownianNativeHeightFailure B T K ω) atTop (𝓝 (0 : ℝ)) from by
      apply tendsto_const_nhds.congr'
      filter_upwards [((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually
        (eventually_ge_atTop ‖intervalPath (processPath B ω) T‖))] with K hK
      simp only [brownianNativeHeightFailure, if_pos hK]))
  simpa only [integral_zero, Function.comp_def] using hd

end SwingRepair
