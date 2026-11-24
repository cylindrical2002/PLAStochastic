import PLAStochastic.Affine.Process.Markov.AugmentedFiltration
import PLAStochastic.Brownian.Markov.StrongMarkovAeFinite

/-!
# Strong Markov for the augmented natural filtration

The deterministic future is independent of an augmented event by replacing
that event with an almost surely equal raw natural-filtration event. The
countable stopping-time decomposition, ceiling-grid limit, and localization
then apply to the actual original continuous Brownian process.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace BrownianAffine.Augmented
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem measurableBrownianFuture_map_restrict_countable (hB : IsPreBrownianReal B μ)
    (I : Finset ℝ≥0) {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (augmentedBrownianFiltration hB) (fun ω => (τ ω : WithTop ℝ≥0)))
    (hcount : (Set.range τ).Countable) {A : Set Ω}
    (hA : MeasurableSet[hτ.measurableSpace] A) :
    (μ.restrict A).map (fun ω => measurableBrownianFuture hB I (τ ω) ω) =
      μ A • BrownianReal.projectiveFamily I := by
  have hτm : Measurable τ := by simpa using! hτ.measurable'.untopD 0
  have hm := measurable_countable_time_selection
    (measurable_measurableBrownianFuture hB I) hτm hcount
  apply Measure.ext
  intro D hD
  rw [Measure.map_apply hm hD, Measure.restrict_apply (hm hD), Measure.smul_apply,
    smul_eq_mul, Set.inter_comm]
  exact countableStoppedSelection_inter_measure (measurable_measurableBrownianFuture hB I)
    (fun t => indep_augmentedFiltration (measurableBrownianFuture_indep hB I t)) (measurableBrownianFuture_hasLaw hB I) hτ hcount hA hD

theorem brownianRestart_finite_aemeasurable (hB : IsBrownianReal B μ)
    (I : Finset ℝ≥0) {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (augmentedBrownianFiltration hB.toIsPreBrownianReal)
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    AEMeasurable (fun ω (t : I) => brownianRestart B τ t.1 ω) μ := by
  apply aemeasurable_of_tendsto_metrizable_ae atTop _
    (measurableBrownianFuture_grid_ae_tendsto hB I τ)
  intro n
  have hg := upperGridTime_isStoppingTime hτ n
  have hm : Measurable (fun ω => upperGridTime n (τ ω)) := by
    simpa using! hg.measurable'.untopD 0
  exact (measurable_countable_time_selection
    (measurable_measurableBrownianFuture hB.toIsPreBrownianReal I) hm
    (upperGridTime_countable_range τ n)).aemeasurable

/-- Conditional Brownian finite-dimensional law after an everywhere finite
stopping time. Boundedness is not needed because the tests are bounded. -/
theorem brownianRestart_map_restrict (hB : IsBrownianReal B μ)
    (I : Finset ℝ≥0) {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (augmentedBrownianFiltration hB.toIsPreBrownianReal)
      (fun ω => (τ ω : WithTop ℝ≥0))) {A : Set Ω}
    (hA : MeasurableSet[hτ.measurableSpace] A) :
    (μ.restrict A).map (fun ω (t : I) => brownianRestart B τ t.1 ω) =
      μ A • BrownianReal.projectiveFamily I := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have : IsFiniteMeasure (μ A • BrownianReal.projectiveFamily I) := by
    constructor
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    exact measure_lt_top μ A
  apply map_eq_of_ae_tendsto_constant_law (X := fun n ω =>
    measurableBrownianFuture hB.toIsPreBrownianReal I (upperGridTime n (τ ω)) ω)
  · intro n
    have hg := upperGridTime_isStoppingTime hτ n
    have hm : Measurable (fun ω => upperGridTime n (τ ω)) := by
      simpa using! hg.measurable'.untopD 0
    exact (measurable_countable_time_selection
      (measurable_measurableBrownianFuture hB.toIsPreBrownianReal I) hm
      (upperGridTime_countable_range τ n)).aemeasurable
  · exact ae_restrict_of_ae (measurableBrownianFuture_grid_ae_tendsto hB I τ)
  · intro n
    have hg := upperGridTime_isStoppingTime hτ n
    apply measurableBrownianFuture_map_restrict_countable hB.toIsPreBrownianReal I hg
      (upperGridTime_countable_range τ n)
    exact hτ.measurableSpace_mono hg
      (fun ω => WithTop.coe_le_coe.mpr (le_upperGridTime n (τ ω))) _ hA

theorem brownianRestart_hasLaw (hB : IsBrownianReal B μ) (I : Finset ℝ≥0) {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (augmentedBrownianFiltration hB.toIsPreBrownianReal)
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    HasLaw (fun ω (t : I) => brownianRestart B τ t.1 ω) (BrownianReal.projectiveFamily I) μ := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  exact ⟨brownianRestart_finite_aemeasurable hB I hτ,
    by simpa using brownianRestart_map_restrict hB I hτ MeasurableSet.univ⟩

/-- The actual original process restarted at the finite stopping time is Brownian. -/
theorem isBrownianReal_brownianRestart (hB : IsBrownianReal B μ) {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (augmentedBrownianFiltration hB.toIsPreBrownianReal)
      (fun ω => (τ ω : WithTop ℝ≥0))) : IsBrownianReal (brownianRestart B τ) μ where
  hasLaw I := brownianRestart_hasLaw hB I hτ
  cont := hB.cont.mono (fun _ hω => (hω.comp (continuous_const.add continuous_id)).sub continuous_const)

theorem brownianRestart_finite_indep_stopped (hB : IsBrownianReal B μ)
    (I : Finset ℝ≥0) {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (augmentedBrownianFiltration hB.toIsPreBrownianReal)
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    Indep (MeasurableSpace.comap (fun ω (t : I) => brownianRestart B τ t.1 ω) inferInstance)
      hτ.measurableSpace μ := by
  apply (Indep_iff _ _ μ).mpr
  intro C A hC hA
  obtain ⟨D, hD, rfl⟩ := hC
  have hm := brownianRestart_finite_aemeasurable hB I hτ
  have hmap := congrArg (fun ν : Measure (I → ℝ) => ν D) (brownianRestart_map_restrict hB I hτ hA)
  rw [Measure.map_apply_of_aemeasurable hm.restrict hD,
    Measure.restrict_apply' (hτ.measurableSpace_le _ hA), Measure.smul_apply, smul_eq_mul] at hmap
  have hval : μ ((fun ω (t : I) => brownianRestart B τ t.1 ω) ⁻¹' D) =
      BrownianReal.projectiveFamily I D := by
    rw [← (brownianRestart_hasLaw hB I hτ).map_eq, Measure.map_apply_of_aemeasurable hm hD]
  rw [hmap, hval, mul_comm]

/-- Strong Markov independence holds for the whole future process with its
coordinate sigma-algebra, not merely for one future increment. -/
theorem brownianRestart_indep_stopped (hB : IsBrownianReal B μ) {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (augmentedBrownianFiltration hB.toIsPreBrownianReal)
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    Indep (MeasurableSpace.comap (fun ω t => brownianRestart B τ t ω) inferInstance)
      hτ.measurableSpace μ := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hm : @Measurable Ω Ω mΩ hτ.measurableSpace id :=
    fun A hA => hτ.measurableSpace_le A hA
  have hi := @IndepFun.process_indepFun₀ ℝ≥0 Ω mΩ μ (fun _ => ℝ) Ω
    (fun _ => inferInstance) hτ.measurableSpace (brownianRestart B τ) id
    (fun t => (isBrownianReal_brownianRestart hB hτ).aemeasurable t)
    (show @AEMeasurable Ω Ω hτ.measurableSpace mΩ id μ from ⟨id, hm, EventuallyEq.rfl⟩)
    (fun I => show @IndepFun Ω (I → ℝ) Ω mΩ inferInstance hτ.measurableSpace
        (fun ω t => brownianRestart B τ t.1 ω) id μ from by
      change Indep _ (MeasurableSpace.comap id hτ.measurableSpace) μ
      simpa only [MeasurableSpace.comap_id] using brownianRestart_finite_indep_stopped hB I hτ)
    inferInstance
  change Indep _ (MeasurableSpace.comap id hτ.measurableSpace) μ at hi
  simpa only [MeasurableSpace.comap_id] using hi

theorem brownianRestartAt_finite_aemeasurable (hB : IsBrownianReal B μ)
    (I : Finset ℝ≥0) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (augmentedBrownianFiltration hB.toIsPreBrownianReal) τ)
    (hfinite : ∀ᵐ ω ∂μ, τ ω ≠ ⊤) :
    AEMeasurable (fun ω (t : I) => brownianRestartAt B τ t.1 ω) μ := by
  apply aemeasurable_of_tendsto_metrizable_ae atTop
    (fun n : ℕ => brownianRestart_finite_aemeasurable hB I
      (truncateBrownianStop_isStoppingTime hτ n))
  filter_upwards [hfinite] with ω hω
  apply tendsto_const_nhds.congr'
  filter_upwards [truncateBrownianStop_eventually_eq hω] with n hn
  funext t
  simp only [brownianRestartAt, brownianRestart, hn]

theorem brownianRestartAt_inter_measure_bounded (hB : IsBrownianReal B μ)
    (I : Finset ℝ≥0) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (augmentedBrownianFiltration hB.toIsPreBrownianReal) τ)
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) (H : ℝ≥0)
    {D : Set (I → ℝ)} (hD : MeasurableSet D) :
    μ ((fun ω (t : I) => brownianRestartAt B τ t.1 ω) ⁻¹' D ∩
      (A ∩ {ω | τ ω ≤ (H : WithTop ℝ≥0)})) =
      μ (A ∩ {ω | τ ω ≤ (H : WithTop ℝ≥0)}) * BrownianReal.projectiveFamily I D := by
  have hstop := truncateBrownianStop_isStoppingTime hτ H
  have hAs := stoppedEvent_truncate_measurable hτ H hA
  have hm := brownianRestart_finite_aemeasurable hB I hstop
  have hmap := congrArg (fun ν : Measure (I → ℝ) => ν D)
    (brownianRestart_map_restrict hB I hstop hAs)
  rw [Measure.map_apply_of_aemeasurable hm.restrict hD,
    Measure.restrict_apply' (hstop.measurableSpace_le _ hAs), Measure.smul_apply, smul_eq_mul] at hmap
  convert hmap using 1
  congr 1
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
  constructor <;> rintro ⟨hd, ha, hle⟩ <;> refine ⟨?_, ha, hle⟩
  · simpa only [brownianRestartAt, brownianRestart, truncateBrownianStop_eq_of_le τ H hle] using hd
  · simpa only [brownianRestartAt, brownianRestart, truncateBrownianStop_eq_of_le τ H hle] using hd

/-- Localization preserves the original stopped sigma-algebra. The increasing
events {τ ≤ n} cover almost every path, so no artificial finite stopping time is used. -/
theorem brownianRestartAt_inter_measure (hB : IsBrownianReal B μ)
    (I : Finset ℝ≥0) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (augmentedBrownianFiltration hB.toIsPreBrownianReal) τ)
    (hfinite : ∀ᵐ ω ∂μ, τ ω ≠ ⊤)
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A)
    {D : Set (I → ℝ)} (hD : MeasurableSet D) :
    μ ((fun ω (t : I) => brownianRestartAt B τ t.1 ω) ⁻¹' D ∩ A) =
      μ A * BrownianReal.projectiveFamily I D := by
  let C : ℕ → Set Ω := fun n => A ∩ {ω | τ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)}
  let V : Set Ω := (fun ω (t : I) => brownianRestartAt B τ t.1 ω) ⁻¹' D
  have hmono : Monotone C := by
    intro n m hnm ω hω
    refine ⟨hω.1, ?_⟩
    exact hω.2.trans (WithTop.coe_le_coe.mpr (Nat.cast_le.mpr hnm : (n : ℝ≥0) ≤ m))
  have hcover : ((⋃ n, C n) : Set Ω) =ᵐ[μ] A := ae_eq_iUnion_stopping_le hfinite A
  have hcoverV : ((⋃ n, V ∩ C n) : Set Ω) =ᵐ[μ] (V ∩ A : Set Ω) := by
    rw [← Set.inter_iUnion]
    exact ae_eq_set_inter EventuallyEq.rfl hcover
  calc
    μ (V ∩ A) = μ (⋃ n, V ∩ C n) := (measure_congr hcoverV).symm
    _ = ⨆ n, μ (V ∩ C n) := (monotone_const.inter hmono).measure_iUnion
    _ = ⨆ n : ℕ, μ (C n) * BrownianReal.projectiveFamily I D := by
      congr 1
      funext n
      exact brownianRestartAt_inter_measure_bounded hB I hτ hA n hD
    _ = (⨆ n, μ (C n)) * BrownianReal.projectiveFamily I D := (ENNReal.iSup_mul _ _).symm
    _ = μ A * BrownianReal.projectiveFamily I D := by
      rw [← hmono.measure_iUnion, measure_congr hcover]

theorem brownianRestartAt_hasLaw (hB : IsBrownianReal B μ) (I : Finset ℝ≥0)
    {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (augmentedBrownianFiltration hB.toIsPreBrownianReal) τ)
    (hfinite : ∀ᵐ ω ∂μ, τ ω ≠ ⊤) :
    HasLaw (fun ω (t : I) => brownianRestartAt B τ t.1 ω) (BrownianReal.projectiveFamily I) μ := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hm := brownianRestartAt_finite_aemeasurable hB I hτ hfinite
  refine ⟨hm, Measure.ext (fun D hD => ?_)⟩
  rw [Measure.map_apply_of_aemeasurable hm hD]
  simpa only [Set.inter_univ, measure_univ, one_mul] using
    brownianRestartAt_inter_measure hB I hτ hfinite MeasurableSet.univ hD

theorem isBrownianReal_brownianRestartAt (hB : IsBrownianReal B μ)
    {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (augmentedBrownianFiltration hB.toIsPreBrownianReal) τ)
    (hfinite : ∀ᵐ ω ∂μ, τ ω ≠ ⊤) : IsBrownianReal (brownianRestartAt B τ) μ where
  hasLaw I := brownianRestartAt_hasLaw hB I hτ hfinite
  cont := hB.cont.mono (fun _ hω => (hω.comp (continuous_const.add continuous_id)).sub continuous_const)

theorem brownianRestartAt_finite_indep_stopped (hB : IsBrownianReal B μ)
    (I : Finset ℝ≥0) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (augmentedBrownianFiltration hB.toIsPreBrownianReal) τ)
    (hfinite : ∀ᵐ ω ∂μ, τ ω ≠ ⊤) :
    Indep (MeasurableSpace.comap (fun ω (t : I) => brownianRestartAt B τ t.1 ω) inferInstance)
      hτ.measurableSpace μ := by
  apply (Indep_iff _ _ μ).mpr
  intro C A hC hA
  obtain ⟨D, hD, rfl⟩ := hC
  have hval : μ ((fun ω (t : I) => brownianRestartAt B τ t.1 ω) ⁻¹' D) =
      BrownianReal.projectiveFamily I D := by
    rw [← (brownianRestartAt_hasLaw hB I hτ hfinite).map_eq,
      Measure.map_apply_of_aemeasurable (brownianRestartAt_finite_aemeasurable hB I hτ hfinite) hD]
  rw [brownianRestartAt_inter_measure hB I hτ hfinite hA hD, hval, mul_comm]

/-- Strong Markov independence for the whole actual future and the original
extended stopping-time sigma-algebra, under almost-sure finiteness only. -/
theorem brownianRestartAt_indep_stopped (hB : IsBrownianReal B μ)
    {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (augmentedBrownianFiltration hB.toIsPreBrownianReal) τ)
    (hfinite : ∀ᵐ ω ∂μ, τ ω ≠ ⊤) :
    Indep (MeasurableSpace.comap (fun ω t => brownianRestartAt B τ t ω) inferInstance)
      hτ.measurableSpace μ := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hm : @Measurable Ω Ω mΩ hτ.measurableSpace id := fun A hA => hτ.measurableSpace_le A hA
  have hi := @IndepFun.process_indepFun₀ ℝ≥0 Ω mΩ μ (fun _ => ℝ) Ω
    (fun _ => inferInstance) hτ.measurableSpace (brownianRestartAt B τ) id
    (fun t => (isBrownianReal_brownianRestartAt hB hτ hfinite).aemeasurable t)
    (show @AEMeasurable Ω Ω hτ.measurableSpace mΩ id μ from ⟨id, hm, EventuallyEq.rfl⟩)
    (fun I => show @IndepFun Ω (I → ℝ) Ω mΩ inferInstance hτ.measurableSpace
        (fun ω t => brownianRestartAt B τ t.1 ω) id μ from by
      change Indep _ (MeasurableSpace.comap id hτ.measurableSpace) μ
      simpa only [MeasurableSpace.comap_id] using brownianRestartAt_finite_indep_stopped hB I hτ hfinite)
    inferInstance
  change Indep _ (MeasurableSpace.comap id hτ.measurableSpace) μ at hi
  simpa only [MeasurableSpace.comap_id] using hi

end BrownianAffine.Augmented
