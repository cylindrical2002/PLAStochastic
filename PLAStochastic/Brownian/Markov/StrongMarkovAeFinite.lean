import PLAStochastic.Brownian.Markov.StrongMarkov

/-!
# Strong Markov at an almost surely finite extended stopping time

The original stopping time and its stopped sigma-algebra are preserved. Truncation
is used only on the event where the original stopping time is below the cutoff.
The value assigned at infinity only defines the future process on a null set.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

def truncateBrownianStop (τ : Ω → WithTop ℝ≥0) (H : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  (min (τ ω) (H : WithTop ℝ≥0)).untopD 0

omit mΩ in
theorem coe_truncateBrownianStop (τ : Ω → WithTop ℝ≥0) (H : ℝ≥0) (ω : Ω) :
    (truncateBrownianStop τ H ω : WithTop ℝ≥0) = min (τ ω) (H : WithTop ℝ≥0) := by
  cases h : τ ω with
  | top => simp only [truncateBrownianStop, h, min_top_left, WithTop.untopD_coe]
  | coe t => simp only [truncateBrownianStop, h, ← WithTop.coe_min, WithTop.untopD_coe]

omit mΩ in
theorem truncateBrownianStop_eq_of_le (τ : Ω → WithTop ℝ≥0) (H : ℝ≥0) {ω : Ω}
    (h : τ ω ≤ (H : WithTop ℝ≥0)) : truncateBrownianStop τ H ω = (τ ω).untopD 0 := by
  simp only [truncateBrownianStop, min_eq_left h]

theorem truncateBrownianStop_isStoppingTime {ℱ : Filtration ℝ≥0 mΩ}
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) (H : ℝ≥0) :
    IsStoppingTime ℱ (fun ω => (truncateBrownianStop τ H ω : WithTop ℝ≥0)) := by
  have heq : (fun ω => (truncateBrownianStop τ H ω : WithTop ℝ≥0)) =
      fun ω => min (τ ω) (H : WithTop ℝ≥0) := funext (coe_truncateBrownianStop τ H)
  rw [heq]
  exact hτ.min_const H

theorem stoppedEvent_truncate_measurable {ℱ : Filtration ℝ≥0 mΩ}
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) (H : ℝ≥0)
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) :
    MeasurableSet[(truncateBrownianStop_isStoppingTime hτ H).measurableSpace]
      (A ∩ {ω | τ ω ≤ (H : WithTop ℝ≥0)}) := by
  have h := hτ.measurableSet_inter_le (isStoppingTime_const ℱ H) A hA
  simp only [IsStoppingTime.measurableSet, coe_truncateBrownianStop] at h ⊢
  exact h

theorem ae_eq_iUnion_stopping_le {τ : Ω → WithTop ℝ≥0}
    (hfinite : ∀ᵐ ω ∂μ, τ ω ≠ ⊤) (A : Set Ω) :
    ((⋃ n : ℕ, A ∩ {ω | τ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)}) : Set Ω) =ᵐ[μ] A := by
  filter_upwards [hfinite] with ω hω
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hω
  obtain ⟨n, hn⟩ := exists_nat_ge t
  apply propext
  change (ω ∈ (⋃ n : ℕ, A ∩ {ω | τ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)})) ↔ ω ∈ A
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · exact fun ⟨_, h, _⟩ => h
  · intro ha
    exact ⟨n, ha, ht ▸ WithTop.coe_le_coe.mpr hn⟩

omit mΩ in
theorem truncateBrownianStop_eventually_eq {τ : Ω → WithTop ℝ≥0} {ω : Ω}
    (hfinite : τ ω ≠ ⊤) :
    ∀ᶠ n : ℕ in atTop, truncateBrownianStop τ n ω = (τ ω).untopD 0 := by
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hfinite
  obtain ⟨N, hN⟩ := exists_nat_ge t
  filter_upwards [eventually_ge_atTop N] with n hn
  apply truncateBrownianStop_eq_of_le
  rw [← ht]
  exact WithTop.coe_le_coe.mpr (hN.trans (by exact_mod_cast hn))

variable {B : ℝ≥0 → Ω → ℝ}

/-- Infinity is left in the stopping-time definition; only evaluation uses a fallback. -/
def brownianRestartAt (B : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0) : ℝ≥0 → Ω → ℝ :=
  brownianRestart B (fun ω => (τ ω).untopD 0)

theorem brownianRestartAt_finite_aemeasurable (hB : IsBrownianReal B μ)
    (I : Finset ℝ≥0) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (brownianNaturalFiltration hB.toIsPreBrownianReal) τ)
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
    (hτ : IsStoppingTime (brownianNaturalFiltration hB.toIsPreBrownianReal) τ)
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
    (hτ : IsStoppingTime (brownianNaturalFiltration hB.toIsPreBrownianReal) τ)
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
    (hτ : IsStoppingTime (brownianNaturalFiltration hB.toIsPreBrownianReal) τ)
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
    (hτ : IsStoppingTime (brownianNaturalFiltration hB.toIsPreBrownianReal) τ)
    (hfinite : ∀ᵐ ω ∂μ, τ ω ≠ ⊤) : IsBrownianReal (brownianRestartAt B τ) μ where
  hasLaw I := brownianRestartAt_hasLaw hB I hτ hfinite
  cont := hB.cont.mono (fun _ hω => (hω.comp (continuous_const.add continuous_id)).sub continuous_const)

theorem brownianRestartAt_finite_indep_stopped (hB : IsBrownianReal B μ)
    (I : Finset ℝ≥0) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (brownianNaturalFiltration hB.toIsPreBrownianReal) τ)
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
    (hτ : IsStoppingTime (brownianNaturalFiltration hB.toIsPreBrownianReal) τ)
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

end BrownianAffine
