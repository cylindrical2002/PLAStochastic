import PLAStochastic.Swing.StationaryLimit.MarginKernel.Limiting

/-! # The limiting margin kernel is equivalent to Lebesgue measure

Theorem 4.3 asserts that the invariant law of `K` is absolutely continuous and
equivalent to Lebesgue measure.  Both directions already hold for each single
transition: the equilibrium overshoot has a Lebesgue density, and that density
is strictly positive because the ladder height can exceed any level on its first
step, while the limiting slope exceeds any level with positive probability.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-! ### The limiting slope dominates each finite ratio -/

theorem swingLimitingSlope_term_le_ae
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (r : ℝ) :
    ∀ᵐ ω ∂μ, ∀ n : ℕ,
      (cumulativeSamples X n ω - r)/((n : ℝ)+1) ≤ swingLimitingSlope X r ω := by
  have hnegX : ∀ n, Measurable (fun ω => -X n ω) := fun n => (hX n).neg
  have hnegi : iIndepFun (fun n ω => -X n ω) μ :=
    hi.comp (fun _ x => -x) (fun _ => measurable_neg)
  have hnegG := gaussianIncrement_reflected_law hX hG
  filter_upwards [frozenUpperSlope_tendsto_zero_ae hnegX hnegi hnegG r] with ω hω
  intro n
  have hb := frozenSlopeMagnitude_bddAbove hω
  have hle := neg_frozenUpperSlope_le_magnitude hb n
  rw [swingLimitingSlope_eq_frozen_reflection]
  refine le_trans (le_of_eq ?_) hle
  simp only [frozenUpperSlope, cumulativeSamples, Finset.sum_neg_distrib]
  ring

/-- The limiting slope exceeds every level with positive probability: already the
first increment can be large. -/
theorem swingSlopeKernel_Ioi_pos [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (r c : ℝ) :
    0 < swingSlopeKernel X μ r (Ioi c) := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hstart : 0 < μ {ω : Ω | 2*c + r < X 0 ω} := by
    have heq : μ {ω : Ω | 2*c + r < X 0 ω} = gaussianReal 0 1 (Ioi (2*c + r)) := by
      rw [← hG 0, Measure.map_apply (hX 0) measurableSet_Ioi]
      rfl
    rw [heq]
    exact gaussianReal_Ioi_pos _
  have hmono : μ {ω : Ω | 2*c + r < X 0 ω} ≤ μ {ω : Ω | swingLimitingSlope X r ω ∈ Ioi c} := by
    refine measure_mono_ae ?_
    filter_upwards [swingLimitingSlope_term_le_ae hX hi hG r] with ω hω hmem
    have hmem' : 2*c + r < X 0 ω := hmem
    have h1 := hω 1
    have hcs : cumulativeSamples X 1 ω = X 0 ω := by
      simp [cumulativeSamples]
    rw [hcs] at h1
    have htwo : ((1 : ℕ) : ℝ) + 1 = 2 := by norm_num
    rw [htwo] at h1
    show c < swingLimitingSlope X r ω
    linarith
  rw [swingSlopeKernel_apply hX r measurableSet_Ioi]
  exact lt_of_lt_of_le hstart hmono

/-! ### The equilibrium density is strictly positive -/

theorem swingEquilibriumDensity_pos
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a o : ℝ} (ha : 0 < a) (ho : 0 ≤ o) :
    0 < swingEquilibriumDensity X μ a o := by
  rw [swingEquilibriumDensity, ENNReal.div_pos_iff]
  exact ⟨(gaussianAscendingLadderLaw_tail_pos hX hG ho).ne',
    gaussianAscendingLadderLaw_mean_ne_top hX hi hG ha le_rfl le_rfl⟩

/-! ### Both directions of absolute continuity for one transition -/

omit [MeasurableSpace Ω] in
theorem volume_preimage_const_sub (a : ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    volume ((fun o : ℝ => a - o) ⁻¹' s) = volume s := by
  have hmp := Measure.measurePreserving_sub_left (volume : Measure ℝ) a
  exact hmp.measure_preimage hs.nullMeasurableSet

omit [MeasurableSpace Ω] in
theorem preimage_const_sub_inter (a : ℝ) (s : Set ℝ) :
    ((fun o : ℝ => a - o) ⁻¹' s) ∩ Ici (0 : ℝ) = (fun o : ℝ => a - o) ⁻¹' (s ∩ Iic a) := by
  ext o
  simp only [mem_inter_iff, mem_preimage, mem_Ici, mem_Iic]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by linarith⟩

/-- The overshoot transition is absolutely continuous with respect to Lebesgue
measure: the equilibrium law has a density. -/
theorem swingOvershootMeasure_absolutelyContinuous (X : ℕ → Ω → ℝ) (μ : Measure Ω) (a : ℝ) :
    swingOvershootMeasure X μ a ≪ volume := by
  refine Measure.AbsolutelyContinuous.mk (fun s hs hzero => ?_)
  rw [swingOvershootMeasure_apply X μ a hs]
  refine setLIntegral_measure_zero _ _ ?_
  have hsub : volume (((fun o : ℝ => a - o) ⁻¹' s) ∩ Ici (0 : ℝ)) ≤
      volume ((fun o : ℝ => a - o) ⁻¹' s) := measure_mono inter_subset_left
  rw [volume_preimage_const_sub a hs, hzero] at hsub
  exact nonpos_iff_eq_zero.mp hsub

/-- Conversely a Lebesgue-positive set below the drift receives positive mass. -/
theorem volume_inter_Iic_eq_zero_of_swingOvershootMeasure_eq_zero
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a)
    {s : Set ℝ} (hs : MeasurableSet s) (hzero : swingOvershootMeasure X μ a s = 0) :
    volume (s ∩ Iic a) = 0 := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  set T : Set ℝ := ((fun o : ℝ => a - o) ⁻¹' s) ∩ Ici (0 : ℝ) with hT
  have hTmeas : MeasurableSet T :=
    (hs.preimage (measurable_const_sub_self a)).inter measurableSet_Ici
  have hint : (∫⁻ o in T, swingEquilibriumDensity X μ a o) = 0 := by
    rw [← swingOvershootMeasure_apply X μ a hs]
    exact hzero
  have hdm : Measurable (fun o : ℝ => swingEquilibriumDensity X μ a o) :=
    (swingEquilibriumDensity_joint_measurable hX).comp
      ((measurable_const (a := a)).prodMk measurable_id)
  have hae : (fun o : ℝ => swingEquilibriumDensity X μ a o) =ᵐ[volume.restrict T] 0 :=
    (lintegral_eq_zero_iff hdm).mp hint
  have hnull : (volume.restrict T) {o : ℝ | swingEquilibriumDensity X μ a o ≠ 0} = 0 := by
    have := hae
    rw [Filter.EventuallyEq, ae_iff] at this
    simpa using this
  have hTsub : T ⊆ {o : ℝ | swingEquilibriumDensity X μ a o ≠ 0} := by
    intro o hoT
    exact (swingEquilibriumDensity_pos hX hi hG ha hoT.2).ne'
  have hT0 : volume T = 0 := by
    have hle : (volume.restrict T) T ≤
        (volume.restrict T) {o : ℝ | swingEquilibriumDensity X μ a o ≠ 0} :=
      measure_mono hTsub
    rw [hnull, le_zero_iff] at hle
    rwa [Measure.restrict_apply_self] at hle
  rw [hT, preimage_const_sub_inter a s, volume_preimage_const_sub a (hs.inter measurableSet_Iic)]
    at hT0
  exact hT0

end SwingRepair
