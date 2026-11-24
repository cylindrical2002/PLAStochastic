import PLAStochastic.Affine.Process.IntervalExit.FirstContact
import PLAStochastic.Affine.Pinch.OffsetAnchor
import PLAStochastic.Brownian.Killed.EndpointMeasure

/-!
# Regularity of the first interval endpoint contact

For an actual Brownian path started inside the interval, the first contact is
finite and is immediately followed by strict crossings. Consequently the existing
capped-crossing survival event is the usual strict first-contact survival event.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

private theorem measurable_unitPath_augmented (hB : IsBrownianReal B μ) (T : ℝ≥0) :
    Measurable[augmentedBrownianFiltration hB.toIsPreBrownianReal T]
      (fun ω => unitPath (continuousBrownianPath hB ω) T) := by
  apply measurableEmbedding_pathObservations.measurable_comp_iff.mp
  refine @measurable_pi_lambda Ω ErrorSample (fun _ => ℝ)
    (augmentedBrownianFiltration hB.toIsPreBrownianReal T) (fun _ => inferInstance) _ ?_
  intro s
  have hst : T * errorSampleTime s ≤ T := mul_le_of_le_one_right T.property s.1.property.2
  have hm := (adapted_continuousBrownian_coordinate hB (T * errorSampleTime s)).mono
    ((augmentedBrownianFiltration hB.toIsPreBrownianReal).mono hst) le_rfl
  simpa only [Function.comp_def, pathObservations, unitPath, ContinuousMap.coe_mk,
    NNReal.coe_mul, errorSampleTime, NNReal.coe_mk] using! hm

private theorem adapted_intervalPrefixNorm (hB : IsBrownianReal B μ) (x r : ℝ) :
    Adapted (augmentedBrownianFiltration hB.toIsPreBrownianReal)
      (fun T ω => prefixNorm (centeredIntervalPath (continuousBrownianPath hB ω) x r) T) := by
  intro T
  have hc : Measurable (fun f : Path 1 => ‖f + ContinuousMap.const (Icc (0 : ℝ) 1) (x - r / 2)‖) := by
    fun_prop
  have he : (fun T ω => prefixNorm (centeredIntervalPath (continuousBrownianPath hB ω) x r) T) T =
      (fun ω => ‖unitPath (continuousBrownianPath hB ω) T +
        ContinuousMap.const (Icc (0 : ℝ) 1) (x - r / 2)‖) := by
    funext ω
    congr 1
  rw [he]
  exact hc.comp (measurable_unitPath_augmented hB T)

/-- An everywhere measurable continuous version of the genuine first contact. -/
def brownianIntervalTouch (hB : IsBrownianReal B μ) (x r : ℝ) (ω : Ω) : ℝ≥0∞ :=
  pathClosedHit (centeredIntervalPath (continuousBrownianPath hB ω) x r) (r / 2)

theorem brownianIntervalTouch_ae_eq (hB : IsBrownianReal B μ) (x r : ℝ) :
    brownianIntervalTouch hB x r =ᵐ[μ] intervalTouchTime B x r := by
  filter_upwards [continuousBrownianPath_all_times_ae_eq hB] with ω hω
  exact (intervalTouchTime_repr (continuousBrownianPath hB ω) hω x r).symm

theorem brownianIntervalTouch_isStoppingTime (hB : IsBrownianReal B μ) (x : ℝ)
    {r : ℝ} (hr : 0 < r) :
    IsStoppingTime (augmentedBrownianFiltration hB.toIsPreBrownianReal) (brownianIntervalTouch hB x r) := by
  intro T
  have heq : {ω | brownianIntervalTouch hB x r ω ≤ (T : WithTop ℝ≥0)} =
      {ω | r / 2 ≤ prefixNorm (centeredIntervalPath (continuousBrownianPath hB ω) x r) T} := by
    ext ω
    change pathClosedHit _ (r / 2) ≤ (T : ℝ≥0∞) ↔ _
    rw [pathClosedHit_eq_firstReach _ (by positivity)]
    exact firstReach_le_iff (monotone_prefixNorm _) (continuous_prefixNorm _) T
  rw [heq]
  exact measurableSet_le measurable_const (adapted_intervalPrefixNorm hB x r T)

/-- The original first contact is a stopping time in the completed natural filtration. -/
theorem intervalTouchTime_isStoppingTime_completed (hB : IsBrownianReal B μ) (x : ℝ)
    {r : ℝ} (hr : 0 < r) :
    IsStoppingTime (completedBrownianFiltration hB.toIsPreBrownianReal)
      (intervalTouchTime B x r) := by
  intro T
  have ht := (brownianIntervalTouch_isStoppingTime hB x hr) T
  apply EventuallyMeasurableSet.congr ht.2
  filter_upwards [brownianIntervalTouch_ae_eq hB x r] with ω hω
  apply propext
  change intervalTouchTime B x r ω ≤ (T : WithTop ℝ≥0) ↔
    brownianIntervalTouch hB x r ω ≤ (T : WithTop ℝ≥0)
  rw [hω]

/-- A Brownian path starting in the open interval has positive first-contact time. -/
theorem intervalTouchTime_ae_pos (hB : IsBrownianReal B μ)
    {x r : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) :
    ∀ᵐ ω ∂μ, 0 < intervalTouchTime B x r ω := by
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero] with ω hc hz
  apply lt_of_not_ge
  intro h
  obtain ⟨t, ht, hout⟩ := (intervalTouchTime_le_iff hc hr 0).mp h
  have ht0 : t = 0 := le_antisymm ht bot_le
  apply hout
  simpa only [ht0, hz, add_zero] using hx

theorem intervalTouchTime_ae_ne_top (hB : IsBrownianReal B μ) (x r : ℝ) :
    ∀ᵐ ω ∂μ, intervalTouchTime B x r ω ≠ ⊤ := by
  filter_upwards [brownian_unbounded_above_ae hB] with ω hω
  obtain ⟨t, ht⟩ := hω (r - x)
  have hout : x + B t ω ∉ Ioo 0 r := by intro h; linarith [h.2]
  exact ne_top_of_le_ne_top ENNReal.coe_ne_top (intervalTouchTime_le_of_outside hout)

theorem isBrownianReal_restart_intervalTouch (hB : IsBrownianReal B μ) (x : ℝ)
    {r : ℝ} (hr : 0 < r) :
    IsBrownianReal (brownianRestartAt B (intervalTouchTime B x r)) μ := by
  have hf : ∀ᵐ ω ∂μ, brownianIntervalTouch hB x r ω ≠ ⊤ := by
    filter_upwards [brownianIntervalTouch_ae_eq hB x r, intervalTouchTime_ae_ne_top hB x r] with ω he hf
    rwa [he]
  have hb := Augmented.isBrownianReal_brownianRestartAt hB
    (brownianIntervalTouch_isStoppingTime hB x hr) hf
  have hpre := hb.toIsPreBrownianReal.congr (C := brownianRestartAt B (intervalTouchTime B x r))
    (fun t => by
      filter_upwards [brownianIntervalTouch_ae_eq hB x r] with ω hω
      simp only [brownianRestartAt, brownianRestart, hω])
  exact ⟨hpre, hB.cont.mono (fun _ hc =>
    (hc.comp (continuous_const.add continuous_id)).sub continuous_const)⟩

theorem brownian_crossing_after_intervalTouch_ae (hB : IsBrownianReal B μ)
    {x r : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) :
    ∀ᵐ ω ∂μ, ∀ δ : ℝ≥0, 0 < δ → ∃ u : ℝ≥0, 0 < u ∧ u < δ ∧
      (x + B ((intervalTouchTime B x r ω).untopD 0 + u) ω < 0 ∨
        r < x + B ((intervalTouchTime B x r ω).untopD 0 + u) ω) := by
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero, intervalTouchTime_ae_ne_top hB x r,
    brownian_linear_oscillation_zero_ae (isBrownianReal_restart_intervalTouch hB x hr)]
    with ω hc hz hf ho
  obtain ⟨σ, hσ⟩ := WithTop.ne_top_iff_exists.mp hf
  have hu : (intervalTouchTime B x r ω).untopD 0 = σ := by rw [← hσ]; rfl
  have hb := intervalTouchTime_terminal hc hz hr hx hσ.symm
  intro δ hδ
  obtain ⟨⟨u, hu0, huδ, hup⟩, ⟨v, hv0, hvδ, hvn⟩⟩ := ho 0 δ hδ
  simp only [brownianRestartAt, brownianRestart, hu, zero_mul, sub_zero] at hup hvn
  rcases hb with hb | hb
  · exact ⟨v, hv0, hvδ, Or.inl (by rw [hu]; linarith)⟩
  · exact ⟨u, hu0, huδ, Or.inr (by rw [hu]; linarith)⟩

theorem boundedIntervalExit_eq_min_touch_ae (hB : IsBrownianReal B μ)
    {x r : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) :
    ∀ᵐ ω ∂μ, ∀ T : ℝ≥0, boundedIntervalExit B x r T ω =
      min ((intervalTouchTime B x r ω).untopD 0) T := by
  filter_upwards [intervalTouchTime_ae_ne_top hB x r, brownian_crossing_after_intervalTouch_ae hB hr hx]
    with ω hf hc
  obtain ⟨σ, hσ⟩ := WithTop.ne_top_iff_exists.mp hf
  have hu : (intervalTouchTime B x r ω).untopD 0 = σ := by rw [← hσ]; rfl
  rw [hu] at hc ⊢
  exact boundedIntervalExit_eq_min_touch_of_crossing hσ.symm hc

theorem intervalTouchTime_aemeasurable (hB : IsBrownianReal B μ) (x : ℝ)
    {r : ℝ} (hr : 0 < r) : AEMeasurable (intervalTouchTime B x r) μ :=
  (brownianIntervalTouch_isStoppingTime hB x hr).measurable'.aemeasurable.congr
    (brownianIntervalTouch_ae_eq hB x r)

theorem intervalTouchTime_ne_fixed_ae (hB : IsBrownianReal B μ)
    {x r : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) {T : ℝ≥0} (hT : T ≠ 0) :
    ∀ᵐ ω ∂μ, intervalTouchTime B x r ω ≠ (T : ℝ≥0∞) := by
  have hX : HasLaw (fun ω => x + B T ω) (gaussianReal x T) μ := by
    simpa only [zero_add] using gaussianReal_const_add (hB.toIsPreBrownianReal.hasLaw_eval T) x
  have hnp : ∀ᵐ ω ∂μ, x + B T ω ≠ 0 ∧ x + B T ω ≠ r := by
    apply (hX.ae_iff (p := fun z : ℝ => z ≠ 0 ∧ z ≠ r) (by fun_prop)).mpr
    apply (gaussianReal_absolutelyContinuous x hT).ae_le
    have h0 : ∀ᵐ z : ℝ ∂volume, z ≠ 0 := by
      rw [ae_iff]
      simp
    have hr0 : ∀ᵐ z : ℝ ∂volume, z ≠ r := by
      rw [ae_iff]
      simp
    exact h0.and hr0
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero, hnp] with ω hc hz hn
  intro he
  exact (intervalTouchTime_terminal hc hz hr hx he).elim hn.1 hn.2

/-- The infimum of actual strict crossings equals the first contact, almost surely. -/
theorem openIntervalExit_eq_touch_ae (hB : IsBrownianReal B μ)
    {x r : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) :
    ∀ᵐ ω ∂μ, (openExitTime (fun t ω => x + B t ω) (driftBarrierSet r 0) ω : ℝ≥0∞) =
      intervalTouchTime B x r ω := by
  filter_upwards [intervalTouchTime_ae_ne_top hB x r, boundedIntervalExit_eq_min_touch_ae hB hr hx,
    brownian_crossing_after_intervalTouch_ae hB hr hx] with ω hf hb hc
  obtain ⟨σ, hσ⟩ := WithTop.ne_top_iff_exists.mp hf
  have hu : (intervalTouchTime B x r ω).untopD 0 = σ := by rw [← hσ]; rfl
  rw [hu] at hb hc
  obtain ⟨u, _, hu1, hout⟩ := hc 1 zero_lt_one
  have hm : x + B (σ + u) ω ∈ driftBarrierSet r 0 := by
    simpa only [driftBarrierSet, mem_union, mem_Iio, mem_Ioi, neg_zero] using hout
  have hne : {t : ℝ≥0 | x + B t ω ∈ driftBarrierSet r 0}.Nonempty := ⟨σ + u, hm⟩
  have hcut : openExitTime (fun t ω => x + B t ω) (driftBarrierSet r 0) ω ≤ σ + 1 := by
    have hh : openExitTime (fun t ω => x + B t ω) (driftBarrierSet r 0) ω ≤ σ + u :=
      csInf_le ⟨0, fun _ _ => bot_le⟩ hm
    exact hh.trans (by gcongr)
  have he := boundedOpenExitTime_eq_openExitTime hne hcut
  change boundedIntervalExit B x r (σ + 1) ω = _ at he
  have hfin := hb (σ + 1)
  rw [he, min_eq_left (by simp)] at hfin
  exact (congrArg (fun t : ℝ≥0 => (t : ℝ≥0∞)) hfin).trans hσ

/-- Standard strict survival and the original capped-crossing event agree almost surely. -/
theorem intervalSurvival_ae_iff_touch_gt (hB : IsBrownianReal B μ)
    {x r : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) {T : ℝ≥0} (hT : T ≠ 0) :
    ∀ᵐ ω ∂μ, boundedIntervalExit B x r T ω = T ↔ (T : ℝ≥0∞) < intervalTouchTime B x r ω := by
  filter_upwards [boundedIntervalExit_eq_min_touch_ae hB hr hx,
    intervalTouchTime_ae_ne_top hB x r, intervalTouchTime_ne_fixed_ae hB hr hx hT]
    with ω hb hf hn
  obtain ⟨σ, hσ⟩ := WithTop.ne_top_iff_exists.mp hf
  have hu : (intervalTouchTime B x r ω).untopD 0 = σ := by rw [← hσ]; rfl
  rw [hb T, hu, ← hσ]
  change min σ T = T ↔ (T : WithTop ℝ≥0) < (σ : WithTop ℝ≥0)
  rw [WithTop.coe_lt_coe, min_eq_right_iff]
  have hne : σ ≠ T := by intro h; apply hn; rw [← hσ, h]; rfl
  exact ⟨fun h => lt_of_le_of_ne h hne.symm, fun h => h.le⟩

/-- The existing killed endpoint measure is exactly the measure killed at first contact. -/
theorem killedBrownianMeasure_eq_touch_survival (hB : IsBrownianReal B μ)
    {x r : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) {T : ℝ≥0} (hT : T ≠ 0) :
    killedBrownianMeasure B μ x r T =
      (μ.restrict {ω | (T : ℝ≥0∞) < intervalTouchTime B x r ω}).map (fun ω => x + B T ω) := by
  unfold killedBrownianMeasure
  congr 1
  apply Measure.restrict_congr_set
  exact (intervalSurvival_ae_iff_touch_gt hB hr hx hT).mono (fun _ h => propext h)

end BrownianAffine
