import PLAStochastic.Affine.Process.IntervalExit.PathPrefix
import PLAStochastic.Affine.Process.IntervalExit.EnlargedDomain

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The measurable continuation test selects exactly the actual newly surviving paths. -/
theorem upperContinuationSet_actual_ae_iff (hB : IsBrownianReal B μ)
    {x r R : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) (hrR : r < R)
    {T : ℝ≥0} (hT : 0 < T) (S : Set ℝ) :
    ∀ᵐ ω ∂μ,
      (((intervalTouchClock B x r ω : ℝ),intervalTouchEndpoint B x r ω),
        unitPath (processPath (brownianRestartAt B (intervalTouchTime B x r)) ω) T) ∈
          upperContinuationSet T r R S ↔
      (T : ℝ≥0∞) < intervalTouchTime B x R ω ∧
        intervalTouchTime B x r ω ≤ T ∧ x+B T ω ∈ S := by
  filter_upwards [hB.cont,hB.eval_zero_ae_eq_zero,intervalTouchTime_ae_ne_top hB x r,
    (isBrownianReal_restart_intervalTouch hB x hr).cont] with ω hc h0 hf hcR
  have hτ : intervalTouchTime B x r ω = (intervalTouchClock B x r ω : ℝ≥0∞) := by
    obtain ⟨s,hs⟩ := WithTop.ne_top_iff_exists.mp hf
    rw [intervalTouchClock,← hs]
    rfl
  have hle : intervalTouchTime B x r ω ≤ T ↔ intervalTouchClock B x r ω ≤ T := by
    rw [hτ]
    exact_mod_cast Iff.rfl
  by_cases hs : intervalTouchClock B x r ω ≤ T
  · have hreal : (intervalTouchClock B x r ω : ℝ) ∈ Icc (0 : ℝ) (T : ℝ) :=
      ⟨(intervalTouchClock B x r ω).property,by exact_mod_cast hs⟩
    have hpre := prefixSurvival_unitPath_iff_touch hcR r (hr.trans hrR) hT hs
    have heval : intervalTouchEndpoint B x r ω +
        unitPath (processPath (brownianRestartAt B (intervalTouchTime B x r)) ω) T
          (remainingFraction T (intervalTouchClock B x r ω)) = x+B T ω := by
      rw [unitPath_remainingFraction_apply _ hT hs,processPath_apply_of_continuous hcR]
      dsimp only [intervalTouchEndpoint,brownianRestartAt,brownianRestart]
      change x+B (intervalTouchClock B x r ω) ω+
        (B (intervalTouchClock B x r ω+(T-intervalTouchClock B x r ω)) ω-
          B (intervalTouchClock B x r ω) ω) = x+B T ω
      rw [add_tsub_cancel_of_le hs]
      ring
    have hd := intervalTouch_enlarged_survival_after_exit hc h0 hr hx hrR hτ hs
    change (T : ℝ≥0∞) < intervalTouchTime B x R ω ↔
      intervalTouchEndpoint B x r ω=r ∧ ((T-intervalTouchClock B x r ω : ℝ≥0) : ℝ≥0∞) <
        intervalTouchTime (brownianRestartAt B (intervalTouchTime B x r)) r R ω at hd
    dsimp only [upperContinuationSet,mem_ofPred_eq,Prod.fst,Prod.snd]
    rw [hpre,hd,hle]
    constructor
    · rintro ⟨_,he,hp,hz⟩
      refine ⟨⟨he,hp⟩,hs,?_⟩
      have hev := heval
      rw [he] at hev
      rwa [hev] at hz
    · rintro ⟨⟨he,hp⟩,_,hz⟩
      refine ⟨hreal,he,hp,?_⟩
      have hev := heval
      rw [he] at hev
      rwa [hev]
  · have hreal : ¬ (intervalTouchClock B x r ω : ℝ) ∈ Icc (0 : ℝ) (T : ℝ) := by
      intro h
      exact hs (by exact_mod_cast h.2)
    simp only [upperContinuationSet,mem_ofPred_eq,hreal,false_and,hle,hs,and_false]

theorem killedBrownianMeasure_apply_touch (hB : IsBrownianReal B μ)
    {x r : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) {T : ℝ≥0} (hT : T ≠ 0)
    {S : Set ℝ} (hS : MeasurableSet S) :
    killedBrownianMeasure B μ x r T S =
      μ {ω | (T : ℝ≥0∞) < intervalTouchTime B x r ω ∧ x+B T ω ∈ S} := by
  have hm := (hB.aemeasurable T).const_add x
  rw [killedBrownianMeasure_eq_touch_survival hB hr hx hT,
    Measure.map_apply_of_aemeasurable hm.restrict hS,
    Measure.restrict_apply₀ (hm.restrict.nullMeasurableSet_preimage hS)]
  congr 1
  ext ω
  exact and_comm

/-- A deterministic exit time in the continuation test yields the actual killed
endpoint measure over precisely the remaining duration. -/
theorem upperContinuationSet_fixed_time_measure (hB : IsBrownianReal B μ)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    {T s : ℝ≥0} (hT : 0 < T) (hs : s < T) {S : Set ℝ} (hS : MeasurableSet S) :
    μ {ω | (((s : ℝ),r),unitPath (processPath B ω) T) ∈ upperContinuationSet T r R S} =
      killedBrownianMeasure B μ r R (T-s) S := by
  rw [killedBrownianMeasure_apply_touch hB (hr.trans hrR) ⟨hr,hrR⟩
    (ne_of_gt (tsub_pos_iff_lt.mpr hs)) hS]
  apply measure_congr
  filter_upwards [hB.cont] with ω hc
  have he : unitPath (processPath B ω) T (remainingFraction T s) = B (T-s) ω := by
    rw [unitPath_remainingFraction_apply _ hT hs.le,processPath_apply_of_continuous hc]
  have hpre := prefixSurvival_unitPath_iff_touch hc r (hr.trans hrR) hT hs.le
  have hreal : (s : ℝ) ∈ Icc (0 : ℝ) (T : ℝ) := ⟨s.property,by exact_mod_cast hs.le⟩
  apply propext
  change (s : ℝ) ∈ Icc (0 : ℝ) (T : ℝ) ∧ r=r ∧
      prefixSurvival (unitPath (processPath B ω) T) (remainingFraction T s) r R ∧
      r+unitPath (processPath B ω) T (remainingFraction T s) ∈ S ↔ _
  rw [hpre,he]
  simp only [hreal,true_and]
  rfl


end BrownianAffine
