import PLAStochastic.Affine.Process.IntervalExit.PathPrefix
import PLAStochastic.Affine.Process.IntervalExit.EnlargedDomain

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- Continuous clipping onto the unit observation interval. -/
def unitClamp (s : ℝ) : Icc (0 : ℝ) 1 :=
  ⟨max 0 (min 1 s),le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩

theorem continuous_unitClamp : Continuous unitClamp :=
  (continuous_const.max (continuous_const.min continuous_id)).subtype_mk _

theorem unitClamp_coe {s : ℝ} (hs : s ∈ Icc 0 1) : (unitClamp s : ℝ)=s := by
  simp only [unitClamp,min_eq_right hs.2,max_eq_right hs.1]

/-- Extend an observed unit path constantly past its observation horizon. -/
def observedPath (T : ℝ) (f : Path 1) : C(ℝ,ℝ) :=
  ⟨fun t => f (unitClamp (t/T)),
    f.continuous.comp (continuous_unitClamp.comp (continuous_id.div_const T))⟩

def observedProcess (T : ℝ) (t : ℝ≥0) (f : Path 1) : ℝ := observedPath T f t

theorem continuous_observedPath_eval (T : ℝ) :
    Continuous (fun p : Path 1 × ℝ => observedPath T p.1 p.2) :=
  continuous_eval.comp (continuous_fst.prodMk
    (continuous_unitClamp.comp (continuous_snd.div_const T)))

theorem continuous_observedPath_prefix (T : ℝ) (U : ℝ≥0) :
    Continuous (fun f : Path 1 => unitPath (observedPath T f) U) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (continuous_observedPath_eval T).comp
    (continuous_fst.prodMk (continuous_const.mul (continuous_subtype_val.comp continuous_snd)))

/-- First contact can be read measurably from the entire observed continuous path. -/
theorem measurable_observedIntervalTouch (T y : ℝ) {R : ℝ} (hR : 0 < R) :
    Measurable (intervalTouchTime (observedProcess T) y R) := by
  apply measurable_of_Iic
  intro u
  by_cases hu : u=⊤
  · simp only [hu,Iic_top,preimage_univ,MeasurableSet.univ]
  · obtain ⟨U,hU⟩ := WithTop.ne_top_iff_exists.mp hu
    have hU' : (U : ℝ≥0∞)=u := hU
    rw [← hU']
    have he : (intervalTouchTime (observedProcess T) y R) ⁻¹' Iic (U : ℝ≥0∞) =
        {f | R/2 ≤ ‖unitPath (observedPath T f) U+ContinuousMap.const _ (y-R/2)‖} := by
      ext f
      change intervalTouchTime (observedProcess T) y R f ≤ (U : ℝ≥0∞) ↔ _
      rw [intervalTouchTime_repr (observedPath T f) (fun _ => rfl),
        pathClosedHit_eq_firstReach _ (by positivity),
        firstReach_le_iff (monotone_prefixNorm _) (continuous_prefixNorm _)]
      rfl
    rw [he]
    exact measurableSet_le measurable_const
      (((continuous_observedPath_prefix T U).add continuous_const).norm.measurable)

theorem measurable_observedIntervalClock (T y : ℝ) {R : ℝ} (hR : 0 < R) :
    Measurable (intervalTouchClock (observedProcess T) y R) :=
  (WithTop.measurable_untopD 0).comp (measurable_observedIntervalTouch T y hR)

theorem measurable_observedIntervalEndpoint (T y : ℝ) {R : ℝ} (hR : 0 < R) :
    Measurable (intervalTouchEndpoint (observedProcess T) y R) :=
  measurable_const.add ((continuous_observedPath_eval T).measurable.comp
    (measurable_id.prodMk (measurable_observedIntervalClock T y hR).coe_nnreal_real))

/-- The read-back process is the actual process at every observed time, pathwise. -/
theorem observedProcess_actual_prefix {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (B · ω)) {T : ℝ≥0} (hT : 0 < T) {t : ℝ≥0} (ht : t ≤ T) :
    observedProcess T t (unitPath (processPath B ω) T)=B t ω := by
  change unitPath (processPath B ω) T (unitClamp ((t : ℝ)/T))=B t ω
  rw [unitPath_processPath_apply hc]
  congr 2
  apply Subtype.ext
  change (T : ℝ)*(unitClamp ((t : ℝ)/T) : ℝ)=(t : ℝ)
  rw [unitClamp_coe (s := (t : ℝ)/(T : ℝ)) ⟨div_nonneg t.property T.property,
    (div_le_one (by exact_mod_cast hT)).mpr (by exact_mod_cast ht)⟩]
  field_simp

/-- Equal observed prefixes have equal first-contact sublevel events before the horizon. -/
theorem intervalTouchTime_le_iff_of_prefix_eq {Ω Ξ : Type*}
    {B : ℝ≥0 → Ω → ℝ} {C : ℝ≥0 → Ξ → ℝ} {ω : Ω} {ξ : Ξ}
    (hB : Continuous (B · ω)) (hC : Continuous (C · ξ)) {x r : ℝ} (hr : 0 < r)
    {T U : ℝ≥0} (hUT : U ≤ T) (he : ∀ t : ℝ≥0, t ≤ T → B t ω=C t ξ) :
    intervalTouchTime B x r ω ≤ U ↔ intervalTouchTime C x r ξ ≤ U := by
  rw [intervalTouchTime_le_iff hB hr,intervalTouchTime_le_iff hC hr]
  apply exists_congr
  intro t
  apply and_congr_right
  intro ht
  rw [he t (ht.trans hUT)]

/-- A contact occurring in the observation period is determined by that prefix exactly. -/
theorem intervalTouchTime_eq_of_prefix_eq_of_le {Ω Ξ : Type*}
    {B : ℝ≥0 → Ω → ℝ} {C : ℝ≥0 → Ξ → ℝ} {ω : Ω} {ξ : Ξ}
    (hB : Continuous (B · ω)) (hC : Continuous (C · ξ)) {x r : ℝ} (hr : 0 < r)
    {T : ℝ≥0} (he : ∀ t : ℝ≥0, t ≤ T → B t ω=C t ξ)
    (hBT : intervalTouchTime B x r ω ≤ T) :
    intervalTouchTime B x r ω=intervalTouchTime C x r ξ := by
  have hBf : intervalTouchTime B x r ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hBT
  obtain ⟨s,hs⟩ := WithTop.ne_top_iff_exists.mp hBf
  have hs' : (s : ℝ≥0∞)=intervalTouchTime B x r ω := hs
  have hsT : s ≤ T := by rw [← hs'] at hBT; exact_mod_cast hBT
  have hCs : intervalTouchTime C x r ξ ≤ s :=
    (intervalTouchTime_le_iff_of_prefix_eq hB hC hr hsT he).mp hs'.symm.le
  have hCf : intervalTouchTime C x r ξ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hCs
  obtain ⟨u,hu⟩ := WithTop.ne_top_iff_exists.mp hCf
  have hu' : (u : ℝ≥0∞)=intervalTouchTime C x r ξ := hu
  have hus : u ≤ s := by rw [← hu'] at hCs; exact_mod_cast hCs
  have hBu : intervalTouchTime B x r ω ≤ u :=
    (intervalTouchTime_le_iff_of_prefix_eq hB hC hr (hus.trans hsT) he).mpr hu'.symm.le
  exact le_antisymm (hBu.trans_eq hu') (hCs.trans_eq hs')

/-- First contact within the observed horizon is an actual measurable path-space reading. -/
theorem observedIntervalTouch_actual_of_le {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (B · ω)) {T : ℝ≥0} (hT : 0 < T) {x r : ℝ} (hr : 0 < r)
    (hτ : intervalTouchTime B x r ω ≤ T) :
    intervalTouchTime (observedProcess T) x r (unitPath (processPath B ω) T)=
      intervalTouchTime B x r ω := by
  have hobs : Continuous (observedProcess T · (unitPath (processPath B ω) T)) :=
    (observedPath T (unitPath (processPath B ω) T)).continuous.comp NNReal.continuous_coe
  exact (intervalTouchTime_eq_of_prefix_eq_of_le (B := B) (C := observedProcess T)
    (ω := ω) (ξ := unitPath (processPath B ω) T) hc hobs hr
    (fun t ht => (observedProcess_actual_prefix hc hT ht).symm) hτ).symm

theorem observedIntervalClock_actual_of_le {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (B · ω)) {T : ℝ≥0} (hT : 0 < T) {x r : ℝ} (hr : 0 < r)
    (hτ : intervalTouchTime B x r ω ≤ T) :
    intervalTouchClock (observedProcess T) x r (unitPath (processPath B ω) T)=
      intervalTouchClock B x r ω := by
  rw [intervalTouchClock,observedIntervalTouch_actual_of_le hc hT hr hτ]
  rfl

end BrownianAffine
