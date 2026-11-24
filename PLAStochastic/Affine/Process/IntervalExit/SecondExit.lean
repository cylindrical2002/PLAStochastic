import PLAStochastic.Affine.Process.IntervalExit.ObservedTouch
import PLAStochastic.Affine.Process.IntervalExit.TimeWindow

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- The second exit is observed in the remaining portion of the first future path. -/
def newSurvivalPathSet (T : ℝ≥0) (x r R : ℝ) (S D : Set ℝ) : Set (ℝ × Path 1) :=
  {p | ((((T-Real.toNNReal p.1 : ℝ≥0) : ℝ≥0∞) <
      intervalTouchTime (observedProcess T) x R p.2 ∧
    intervalTouchTime (observedProcess T) x r p.2 ≤ (T-Real.toNNReal p.1 : ℝ≥0) ∧
    x+observedProcess T (T-Real.toNNReal p.1) p.2 ∈ S)) ∧
    (intervalTouchClock (observedProcess T) x r p.2 : ℝ) ∈ D}

theorem measurableSet_newSurvivalPathSet (T : ℝ≥0) (x : ℝ) {r R : ℝ}
    (hr : 0 < r) (hR : 0 < R) {S D : Set ℝ} (hS : MeasurableSet S) (hD : MeasurableSet D) :
    MeasurableSet (newSurvivalPathSet T x r R S D) := by
  have hU : Measurable (fun p : ℝ × Path 1 => T-Real.toNNReal p.1) := by fun_prop
  have hτR : Measurable (fun p : ℝ × Path 1 => intervalTouchTime (observedProcess T) x R p.2) := (measurable_observedIntervalTouch (T : ℝ) x hR).comp measurable_snd
  have hτr : Measurable (fun p : ℝ × Path 1 => intervalTouchTime (observedProcess T) x r p.2) := (measurable_observedIntervalTouch (T : ℝ) x hr).comp measurable_snd
  have he : Measurable (fun p : ℝ × Path 1 => x+observedProcess T (T-Real.toNNReal p.1) p.2) := measurable_const.add ((continuous_observedPath_eval (T : ℝ)).measurable.comp
    (measurable_snd.prodMk hU.coe_nnreal_real))
  exact ((measurableSet_lt hU.coe_nnreal_ennreal hτR).inter
    ((measurableSet_le hτr hU.coe_nnreal_ennreal).inter (hS.preimage he))).inter
      (hD.preimage ((measurable_observedIntervalClock (T : ℝ) x hr).coe_nnreal_real.comp measurable_snd))

/-- Before the observation horizon, the path-space first-contact sublevel is exact. -/
theorem observedIntervalTouch_le_iff_actual {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (B · ω)) {T : ℝ≥0} (hT : 0 < T) {x r : ℝ} (hr : 0 < r)
    {U : ℝ≥0} (hUT : U ≤ T) :
    intervalTouchTime (observedProcess T) x r (unitPath (processPath B ω) T) ≤ U ↔
      intervalTouchTime B x r ω ≤ U := by
  have hobs : Continuous (observedProcess T · (unitPath (processPath B ω) T)) :=
    (observedPath T (unitPath (processPath B ω) T)).continuous.comp NNReal.continuous_coe
  exact intervalTouchTime_le_iff_of_prefix_eq (B := observedProcess T) (C := B)
    (ω := unitPath (processPath B ω) T) (ξ := ω) hobs hc hr hUT
    (fun t ht => observedProcess_actual_prefix hc hT ht)

/-- All remaining-time, second-contact, and endpoint conditions agree with the
actual process, simultaneously for every possible first exit time. -/
theorem newSurvivalPathSet_actual_iff {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (B · ω)) {T : ℝ≥0} (hT : 0 < T) (x : ℝ)
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (S D : Set ℝ) (s : ℝ) :
    (s,unitPath (processPath B ω) T) ∈ newSurvivalPathSet T x r R S D ↔
      ((((T-Real.toNNReal s : ℝ≥0) : ℝ≥0∞) < intervalTouchTime B x R ω ∧
        intervalTouchTime B x r ω ≤ (T-Real.toNNReal s : ℝ≥0) ∧
        x+B (T-Real.toNNReal s) ω ∈ S)) ∧
        (intervalTouchClock B x r ω : ℝ) ∈ D := by
  have hUT : T-Real.toNNReal s ≤ T := tsub_le_self
  have hleR := observedIntervalTouch_le_iff_actual hc hT hR hUT (x := x)
  have hler := observedIntervalTouch_le_iff_actual hc hT hr hUT (x := x)
  have hgtR : (((T-Real.toNNReal s : ℝ≥0) : ℝ≥0∞) <
      intervalTouchTime (observedProcess T) x R (unitPath (processPath B ω) T)) ↔
      (((T-Real.toNNReal s : ℝ≥0) : ℝ≥0∞) < intervalTouchTime B x R ω) := by
    simpa only [not_le] using not_congr hleR
  dsimp only [newSurvivalPathSet,mem_ofPred_eq,Prod.fst,Prod.snd]
  rw [hgtR,hler,observedProcess_actual_prefix hc hT hUT]
  apply and_congr_right
  rintro ⟨_,ht,_⟩
  rw [observedIntervalClock_actual_of_le hc hT hr (ht.trans (by exact_mod_cast hUT))]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The measurable second-exit path test has its actual upper-boundary convolution law. -/
theorem measure_newSurvivalPathSet_eq_convolution (hB : IsBrownianReal B μ)
    {x r R : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) (hrR : r < R)
    {T : ℝ≥0} (hT : 0 < T) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (T : ℝ))
    {S D : Set ℝ} (hS : MeasurableSet S) (hD : MeasurableSet D) :
    μ {ω | (s,unitPath (processPath B ω) T) ∈ newSurvivalPathSet T x r R S D} =
      ∫⁻ v in D ∩ Ioo (0 : ℝ) ((T-Real.toNNReal s : ℝ≥0) : ℝ),
        ENNReal.ofReal (heatBoundaryRight r v x/2)*
          killedBrownianMeasure B μ r R ((T-Real.toNNReal s)-Real.toNNReal v) S := by
  have hsN : Real.toNNReal s < T := by
    exact_mod_cast (show (Real.toNNReal s : ℝ) < (T : ℝ) by
      rw [Real.coe_toNNReal _ hs.1.le]
      exact hs.2)
  rw [← measure_new_survival_timeSet_eq_killed_convolution hB hr hx hrR
    (tsub_pos_iff_lt.mpr hsN) hS hD]
  apply measure_congr
  filter_upwards [hB.cont] with ω hc
  exact propext (newSurvivalPathSet_actual_iff hc hT x hr (hr.trans hrR) S D s)

end BrownianAffine
