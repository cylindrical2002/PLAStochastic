import PLAStochastic.Index.CEPS.Normal.SlopeDerivative
import Mathlib.Analysis.Complex.RemovableSingularity
import PLAStochastic.ForMathlib.Analysis.Complex.CompactSpatialDeriv

/-! # Joint analytic moving slopes from genuine continuous-function lifts -/

noncomputable section
open Complex Set Metric Filter Topology MeasureTheory
namespace PGM

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def unitSegmentComplexCoord : C(UnitSegment, ℂ) := ⟨fun s => (s.val : ℂ), by fun_prop⟩

theorem dslope_entire_eq_integral {f : ℂ → ℂ} (hf : Differentiable ℂ f) (a b : ℂ) :
    dslope f a b = ∫ s in (0 : ℝ)..1, deriv f (a + (s : ℂ) * (b - a)) := by
  let R : ℝ := 1 + ‖a‖ + ‖b‖
  exact cepsNormal_dslope_eq_integral (R := R) hf.differentiableOn
    (mem_ball_zero_iff.mpr (by dsimp [R]; linarith [norm_nonneg b]))
    (mem_ball_zero_iff.mpr (by dsimp [R]; linarith [norm_nonneg a]))

theorem second_dslope_entire_eq_integral {f : ℂ → ℂ} (hf : Differentiable ℂ f) (a b c : ℂ) :
    dslope (dslope f a) b c = ∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1,
      (s : ℂ) * deriv (deriv f) (a + (s : ℂ) * (b + (t : ℂ) * (c - b) - a)) := by
  let R : ℝ := 1 + ‖a‖ + ‖b‖ + ‖c‖
  have ha : a ∈ ball (0 : ℂ) R := mem_ball_zero_iff.mpr (by dsimp [R]; linarith [norm_nonneg b, norm_nonneg c])
  have hb : b ∈ ball (0 : ℂ) R := mem_ball_zero_iff.mpr (by dsimp [R]; linarith [norm_nonneg a, norm_nonneg c])
  have hc : c ∈ ball (0 : ℂ) R := mem_ball_zero_iff.mpr (by dsimp [R]; linarith [norm_nonneg a, norm_nonneg b])
  have hs : Differentiable ℂ (dslope f a) := by
    have h := (differentiableOn_dslope (s := univ) (c := a) univ_mem).mpr hf.differentiableOn
    exact fun z => (h z (mem_univ z)).differentiableAt univ_mem
  rw [dslope_entire_eq_integral hs]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  exact cepsNormal_deriv_dslope_eq_integral hf.differentiableOn ha
    (cepsNormal_segment_mem_ball hb hc ht)

/-- The functional lift pays analyticity on every collision of the two moving nodes. -/
theorem analyticAt_moving_dslope_of_compact_lift {U : Set E} (hU : IsOpen U)
    {x : E} (hx : x ∈ U) {f : E → ℂ → ℂ}
    {H : E × C(UnitSegment, ℂ) → C(UnitSegment, ℂ)}
    (hH : AnalyticOnNhd ℂ H (U ×ˢ univ))
    (he : ∀ u ∈ U, ∀ X : C(UnitSegment, ℂ), ∀ s, H (u, X) s = f u (X s))
    (hf : ∀ u ∈ U, Differentiable ℂ (f u))
    {a b : E → ℂ} (ha : AnalyticAt ℂ a x) (hb : AnalyticAt ℂ b x) :
    AnalyticAt ℂ (fun u => dslope (f u) (a u) (b u)) x := by
  let X : E → C(UnitSegment, ℂ) := fun u => ContinuousMap.const _ (a u) +
    unitSegmentComplexCoord * (ContinuousMap.const _ (b u) - ContinuousMap.const _ (a u))
  have hX : AnalyticAt ℂ X x :=
    ha.continuousMap_const.add (analyticAt_const.mul (hb.continuousMap_const.sub ha.continuousMap_const))
  have hD := (compactSpatialDeriv_analyticAt (hH (x, X x) ⟨hx, mem_univ _⟩)).comp
    (x := x) (f := fun u => (u, X u)) (analyticAt_id.prod hX)
  have hI := ((unitSegmentIntegralCLM (F := ℂ)).analyticAt _).comp hD
  apply hI.congr
  filter_upwards [hU.mem_nhds hx] with u hu
  change unitSegmentIntegralCLM (compactSpatialDeriv H (u, X u)) = _
  rw [dslope_entire_eq_integral (hf u hu)]
  apply unitSegmentIntegralCLM_eq_integral
  intro s
  rw [compactSpatialDeriv_apply (hH (u, X u) ⟨hu, mem_univ _⟩) (he u hu) (hf u hu)]
  rfl

def doubleUnitSegmentInnerCoord : C(UnitSegment × UnitSegment, ℂ) :=
  ⟨fun q => (q.2.val : ℂ), by fun_prop⟩

def doubleUnitSegmentOuterCoord : C(UnitSegment × UnitSegment, ℂ) :=
  ⟨fun q => (q.1.val : ℂ), by fun_prop⟩

/-- A twice differentiated functional lift pays all collisions of three moving nodes. -/
theorem analyticAt_moving_second_dslope_of_compact_lift {U : Set E} (hU : IsOpen U)
    {x : E} (hx : x ∈ U) {f : E → ℂ → ℂ}
    {H : E × C(UnitSegment × UnitSegment, ℂ) → C(UnitSegment × UnitSegment, ℂ)}
    (hH : AnalyticOnNhd ℂ H (U ×ˢ univ))
    (he : ∀ u ∈ U, ∀ X : C(UnitSegment × UnitSegment, ℂ), ∀ s, H (u, X) s = f u (X s))
    (hf : ∀ u ∈ U, Differentiable ℂ (f u))
    {a b c : E → ℂ} (ha : AnalyticAt ℂ a x) (hb : AnalyticAt ℂ b x) (hc : AnalyticAt ℂ c x) :
    AnalyticAt ℂ (fun u => dslope (dslope (f u) (a u)) (b u) (c u)) x := by
  let X : E → C(UnitSegment × UnitSegment, ℂ) := fun u => ContinuousMap.const _ (a u) +
    doubleUnitSegmentInnerCoord * (ContinuousMap.const _ (b u) +
      doubleUnitSegmentOuterCoord * (ContinuousMap.const _ (c u) - ContinuousMap.const _ (b u)) -
        ContinuousMap.const _ (a u))
  have hX : AnalyticAt ℂ X x := ha.continuousMap_const.add (analyticAt_const.mul
    ((hb.continuousMap_const.add (analyticAt_const.mul
      (hc.continuousMap_const.sub hb.continuousMap_const))).sub ha.continuousMap_const))
  have hH' : AnalyticOnNhd ℂ (compactSpatialDeriv H) (U ×ˢ univ) :=
    fun v hv => compactSpatialDeriv_analyticAt (hH v hv)
  have he' : ∀ u ∈ U, ∀ X : C(UnitSegment × UnitSegment, ℂ), ∀ s,
      compactSpatialDeriv H (u, X) s = deriv (f u) (X s) :=
    fun u hu X s => compactSpatialDeriv_apply (hH (u, X) ⟨hu, mem_univ _⟩) (he u hu) (hf u hu) s
  have hD := (compactSpatialDeriv_analyticAt (hH' (x, X x) ⟨hx, mem_univ _⟩)).comp
    (x := x) (f := fun u => (u, X u)) (analyticAt_id.prod hX)
  have hW := (analyticAt_const (v := doubleUnitSegmentInnerCoord)).mul hD
  have hI := (doubleUnitSegmentIntegralCLM.analyticAt _).comp hW
  apply hI.congr
  filter_upwards [hU.mem_nhds hx] with u hu
  change doubleUnitSegmentIntegralCLM
    (doubleUnitSegmentInnerCoord * compactSpatialDeriv (compactSpatialDeriv H) (u, X u)) = _
  rw [second_dslope_entire_eq_integral (hf u hu)]
  apply doubleUnitSegmentIntegralCLM_eq_integral
  intro t s
  rw [ContinuousMap.mul_apply,
    compactSpatialDeriv_apply (f := fun u => deriv (f u)) (hH' (u, X u) ⟨hu, mem_univ _⟩) (he' u hu)
      ((hf u hu).deriv)]
  rfl

end PGM
