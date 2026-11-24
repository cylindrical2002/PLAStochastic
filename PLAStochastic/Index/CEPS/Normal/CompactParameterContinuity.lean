import PLAStochastic.Index.CEPS.Normal.ParameterIntegral

/-! # Continuous compact integrals with arbitrary finite parameters -/

noncomputable section
open Complex Set Metric Filter Topology MeasureTheory
namespace PGM

theorem cepsNormal_continuousOn_parameterIntegral_general
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {U : Set E} (hU : IsOpen U) {F : E → ℝ → ℂ}
    (hc : ContinuousOn (fun x : E × ℝ => F x.1 x.2) (U ×ˢ Icc 0 1)) :
    ContinuousOn (fun x => ∫ s in (0 : ℝ)..1, F x s) U := by
  intro x hx
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x hx
  let R := ε / 2
  have hR : 0 < R := by dsimp [R]; positivity
  have hsub : closedBall x R ⊆ U :=
    (closedBall_subset_ball (by dsimp [R]; linarith)).trans hεU
  have hcompact := (isCompact_closedBall x R).prod
    (isCompact_Icc (a := (0 : ℝ)) (b := 1))
  obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuousOn
    (hc.mono (fun y hy => ⟨hsub hy.1, hy.2⟩))
  apply ContinuousAt.continuousWithinAt
  refine intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => M)
    ?_ ?_ intervalIntegrable_const ?_
  · filter_upwards [Metric.ball_mem_nhds x hR] with y hy
    have hyU := hsub (ball_subset_closedBall hy)
    rw [uIoc_of_le zero_le_one]
    exact ((hc.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs => ⟨hyU, hs⟩)).mono Ioc_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioc
  · filter_upwards [Metric.ball_mem_nhds x hR] with y hy
    refine Eventually.of_forall fun s hs => ?_
    rw [uIoc_of_le zero_le_one] at hs
    exact hM (y, s) ⟨ball_subset_closedBall hy, Ioc_subset_Icc_self hs⟩
  · refine Eventually.of_forall fun s hs => ?_
    rw [uIoc_of_le zero_le_one] at hs
    have hs' := Ioc_subset_Icc_self hs
    have hslice : ContinuousOn (fun y => F y s) U :=
      hc.comp (continuous_id.prodMk continuous_const).continuousOn (fun y hy => ⟨hy, hs'⟩)
    exact hslice.continuousAt (hU.mem_nhds hx)

end PGM
