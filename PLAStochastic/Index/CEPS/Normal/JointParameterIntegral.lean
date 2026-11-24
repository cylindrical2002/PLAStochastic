import PLAStochastic.Index.CEPS.Normal.ParameterIntegral

/-! # Joint complex differentiability of compact parameter integrals -/

noncomputable section
open Complex Set Metric Filter Topology MeasureTheory
namespace PGM

theorem cepsNormal_continuousOn_joint_parameterIntegral
    {U : Set (ℂ × ℂ)} (hU : IsOpen U) {F : (ℂ × ℂ) → ℝ → ℂ}
    (hc : ContinuousOn (fun x : (ℂ × ℂ) × ℝ => F x.1 x.2) (U ×ˢ Icc 0 1)) :
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

theorem cepsNormal_differentiableOn_joint_parameterIntegral
    {U : Set (ℂ × ℂ)} (hU : IsOpen U) {F : (ℂ × ℂ) → ℝ → ℂ}
    (hc : ContinuousOn (fun x : (ℂ × ℂ) × ℝ => F x.1 x.2) (U ×ˢ Icc 0 1))
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, DifferentiableOn ℂ (fun x => F x s) U) :
    DifferentiableOn ℂ (fun x => ∫ s in (0 : ℝ)..1, F x s) U := by
  refine osgood hU (cepsNormal_continuousOn_joint_parameterIntegral hU hc) ?_ ?_
  · intro x hx
    let V : Set ℂ := {z | (z, x.2) ∈ U}
    have hV : IsOpen V := hU.preimage (continuous_id.prodMk continuous_const)
    have hp : ContinuousOn (fun y : ℂ × ℝ => ((y.1, x.2), y.2)) (V ×ˢ Icc 0 1) :=
      by fun_prop
    have hcV : ContinuousOn (fun y : ℂ × ℝ => F (y.1, x.2) y.2) (V ×ˢ Icc 0 1) :=
      hc.comp hp (fun _ hy => ⟨hy.1, hy.2⟩)
    have hdV : ∀ s ∈ Icc (0 : ℝ) 1, DifferentiableOn ℂ (fun z => F (z, x.2) s) V := by
      intro s hs
      exact (hd s hs).comp (differentiableOn_id.prodMk (differentiableOn_const x.2))
        (fun z hz => hz)
    exact ((cepsNormal_differentiableOn_parameterIntegral hV hcV hdV) x.1 hx).differentiableAt
      (hV.mem_nhds hx)
  · intro x hx
    let V : Set ℂ := {z | (x.1, z) ∈ U}
    have hV : IsOpen V := hU.preimage (continuous_const.prodMk continuous_id)
    have hp : ContinuousOn (fun y : ℂ × ℝ => ((x.1, y.1), y.2)) (V ×ˢ Icc 0 1) :=
      by fun_prop
    have hcV : ContinuousOn (fun y : ℂ × ℝ => F (x.1, y.1) y.2) (V ×ˢ Icc 0 1) :=
      hc.comp hp (fun _ hy => ⟨hy.1, hy.2⟩)
    have hdV : ∀ s ∈ Icc (0 : ℝ) 1, DifferentiableOn ℂ (fun z => F (x.1, z) s) V := by
      intro s hs
      exact (hd s hs).comp ((differentiableOn_const x.1).prodMk differentiableOn_id)
        (fun z hz => hz)
    exact ((cepsNormal_differentiableOn_parameterIntegral hV hcV hdV) x.2 hx).differentiableAt
      (hV.mem_nhds hx)

end PGM
