import PLAStochastic.Index.CEPS.Normal.MovingSecondSlope
import PLAStochastic.Index.CEPS.Normal.JointParameterIntegral

/-! # Joint holomorphy of divided differences with moving base points

The segment-integral formula includes the diagonal value. Iteration provides
joint parameter/spatial complex differentiability at merged roots as well.
-/

noncomputable section
open Complex Set Metric
namespace PGM

theorem cepsNormal_differentiableOn_joint_moving_dslope
    {U : Set ℂ} (hU : IsOpen U) {G : ℂ → ℂ → ℂ} {R : ℝ}
    (hG : ∀ r ∈ U, DifferentiableOn ℂ (G r) (ball 0 R))
    (hGζ : DifferentiableOn ℂ (fun x : ℂ × ℂ => deriv (G x.1) x.2) (U ×ˢ ball 0 R))
    {a : ℂ → ℂ} (ha : DifferentiableOn ℂ a U)
    (hamap : MapsTo a U (ball 0 R)) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => dslope (G x.1) (a x.1) x.2)
      (U ×ˢ ball 0 R) := by
  let F : (ℂ × ℂ) → ℝ → ℂ := fun x s =>
    deriv (G x.1) (a x.1 + (s : ℂ) * (x.2 - a x.1))
  have hmap : ∀ y : (ℂ × ℂ) × ℝ, y ∈ (U ×ˢ ball (0 : ℂ) R) ×ˢ Icc 0 1 →
      (y.1.1, a y.1.1 + (y.2 : ℂ) * (y.1.2 - a y.1.1)) ∈ U ×ˢ ball 0 R :=
    fun y hy => ⟨hy.1.1, cepsNormal_segment_mem_ball (hamap hy.1.1) hy.1.2 hy.2⟩
  have hca : ContinuousOn (fun y : (ℂ × ℂ) × ℝ => a y.1.1)
      ((U ×ˢ ball 0 R) ×ˢ Icc 0 1) :=
    ha.continuousOn.comp (by fun_prop) (fun _ hy => hy.1.1)
  have hcs : ContinuousOn (fun y : (ℂ × ℂ) × ℝ => (y.2 : ℂ))
      ((U ×ˢ ball 0 R) ×ˢ Icc 0 1) := by fun_prop
  have hcb : ContinuousOn (fun y : (ℂ × ℂ) × ℝ => y.1.2)
      ((U ×ˢ ball 0 R) ×ˢ Icc 0 1) := by fun_prop
  have hpath : ContinuousOn (fun y : (ℂ × ℂ) × ℝ =>
      (y.1.1, a y.1.1 + (y.2 : ℂ) * (y.1.2 - a y.1.1)))
      ((U ×ˢ ball 0 R) ×ˢ Icc 0 1) :=
    (by fun_prop : ContinuousOn (fun y : (ℂ × ℂ) × ℝ => y.1.1) _).prodMk
      (hca.add (hcs.mul (hcb.sub hca)))
  have hcF : ContinuousOn (fun y : (ℂ × ℂ) × ℝ => F y.1 y.2)
      ((U ×ˢ ball 0 R) ×ˢ Icc 0 1) := hGζ.continuousOn.comp hpath hmap
  have hdF : ∀ s ∈ Icc (0 : ℝ) 1,
      DifferentiableOn ℂ (fun x => F x s) (U ×ˢ ball 0 R) := by
    intro s hs
    have ha' : DifferentiableOn ℂ (fun x : ℂ × ℂ => a x.1) (U ×ˢ ball 0 R) :=
      ha.comp differentiableOn_fst (fun _ hx => hx.1)
    have hp := differentiableOn_fst.prodMk
      (ha'.add ((differentiableOn_snd.sub ha').const_mul (s : ℂ)))
    exact hGζ.comp hp (fun x hx =>
      ⟨hx.1, cepsNormal_segment_mem_ball (hamap hx.1) hx.2 hs⟩)
  have hI := cepsNormal_differentiableOn_joint_parameterIntegral
    (hU.prod isOpen_ball) hcF hdF
  apply hI.congr
  intro x hx
  exact cepsNormal_dslope_eq_integral (hG x.1 hx.1) (hamap hx.1) hx.2

theorem cepsNormal_joint_moving_dslope_of_analytic
    {U : Set ℂ} (hU : IsOpen U) {R : ℝ} {G : ℂ → ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ (fun x : ℂ × ℂ => G x.1 x.2) (U ×ˢ ball 0 R))
    {a : ℂ → ℂ} (ha : DifferentiableOn ℂ a U) (hamap : MapsTo a U (ball 0 R)) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => dslope (G x.1) (a x.1) x.2)
      (U ×ˢ ball 0 R) :=
  cepsNormal_differentiableOn_joint_moving_dslope hU
    (fun r hr z hz => (hG (r, z) ⟨hr, hz⟩).curry_right.differentiableAt.differentiableWithinAt)
    (cepsNormal_analyticOnNhd_spatial_deriv hU hG).differentiableOn ha hamap

theorem cepsNormal_differentiableOn_joint_moving_second_dslope
    {U : Set ℂ} (hU : IsOpen U) {R : ℝ} {G : ℂ → ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ (fun x : ℂ × ℂ => G x.1 x.2) (U ×ˢ ball 0 R))
    {a b : ℂ → ℂ} (ha : DifferentiableOn ℂ a U) (hb : DifferentiableOn ℂ b U)
    (hamap : MapsTo a U (ball 0 R)) (hbmap : MapsTo b U (ball 0 R)) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => dslope (dslope (G x.1) (a x.1)) (b x.1) x.2)
      (U ×ˢ ball 0 R) := by
  have hs : ∀ r ∈ U, DifferentiableOn ℂ (G r) (ball 0 R) := fun r hr z hz =>
    (hG (r, z) ⟨hr, hz⟩).curry_right.differentiableAt.differentiableWithinAt
  have hGζ := cepsNormal_analyticOnNhd_spatial_deriv hU hG
  have hGζζ := cepsNormal_analyticOnNhd_spatial_deriv (G := fun r => deriv (G r)) hU hGζ
  have hI : DifferentiableOn ℂ
      (fun x : ℂ × ℂ => ∫ s in (0 : ℝ)..1,
        (s : ℂ) * deriv (deriv (G x.1)) (a x.1 + (s : ℂ) * (x.2 - a x.1)))
      (U ×ˢ ball 0 R) := by
    intro x hx
    exact (cepsNormal_hasFDerivAt_weighted_segmentIntegral (D := fun x : ℂ × ℂ =>
      deriv (deriv (G x.1)) x.2) hU hGζζ (ha.analyticOnNhd hU) hamap
      (by fun_prop : ContinuousOn (fun s : ℝ => (s : ℂ)) (Icc 0 1)) hx).differentiableAt.differentiableWithinAt
  have hHζ : DifferentiableOn ℂ
      (fun x : ℂ × ℂ => deriv (dslope (G x.1) (a x.1)) x.2) (U ×ˢ ball 0 R) := by
    apply hI.congr
    intro x hx
    exact cepsNormal_deriv_dslope_eq_integral (hs x.1 hx.1) (hamap hx.1) hx.2
  have hH : ∀ r ∈ U, DifferentiableOn ℂ (dslope (G r) (a r)) (ball 0 R) := by
    intro r hr
    exact (differentiableOn_dslope (isOpen_ball.mem_nhds (hamap hr))).mpr (hs r hr)
  exact cepsNormal_differentiableOn_joint_moving_dslope hU hH hHζ hb hbmap

end PGM
