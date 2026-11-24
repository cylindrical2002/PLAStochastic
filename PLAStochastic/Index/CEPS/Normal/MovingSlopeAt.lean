import PLAStochastic.Index.CEPS.Normal.MovingSlopeContinuity
import PLAStochastic.ForMathlib.Analysis.Complex.TaylorSeriesCongr

/-! # Continuity of moving divided differences for analytic germs -/

noncomputable section
open Complex Set Metric Filter Topology
namespace PGM

set_option maxHeartbeats 250000 in
theorem cepsNormal_continuousAt_moving_dslope_of_analyticAt {H a b : ℂ → ℂ}
    (hH : AnalyticAt ℂ H 0) (ha : AnalyticAt ℂ a 0) (hb : AnalyticAt ℂ b 0)
    (ha0 : a 0 = 0) (hb0 : b 0 = 0) :
    ContinuousAt (fun u : ℂ => dslope H (a u) (b u)) 0 := by
  have heH : ∀ᶠ u : ℂ in 𝓝 (0 : ℂ), DifferentiableAt ℂ H u :=
    analyticAt_iff_eventually_differentiableAt.mp hH
  obtain ⟨R, hR, hHR⟩ := Metric.mem_nhds_iff.mp heH
  have h0R : (0 : ℂ) ∈ ball (0 : ℂ) R := mem_ball_self hR
  have hamap : ∀ᶠ u : ℂ in 𝓝 0, a u ∈ ball (0 : ℂ) R :=
    ha.continuousAt.eventually (by rw [ha0]; exact isOpen_ball.mem_nhds h0R)
  have hbmap : ∀ᶠ u : ℂ in 𝓝 0, b u ∈ ball (0 : ℂ) R :=
    hb.continuousAt.eventually (by rw [hb0]; exact isOpen_ball.mem_nhds h0R)
  have hev : ∀ᶠ u : ℂ in 𝓝 (0 : ℂ), DifferentiableAt ℂ a u ∧
      DifferentiableAt ℂ b u ∧ a u ∈ ball (0 : ℂ) R ∧ b u ∈ ball (0 : ℂ) R :=
    (analyticAt_iff_eventually_differentiableAt.mp ha).and
      ((analyticAt_iff_eventually_differentiableAt.mp hb).and (hamap.and hbmap))
  obtain ⟨B, hB, hball⟩ := Metric.mem_nhds_iff.mp hev
  have hdH : DifferentiableOn ℂ H (ball 0 R) := fun u hu => (hHR hu).differentiableWithinAt
  have hca : ContinuousOn a (ball 0 B) :=
    (show DifferentiableOn ℂ a (ball 0 B) from fun u hu => (hball hu).1.differentiableWithinAt).continuousOn
  have hcH : ContinuousOn (fun x : ℂ × ℂ => H x.2) (ball 0 B ×ˢ ball 0 R) :=
    hdH.continuousOn.comp continuousOn_snd (fun _ hx => hx.2)
  have hds := cepsNormal_continuousOn_joint_moving_dslope_general (E := ℂ)
    (U := ball (0 : ℂ) B) (R := R) (G := fun _ => H) (a := a) isOpen_ball hcH
    (fun _ _ => hdH) hca (fun _ hu => (hball hu).2.2.1)
  have hmem : ((0 : ℂ), (0 : ℂ)) ∈ ball 0 B ×ˢ ball 0 R := ⟨mem_ball_self hB, h0R⟩
  have hat : ContinuousAt (fun x : ℂ × ℂ => dslope H (a x.1) x.2) (0, 0) :=
    hds.continuousAt ((isOpen_ball.prod isOpen_ball).mem_nhds hmem)
  have hcurve : ContinuousAt (fun u : ℂ => (u, b u)) 0 :=
    continuousAt_id.prodMk hb.continuousAt
  have he : ((0 : ℂ), b 0) = ((0 : ℂ), (0 : ℂ)) := by rw [hb0]
  simpa only [Function.comp_apply] using!
    hat.comp_of_eq (f := fun u : ℂ => (u, b u)) hcurve he

end PGM
