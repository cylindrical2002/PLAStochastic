import PLAStochastic.Index.CEPS.Normal.MovingSecondSlope
import PLAStochastic.ForMathlib.Analysis.Complex.TaylorSeriesCongr

/-! # Analyticity of moving divided differences for analytic germs -/

noncomputable section
open Complex Set Metric Filter Topology
namespace PGM

theorem cepsNormal_analyticAt_moving_dslope_of_analyticAt {H a b : ℂ → ℂ}
    (hH : AnalyticAt ℂ H 0) (ha : AnalyticAt ℂ a 0) (hb : AnalyticAt ℂ b 0)
    (ha0 : a 0 = 0) (hb0 : b 0 = 0) :
    AnalyticAt ℂ (fun u : ℂ => dslope H (a u) (b u)) 0 := by
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
  have hda : DifferentiableOn ℂ a (ball 0 B) := fun u hu => (hball hu).1.differentiableWithinAt
  have hdb : DifferentiableOn ℂ b (ball 0 B) := fun u hu => (hball hu).2.1.differentiableWithinAt
  have hGa : AnalyticOnNhd ℂ (fun x : ℂ × ℂ => H x.2) (ball 0 B ×ˢ ball 0 R) :=
    fun x hx => ((hdH.analyticOnNhd isOpen_ball) x.2 hx.2).comp analyticAt_snd
  have hds : DifferentiableOn ℂ (fun u : ℂ => dslope H (a u) (b u)) (ball 0 B) :=
    cepsNormal_moving_dslope_of_analytic (G := fun _ => H) isOpen_ball
      hGa hda hdb
      (fun _ hu => (hball hu).2.2.1) (fun _ hu => (hball hu).2.2.2)
  exact (hds.analyticOnNhd isOpen_ball) 0 (mem_ball_self hB)

end PGM
