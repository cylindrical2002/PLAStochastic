import PLAStochastic.Index.CEPS.Normal.MovingHolomorphicSlope
import PLAStochastic.ForMathlib.Analysis.Complex.AnalyticCurve

/-! # Analyticity at arbitrary moving nodes from joint holomorphic spatial germs -/

noncomputable section
open Complex Set Metric Filter Topology
namespace PGM

theorem cepsNormal_moving_dslope_analyticAt_of_differentiableOn {G : ℂ → ℂ → ℂ} {B R : ℝ}
    (hB : 0 < B) (hG : DifferentiableOn ℂ (fun x : ℂ × ℂ => G x.1 x.2)
      (ball 0 B ×ˢ ball 0 R)) {a t : ℂ → ℂ}
    (ha : AnalyticAt ℂ a 0) (ht : AnalyticAt ℂ t 0)
    (ha0 : a 0 ∈ ball 0 R) (ht0 : t 0 ∈ ball 0 R) :
    AnalyticAt ℂ (fun b => dslope (G b) (a b) (t b)) 0 := by
  have hBmem : ∀ᶠ b : ℂ in 𝓝 0, b ∈ ball (0 : ℂ) B := ball_mem_nhds _ hB
  have hev := hBmem.and ((analyticAt_iff_eventually_differentiableAt.mp ha).and
    (ha.continuousAt.eventually (isOpen_ball.mem_nhds ha0)))
  obtain ⟨C, hC, hball⟩ := Metric.mem_nhds_iff.mp hev
  have hGC := hG.mono (fun x (hx : x ∈ ball (0 : ℂ) C ×ˢ ball (0 : ℂ) R) =>
    ⟨(hball hx.1).1, hx.2⟩)
  have hS := cepsNormal_joint_moving_dslope_of_differentiable isOpen_ball hGC
    (fun b hb => (hball hb).2.1.differentiableWithinAt) (fun b hb => (hball hb).2.2)
  exact analyticAt_complex_curve_of_differentiableOn
    (F := fun x : ℂ × ℂ => dslope (G x.1) (a x.1) x.2)
    (a := fun b : ℂ => (b, t b)) (isOpen_ball.prod isOpen_ball) hS
    (analyticAt_id.prod ht) ⟨mem_ball_self hC, ht0⟩

theorem cepsNormal_moving_second_dslope_analyticAt_of_differentiableOn {G : ℂ → ℂ → ℂ} {B R : ℝ}
    (hB : 0 < B) (hG : DifferentiableOn ℂ (fun x : ℂ × ℂ => G x.1 x.2)
      (ball 0 B ×ˢ ball 0 R)) {a d t : ℂ → ℂ}
    (ha : AnalyticAt ℂ a 0) (hd : AnalyticAt ℂ d 0) (ht : AnalyticAt ℂ t 0)
    (ha0 : a 0 ∈ ball 0 R) (hd0 : d 0 ∈ ball 0 R) (ht0 : t 0 ∈ ball 0 R) :
    AnalyticAt ℂ (fun b => dslope (dslope (G b) (a b)) (d b) (t b)) 0 := by
  have hBmem : ∀ᶠ b : ℂ in 𝓝 0, b ∈ ball (0 : ℂ) B := ball_mem_nhds _ hB
  have hev := hBmem.and ((analyticAt_iff_eventually_differentiableAt.mp ha).and
    ((analyticAt_iff_eventually_differentiableAt.mp hd).and
      ((ha.continuousAt.eventually (isOpen_ball.mem_nhds ha0)).and
        (hd.continuousAt.eventually (isOpen_ball.mem_nhds hd0)))))
  obtain ⟨C, hC, hball⟩ := Metric.mem_nhds_iff.mp hev
  have hGC := hG.mono (fun x (hx : x ∈ ball (0 : ℂ) C ×ˢ ball (0 : ℂ) R) =>
    ⟨(hball hx.1).1, hx.2⟩)
  have hS := cepsNormal_joint_moving_second_dslope_of_differentiable isOpen_ball hGC
    (fun b hb => (hball hb).2.1.differentiableWithinAt)
    (fun b hb => (hball hb).2.2.1.differentiableWithinAt)
    (fun b hb => (hball hb).2.2.2.1) (fun b hb => (hball hb).2.2.2.2)
  exact analyticAt_complex_curve_of_differentiableOn
    (F := fun x : ℂ × ℂ => dslope (dslope (G x.1) (a x.1)) (d x.1) x.2)
    (a := fun b : ℂ => (b, t b)) (isOpen_ball.prod isOpen_ball) hS
    (analyticAt_id.prod ht) ⟨mem_ball_self hC, ht0⟩

end PGM
