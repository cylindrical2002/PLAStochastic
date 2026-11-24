import PLAStochastic.Index.CEPS.Normal.MovingSecondSlope

/-! # Analytic moving second slopes for arbitrary local node curves -/

noncomputable section
open Complex Set Metric Filter Topology
namespace PGM

theorem cepsNormal_analyticAt_moving_second_dslope {G : ℂ → ℂ → ℂ} {B R : ℝ}
    (hB : 0 < B) (hG : AnalyticOnNhd ℂ (fun x : ℂ × ℂ => G x.1 x.2)
      (ball 0 B ×ˢ ball 0 R)) {a b t : ℂ → ℂ}
    (ha : AnalyticAt ℂ a 0) (hb : AnalyticAt ℂ b 0) (ht : AnalyticAt ℂ t 0)
    (ha0 : a 0 ∈ ball 0 R) (hb0 : b 0 ∈ ball 0 R) (ht0 : t 0 ∈ ball 0 R) :
    AnalyticAt ℂ (fun u => dslope (dslope (G u) (a u)) (b u) (t u)) 0 := by
  have hBmem : ∀ᶠ u : ℂ in 𝓝 0, u ∈ ball (0 : ℂ) B := ball_mem_nhds _ hB
  have hev : ∀ᶠ u : ℂ in 𝓝 0, u ∈ ball (0 : ℂ) B ∧
      DifferentiableAt ℂ a u ∧ DifferentiableAt ℂ b u ∧ DifferentiableAt ℂ t u ∧
      a u ∈ ball 0 R ∧ b u ∈ ball 0 R ∧ t u ∈ ball 0 R :=
    hBmem.and
      ((analyticAt_iff_eventually_differentiableAt.mp ha).and
        ((analyticAt_iff_eventually_differentiableAt.mp hb).and
          ((analyticAt_iff_eventually_differentiableAt.mp ht).and
            ((ha.continuousAt.eventually (isOpen_ball.mem_nhds ha0)).and
              ((hb.continuousAt.eventually (isOpen_ball.mem_nhds hb0)).and
                (ht.continuousAt.eventually (isOpen_ball.mem_nhds ht0)))))))
  obtain ⟨C, hC, hball⟩ := Metric.mem_nhds_iff.mp hev
  have hGC : AnalyticOnNhd ℂ (fun x : ℂ × ℂ => G x.1 x.2)
      (ball 0 C ×ˢ ball 0 R) := hG.mono (fun x hx => ⟨(hball hx.1).1, hx.2⟩)
  have hda : DifferentiableOn ℂ a (ball 0 C) := fun u hu => (hball hu).2.1.differentiableWithinAt
  have hdb : DifferentiableOn ℂ b (ball 0 C) := fun u hu => (hball hu).2.2.1.differentiableWithinAt
  have hdt : DifferentiableOn ℂ t (ball 0 C) := fun u hu => (hball hu).2.2.2.1.differentiableWithinAt
  have hd := cepsNormal_moving_second_dslope isOpen_ball hGC hda hdb hdt
    (fun _ hu => (hball hu).2.2.2.2.1)
    (fun _ hu => (hball hu).2.2.2.2.2.1)
    (fun _ hu => (hball hu).2.2.2.2.2.2)
  exact hd.analyticAt (ball_mem_nhds _ hC)

end PGM
