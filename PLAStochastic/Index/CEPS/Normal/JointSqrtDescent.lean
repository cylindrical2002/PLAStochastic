import PLAStochastic.ForMathlib.Analysis.Complex.EvenSqrtLocal
import PLAStochastic.ForMathlib.Analysis.Complex.Osgood

/-! # Joint holomorphy after square-root descent -/

noncomputable section
open Complex Set Metric
namespace PGM

theorem cepsNormal_differentiableOn_joint_comp_sqrt
    {U : Set ℂ} (hU : IsOpen U) {R : ℝ} (hR : 0 < R) {G : ℂ → ℂ → ℂ}
    (hG : DifferentiableOn ℂ (fun x : ℂ × ℂ => G x.1 x.2) (U ×ˢ ball 0 R))
    (heven : ∀ z ∈ U, ∀ r ∈ ball (0 : ℂ) R, G z (-r) = G z r) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => G x.1 (Complex.sqrt x.2))
      (U ×ˢ ball 0 (R ^ 2)) := by
  have hc := continuousOn_comp_sqrt_of_locally_even hR hG.continuousOn heven
  refine osgood (hU.prod isOpen_ball) hc ?_ ?_
  · intro x hx
    have hs : Complex.sqrt x.2 ∈ ball (0 : ℂ) R :=
      mem_ball_zero_iff.mpr (norm_sqrt_lt hR (mem_ball_zero_iff.mp hx.2))
    have hp : DifferentiableOn ℂ (fun z : ℂ => (z, Complex.sqrt x.2)) U :=
      differentiableOn_id.prodMk (differentiableOn_const _)
    exact ((hG.comp hp (fun z hz => ⟨hz, hs⟩)) x.1 hx.1).differentiableAt
      (hU.mem_nhds hx.1)
  · intro x hx
    have hp : DifferentiableOn ℂ (fun r : ℂ => (x.1, r)) (ball 0 R) :=
      (differentiableOn_const _).prodMk differentiableOn_id
    have hd : DifferentiableOn ℂ (G x.1) (ball 0 R) :=
      hG.comp hp (fun r hr => ⟨hx.1, hr⟩)
    exact ((differentiableOn_comp_sqrt_of_locally_even hR hd (heven x.1 hx.1))
      x.2 hx.2).differentiableAt (isOpen_ball.mem_nhds hx.2)

end PGM
