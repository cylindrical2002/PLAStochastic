import PLAStochastic.ForMathlib.Analysis.Complex.PartialDeriv

/-! # Spatial derivatives of jointly holomorphic families -/

noncomputable section
open Complex Set Metric
namespace PGM

theorem cepsNormal_differentiableOn_spatial_deriv {U : Set ℂ} (hU : IsOpen U) {R : ℝ}
    {G : ℂ → ℂ → ℂ}
    (hG : DifferentiableOn ℂ (fun x : ℂ × ℂ => G x.1 x.2) (U ×ˢ ball 0 R)) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => deriv (G x.1) x.2) (U ×ˢ ball 0 R) := by
  have hp : DifferentiableOn ℂ (fun x : ℂ × ℂ => (x.2, x.1)) (ball 0 R ×ˢ U) :=
    by fun_prop
  have hswap : DifferentiableOn ℂ (fun x : ℂ × ℂ => G x.2 x.1) (ball 0 R ×ˢ U) :=
    hG.comp (f := fun x : ℂ × ℂ => (x.2, x.1)) hp (fun _ hx => ⟨hx.2, hx.1⟩)
  have hd := differentiableOn_deriv_fst (isOpen_ball.prod hU) hswap
  have hp' : DifferentiableOn ℂ (fun x : ℂ × ℂ => (x.2, x.1)) (U ×ˢ ball 0 R) :=
    by fun_prop
  exact hd.comp (f := fun x : ℂ × ℂ => (x.2, x.1)) hp' (fun _ hx => ⟨hx.2, hx.1⟩)

end PGM
