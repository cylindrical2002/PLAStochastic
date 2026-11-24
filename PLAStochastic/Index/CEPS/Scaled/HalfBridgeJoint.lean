import PLAStochastic.Index.CEPS.Scaled.SurrogateJointSlices
import PLAStochastic.Index.CEPS.Normal.TwoParameterEvaluation
import PLAStochastic.Index.CEPS.Scaled.SurrogateBridgeCorrection

/-! # Joint scale-frequency holomorphy of the half-line bridge -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

set_option maxHeartbeats 800000 in
include hW hθ hD in
theorem cepsScaledSurrogateHalfBridge_holomorphic_near_joint {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) (hne : lam ≠ 0 ∨ z ≠ 0) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (min (dom.jointRootScaleRadius lam z)
      (dom.entranceScaleRadius N M lam z))) :
    ∃ ε > 0,
      DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledSurrogateHalfBridge dom ρW N lam x.2 x.1)
        (ball b ε ×ˢ ball z ε) ∧
      DifferentiableOn ℂ (fun x : ℂ × ℂ =>
        deriv (fun w => cepsScaledSurrogateHalfBridge dom ρW N lam w x.1) x.2)
        (ball b ε ×ˢ ball z ε) := by
  obtain ⟨δ, hδ, hroots, hbounds⟩ := cepsScaled_joint_root_chart dom hW hθ hD N M lam hz hne hb
  let S := dom.entranceSpatialScaleRadius lam z
  have hp := hroots 1 (by norm_num)
  have hm := hroots (-1) (by norm_num)
  have hgbounds : ∀ x ∈ ball b δ ×ˢ ball z δ,
      ‖x.1 * (lam : ℂ)‖ < dom.μ₀ ∧
      ‖x.1 * cepsScaledRootCoordinate D θ ρW lam x.2 x.1‖ < dom.rmax ∧
      ‖cepsComplexScaledDiscount lam x.2 x.1‖ < dom.q₀ / 2 ∧ ‖x.1‖ * S < dom.c₀ / 2 ∧
      cepsScaledSignedRoot D θ ρW lam x.2 1 x.1 ∈ ball 0 S ∧
      cepsScaledSignedRoot D θ ρW lam x.2 (-1) x.1 ∈ ball 0 S := by
    intro x hx
    obtain ⟨h1, h2, h3, h4, h5, h6, _⟩ := hbounds x hx
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  obtain ⟨hcG, hG₁, hG₂⟩ := cepsScaledSurrogateG_joint_on_root_chart dom hW hθ hD hf hη N hN lam
    isOpen_ball isOpen_ball hp hm hgbounds
  have hpmap : MapsTo (fun x : ℂ × ℂ => cepsScaledSignedRoot D θ ρW lam x.2 1 x.1)
      (ball b δ ×ˢ ball z δ) (ball 0 S) := fun x hx => (hbounds x hx).2.2.2.2.1
  have hpG := cepsNormal_differentiableOn_two_parameter_eval
    (G := fun x ξ => cepsScaledSurrogateG dom ρW N lam x.2 x.1 ξ)
    (a := fun x => cepsScaledSignedRoot D θ ρW lam x.2 1 x.1)
    isOpen_ball isOpen_ball hcG hG₁ hG₂ hp hpmap
  have hB : DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledSurrogateHalfBridge dom ρW N lam x.2 x.1)
      (ball b δ ×ˢ ball z δ) := (hp.sub hm).mul hpG
  have hs : DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledSurrogateHalfBridge dom ρW N lam x.1 x.2)
      (ball z δ ×ˢ ball b δ) := hB.comp (f := fun x : ℂ × ℂ => (x.2, x.1))
        (differentiableOn_snd.prodMk differentiableOn_fst) (fun x hx => ⟨hx.2, hx.1⟩)
  refine ⟨δ, hδ, hB, ?_⟩
  exact (differentiableOn_deriv_fst (isOpen_ball.prod isOpen_ball) hs).comp
    (f := fun x : ℂ × ℂ => (x.2, x.1)) (differentiableOn_snd.prodMk differentiableOn_fst)
      (fun x hx => ⟨hx.2, hx.1⟩)

end PGM
