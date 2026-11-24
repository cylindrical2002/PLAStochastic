import PLAStochastic.Index.CEPS.Scaled.SurrogateJointSlices
import PLAStochastic.Index.CEPS.Normal.TwoParameterEvaluation
import PLAStochastic.Index.CEPS.Scaled.SurrogateBridge

/-! # Joint scale-frequency holomorphy of the surrogate bridge away from the joint origin -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

set_option maxHeartbeats 800000 in
include hW hθ hD in
theorem cepsScaledSurrogateBridge_holomorphic_near_joint {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) (hne : lam ≠ 0 ∨ z ≠ 0) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (min (dom.jointRootScaleRadius lam z)
      (dom.entranceScaleRadius N M lam z))) :
    ∃ ε > 0,
      DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledSurrogateBridge dom ρW N lam x.2 x.1)
        (ball b ε ×ˢ ball z ε) ∧
      DifferentiableOn ℂ (fun x : ℂ × ℂ =>
        deriv (fun w => cepsScaledSurrogateBridge dom ρW N lam w x.1) x.2)
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
  have hmmap : MapsTo (fun x : ℂ × ℂ => cepsScaledSignedRoot D θ ρW lam x.2 (-1) x.1)
      (ball b δ ×ˢ ball z δ) (ball 0 S) := fun x hx => (hbounds x hx).2.2.2.2.2.1
  have hd : DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledSurrogateDenominator dom ρW N lam x.2 x.1)
      (ball b δ ×ˢ ball z δ) :=
    cepsNormal_differentiableOn_two_parameter_moving_dslope
      (G := fun x ξ => cepsScaledSurrogateG dom ρW N lam x.2 x.1 ξ)
      (a := fun x => cepsScaledSignedRoot D θ ρW lam x.2 (-1) x.1)
      (b := fun x => cepsScaledSignedRoot D θ ρW lam x.2 1 x.1)
      isOpen_ball isOpen_ball hcG hG₁ hG₂ hm hp hmmap hpmap
  have hpG := cepsNormal_differentiableOn_two_parameter_eval
    (G := fun x ξ => cepsScaledSurrogateG dom ρW N lam x.2 x.1 ξ)
    (a := fun x => cepsScaledSignedRoot D θ ρW lam x.2 1 x.1)
    isOpen_ball isOpen_ball hcG hG₁ hG₂ hp hpmap
  have hmG := cepsNormal_differentiableOn_two_parameter_eval
    (G := fun x ξ => cepsScaledSurrogateG dom ρW N lam x.2 x.1 ξ)
    (a := fun x => cepsScaledSignedRoot D θ ρW lam x.2 (-1) x.1)
    isOpen_ball isOpen_ball hcG hG₁ hG₂ hm hmmap
  have hbE := ball_subset_ball (min_le_right _ _) hb
  have hbS := ball_subset_ball (min_le_left _ _) hbE
  have hneD := cepsScaledSurrogateDenominator_ne_zero dom hW hθ hD hf hη hM N hN lam hz hbS
  have hx : (b, z) ∈ ball b δ ×ˢ ball z δ := ⟨mem_ball_self hδ, mem_ball_self hδ⟩
  have he := (hd.continuousOn.continuousAt ((isOpen_ball.prod isOpen_ball).mem_nhds hx)).eventually_ne hneD
  obtain ⟨γ, hγ, hball⟩ := Metric.eventually_nhds_iff.mp he
  let ε := min δ γ
  have hε : 0 < ε := lt_min hδ hγ
  have hsub : ball b ε ×ˢ ball z ε ⊆ ball b δ ×ˢ ball z δ := fun x hx =>
    ⟨ball_subset_ball (min_le_left _ _) hx.1, ball_subset_ball (min_le_left _ _) hx.2⟩
  have hnon : ∀ x ∈ ball b ε ×ˢ ball z ε, cepsScaledSurrogateDenominator dom ρW N lam x.2 x.1 ≠ 0 := by
    intro x hx
    apply hball
    have hh : x ∈ ball (b, z) γ := by
      rw [← ball_prod_same]
      exact ⟨ball_subset_ball (min_le_right _ _) hx.1, ball_subset_ball (min_le_right _ _) hx.2⟩
    exact mem_ball.mp hh
  have hB : DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledSurrogateBridge dom ρW N lam x.2 x.1)
      (ball b ε ×ˢ ball z ε) :=
    ((hpG.mono hsub).neg.mul (hmG.mono hsub)).mul ((hd.mono hsub).inv hnon)
  have hs : DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledSurrogateBridge dom ρW N lam x.1 x.2)
      (ball z ε ×ˢ ball b ε) := hB.comp (f := fun x : ℂ × ℂ => (x.2, x.1))
        (differentiableOn_snd.prodMk differentiableOn_fst) (fun x hx => ⟨hx.2, hx.1⟩)
  refine ⟨ε, hε, hB, ?_⟩
  exact (differentiableOn_deriv_fst (isOpen_ball.prod isOpen_ball) hs).comp
    (f := fun x : ℂ × ℂ => (x.2, x.1)) (differentiableOn_snd.prodMk differentiableOn_fst)
      (fun x hx => ⟨hx.2, hx.1⟩)

end PGM
