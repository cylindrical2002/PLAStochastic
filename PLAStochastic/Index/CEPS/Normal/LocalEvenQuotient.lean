import PLAStochastic.Index.CEPS.Normal.JointSqrtDescent

/-! # Local square-root descent of an even quotient at its joint origin -/

noncomputable section
open Complex Set Metric Filter Topology
namespace PGM

theorem cepsNormal_joint_even_quotient_near_origin
    {U : Set ℂ} (hU : IsOpen U) {R : ℝ} (hR : 0 < R) {F S : ℂ → ℂ → ℂ}
    (hF : DifferentiableOn ℂ (fun x : ℂ × ℂ => F x.1 x.2) (U ×ˢ ball 0 R))
    (hS : DifferentiableOn ℂ (fun x : ℂ × ℂ => S x.1 x.2) (U ×ˢ ball 0 R))
    (hFeven : ∀ b ∈ U, ∀ r ∈ ball (0 : ℂ) R, F b (-r) = F b r)
    (hSeven : ∀ b ∈ U, ∀ r ∈ ball (0 : ℂ) R, S b (-r) = S b r)
    {b : ℂ} (hb : b ∈ U) (hS0 : S b 0 ≠ 0) :
    ∃ ε > 0, DifferentiableOn ℂ (fun x : ℂ × ℂ => F x.1 (sqrt x.2) / S x.1 (sqrt x.2))
      (ball b ε ×ˢ ball 0 (ε ^ 2)) := by
  have hx : (b, (0 : ℂ)) ∈ U ×ˢ ball 0 R := ⟨hb, mem_ball_self hR⟩
  have hcS := hS.continuousOn.continuousAt ((hU.prod isOpen_ball).mem_nhds hx)
  have hbase : ∀ᶠ x : ℂ × ℂ in 𝓝 (b, 0), x ∈ U ×ˢ ball 0 R :=
    (hU.prod isOpen_ball).mem_nhds hx
  have hsmall : ∀ᶠ x : ℂ × ℂ in 𝓝 (b, 0), x ∈ U ×ˢ ball 0 R ∧ S x.1 x.2 ≠ 0 :=
    hbase.and
      (hcS.tendsto.eventually (isOpen_ne.mem_nhds hS0))
  obtain ⟨ε, hε, hmem⟩ := Metric.eventually_nhds_iff.mp hsmall
  have hp : ∀ x ∈ ball b ε ×ˢ ball (0 : ℂ) ε, x ∈ U ×ˢ ball 0 R ∧ S x.1 x.2 ≠ 0 := by
    intro x hx'
    apply hmem
    rw [← mem_ball, ← ball_prod_same]
    exact hx'
  have hF' : DifferentiableOn ℂ (fun x : ℂ × ℂ => F x.1 x.2) (ball b ε ×ˢ ball 0 ε) :=
    hF.mono (fun _ hx' => (hp _ hx').1)
  have hS' : DifferentiableOn ℂ (fun x : ℂ × ℂ => S x.1 x.2) (ball b ε ×ˢ ball 0 ε) :=
    hS.mono (fun _ hx' => (hp _ hx').1)
  have hq : DifferentiableOn ℂ (fun x : ℂ × ℂ => F x.1 x.2 / S x.1 x.2)
      (ball b ε ×ˢ ball 0 ε) := hF'.mul (hS'.inv (fun _ hx' => (hp _ hx').2))
  refine ⟨ε, hε, cepsNormal_differentiableOn_joint_comp_sqrt
    (G := fun b r => F b r / S b r) (U := ball b ε) isOpen_ball hε hq ?_⟩
  intro b' hb' r hr
  have hbr := (hp (b', r) ⟨hb', hr⟩).1
  rw [hFeven b' hbr.1 r hbr.2, hSeven b' hbr.1 r hbr.2]

end PGM
