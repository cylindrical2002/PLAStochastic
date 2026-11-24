import PLAStochastic.Index.CEPS.Normal.TwoParameterEvaluation

/-! # Holomorphic spatial families with two genuine complex parameters -/

noncomputable section
open Complex Set Metric
namespace PGM

structure CepsHolomorphicSpatialFamily (G : (ℂ × ℂ) → ℂ → ℂ)
    (U V : Set ℂ) (R : ℝ) : Prop where
  continuous : ContinuousOn (fun x : (ℂ × ℂ) × ℂ => G x.1 x.2) ((U ×ˢ V) ×ˢ ball 0 R)
  scale : ∀ z ∈ V, DifferentiableOn ℂ (fun x : ℂ × ℂ => G (x.1, z) x.2) (U ×ˢ ball 0 R)
  frequency : ∀ b ∈ U, DifferentiableOn ℂ (fun x : ℂ × ℂ => G (b, x.1) x.2) (V ×ˢ ball 0 R)

theorem CepsHolomorphicSpatialFamily.of_differentiable
    {G : (ℂ × ℂ) → ℂ → ℂ} {U V : Set ℂ} {R : ℝ}
    (hG : DifferentiableOn ℂ (fun x : (ℂ × ℂ) × ℂ => G x.1 x.2) ((U ×ˢ V) ×ˢ ball 0 R)) :
    CepsHolomorphicSpatialFamily G U V R where
  continuous := hG.continuousOn
  scale := fun z hz => hG.comp (f := fun x : ℂ × ℂ => ((x.1, z), x.2)) (by fun_prop)
    (fun _ hx => ⟨⟨hx.1, hz⟩, hx.2⟩)
  frequency := fun b hb => hG.comp (f := fun x : ℂ × ℂ => ((b, x.1), x.2)) (by fun_prop)
    (fun _ hx => ⟨⟨hb, hx.1⟩, hx.2⟩)

theorem CepsHolomorphicSpatialFamily.spatial {G : (ℂ × ℂ) → ℂ → ℂ}
    {U V : Set ℂ} {R : ℝ} (hU : IsOpen U) (hG : CepsHolomorphicSpatialFamily G U V R)
    {x : ℂ × ℂ} (hx : x ∈ U ×ˢ V) : DifferentiableOn ℂ (G x) (ball 0 R) := by
  intro ξ hξ
  exact (differentiableAt_slice_snd (hU.prod isOpen_ball) (hG.scale x.2 hx.2)
    (show (x.1, ξ) ∈ U ×ˢ ball 0 R from ⟨hx.1, hξ⟩)).differentiableWithinAt

set_option maxHeartbeats 800000 in
theorem CepsHolomorphicSpatialFamily.dslope {G : (ℂ × ℂ) → ℂ → ℂ}
    {U V : Set ℂ} {R : ℝ} (hU : IsOpen U) (hV : IsOpen V)
    (hG : CepsHolomorphicSpatialFamily G U V R) {a : (ℂ × ℂ) → ℂ}
    (ha : DifferentiableOn ℂ a (U ×ˢ V)) (hmap : MapsTo a (U ×ˢ V) (ball 0 R)) :
    CepsHolomorphicSpatialFamily (fun x ξ => dslope (G x) (a x) ξ) U V R where
  continuous := cepsNormal_continuousOn_joint_moving_dslope_general (G := G) (a := a) (hU.prod hV)
    hG.continuous (fun _ hx => hG.spatial hU hx) ha.continuousOn hmap
  scale := by
    intro z hz
    exact cepsNormal_joint_moving_dslope_of_differentiable
      (G := fun b ξ => G (b, z) ξ) (a := fun b => a (b, z)) hU (hG.scale z hz)
      (ha.comp (f := fun b : ℂ => (b, z)) (by fun_prop) (fun _ hb => ⟨hb, hz⟩))
      (fun _ hb => hmap ⟨hb, hz⟩)
  frequency := by
    intro b hb
    exact cepsNormal_joint_moving_dslope_of_differentiable
      (G := fun z ξ => G (b, z) ξ) (a := fun z => a (b, z)) hV (hG.frequency b hb)
      (ha.comp (f := fun z : ℂ => (b, z)) (by fun_prop) (fun _ hz => ⟨hb, hz⟩))
      (fun _ hz => hmap ⟨hb, hz⟩)

theorem CepsHolomorphicSpatialFamily.mul {F G : (ℂ × ℂ) → ℂ → ℂ}
    {U V : Set ℂ} {R : ℝ} (hF : CepsHolomorphicSpatialFamily F U V R)
    (hG : CepsHolomorphicSpatialFamily G U V R) :
    CepsHolomorphicSpatialFamily (fun x ξ => F x ξ * G x ξ) U V R where
  continuous := hF.continuous.mul hG.continuous
  scale := fun z hz => (hF.scale z hz).mul (hG.scale z hz)
  frequency := fun b hb => (hF.frequency b hb).mul (hG.frequency b hb)

theorem CepsHolomorphicSpatialFamily.cexp {G : (ℂ × ℂ) → ℂ → ℂ}
    {U V : Set ℂ} {R : ℝ} (hG : CepsHolomorphicSpatialFamily G U V R) :
    CepsHolomorphicSpatialFamily (fun x ξ => exp (G x ξ)) U V R where
  continuous := hG.continuous.cexp
  scale := fun z hz => (hG.scale z hz).cexp
  frequency := fun b hb => (hG.frequency b hb).cexp

theorem CepsHolomorphicSpatialFamily.mono {G : (ℂ × ℂ) → ℂ → ℂ}
    {U V U' V' : Set ℂ} {R R' : ℝ} (hG : CepsHolomorphicSpatialFamily G U V R)
    (hU : U' ⊆ U) (hV : V' ⊆ V) (hR : R' ≤ R) :
    CepsHolomorphicSpatialFamily G U' V' R' where
  continuous := hG.continuous.mono (fun _ hx => ⟨⟨hU hx.1.1, hV hx.1.2⟩, ball_subset_ball hR hx.2⟩)
  scale := fun z hz => (hG.scale z (hV hz)).mono (fun _ hx => ⟨hU hx.1, ball_subset_ball hR hx.2⟩)
  frequency := fun b hb => (hG.frequency b (hU hb)).mono (fun _ hx => ⟨hV hx.1, ball_subset_ball hR hx.2⟩)

theorem CepsHolomorphicSpatialFamily.eval {G : (ℂ × ℂ) → ℂ → ℂ}
    {U V : Set ℂ} {R : ℝ} (hU : IsOpen U) (hV : IsOpen V)
    (hG : CepsHolomorphicSpatialFamily G U V R) {a : (ℂ × ℂ) → ℂ}
    (ha : DifferentiableOn ℂ a (U ×ˢ V)) (hmap : MapsTo a (U ×ˢ V) (ball 0 R)) :
    DifferentiableOn ℂ (fun x => G x (a x)) (U ×ˢ V) :=
  cepsNormal_differentiableOn_two_parameter_eval hU hV hG.continuous hG.scale hG.frequency ha hmap

end PGM
