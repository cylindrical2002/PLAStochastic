import PLAStochastic.Index.CEPS.Normal.MovingSlopeContinuity
import PLAStochastic.Index.CEPS.Normal.MovingHolomorphicSlope

/-! # Two-parameter moving divided differences from actual slice holomorphy

Joint continuity and the two parameter/spatial holomorphic slices suffice.
No multivariable analytic-power-series premise is introduced. Both moving
first and second differences retain their actual values on every diagonal.
-/

noncomputable section
open Complex Set Metric
namespace PGM

set_option maxHeartbeats 800000 in
theorem cepsNormal_differentiableOn_two_parameter_moving_dslope
    {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V) {R : ℝ} {G : (ℂ × ℂ) → ℂ → ℂ}
    (hc : ContinuousOn (fun x : (ℂ × ℂ) × ℂ => G x.1 x.2) ((U ×ˢ V) ×ˢ ball 0 R))
    (hG₁ : ∀ r ∈ V, DifferentiableOn ℂ (fun x : ℂ × ℂ => G (x.1, r) x.2) (U ×ˢ ball 0 R))
    (hG₂ : ∀ b ∈ U, DifferentiableOn ℂ (fun x : ℂ × ℂ => G (b, x.1) x.2) (V ×ˢ ball 0 R))
    {a b : (ℂ × ℂ) → ℂ} (ha : DifferentiableOn ℂ a (U ×ˢ V))
    (hb : DifferentiableOn ℂ b (U ×ˢ V))
    (hamap : MapsTo a (U ×ˢ V) (ball 0 R)) (hbmap : MapsTo b (U ×ˢ V) (ball 0 R)) :
    DifferentiableOn ℂ (fun x => dslope (G x) (a x) (b x)) (U ×ˢ V) := by
  have hd : ∀ x ∈ U ×ˢ V, DifferentiableOn ℂ (G x) (ball 0 R) := by
    intro x hx ξ hξ
    exact (differentiableAt_slice_snd (G := fun y => G (y.1, x.2) y.2) (hU.prod isOpen_ball) (hG₁ x.2 hx.2)
      (show (x.1, ξ) ∈ U ×ˢ ball 0 R from ⟨hx.1, hξ⟩)).differentiableWithinAt
  have hcH := cepsNormal_continuousOn_joint_moving_dslope_general
    (G := G) (a := a) (hU.prod hV) hc hd ha.continuousOn hamap
  have hcS : ContinuousOn (fun x => dslope (G x) (a x) (b x)) (U ×ˢ V) :=
    hcH.comp (f := fun x : ℂ × ℂ => (x, b x))
      (continuousOn_id.prodMk hb.continuousOn) (fun x hx => ⟨hx, hbmap hx⟩)
  refine osgood (hU.prod hV) hcS ?_ ?_
  · intro x hx
    have ha₁ : DifferentiableOn ℂ (fun z => a (z, x.2)) U :=
      ha.comp (differentiableOn_id.prodMk (differentiableOn_const x.2)) (fun _ hz => ⟨hz, hx.2⟩)
    have hb₁ : DifferentiableOn ℂ (fun z => b (z, x.2)) U :=
      hb.comp (differentiableOn_id.prodMk (differentiableOn_const x.2)) (fun _ hz => ⟨hz, hx.2⟩)
    have hH₁ := cepsNormal_joint_moving_dslope_of_differentiable
      (G := fun z ξ => G (z, x.2) ξ) (a := fun z => a (z, x.2)) hU (hG₁ x.2 hx.2) ha₁
      (fun z hz => hamap ⟨hz, hx.2⟩)
    have hS₁ : DifferentiableOn ℂ (fun z => dslope (G (z, x.2)) (a (z, x.2)) (b (z, x.2))) U :=
      hH₁.comp (f := fun z : ℂ => (z, b (z, x.2)))
        (differentiableOn_id.prodMk hb₁) (fun z hz => ⟨hz, hbmap ⟨hz, hx.2⟩⟩)
    exact (hS₁ x.1 hx.1).differentiableAt (hU.mem_nhds hx.1)
  · intro x hx
    have ha₂ : DifferentiableOn ℂ (fun z => a (x.1, z)) V :=
      ha.comp ((differentiableOn_const x.1).prodMk differentiableOn_id) (fun _ hz => ⟨hx.1, hz⟩)
    have hb₂ : DifferentiableOn ℂ (fun z => b (x.1, z)) V :=
      hb.comp ((differentiableOn_const x.1).prodMk differentiableOn_id) (fun _ hz => ⟨hx.1, hz⟩)
    have hH₂ := cepsNormal_joint_moving_dslope_of_differentiable
      (G := fun z ξ => G (x.1, z) ξ) (a := fun z => a (x.1, z)) hV (hG₂ x.1 hx.1) ha₂
      (fun z hz => hamap ⟨hx.1, hz⟩)
    have hS₂ : DifferentiableOn ℂ (fun z => dslope (G (x.1, z)) (a (x.1, z)) (b (x.1, z))) V :=
      hH₂.comp (f := fun z : ℂ => (z, b (x.1, z)))
        (differentiableOn_id.prodMk hb₂) (fun z hz => ⟨hz, hbmap ⟨hx.1, hz⟩⟩)
    exact (hS₂ x.2 hx.2).differentiableAt (hV.mem_nhds hx.2)

set_option maxHeartbeats 800000 in
theorem cepsNormal_differentiableOn_two_parameter_moving_second_dslope
    {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V) {R : ℝ} {G : (ℂ × ℂ) → ℂ → ℂ}
    (hc : ContinuousOn (fun x : (ℂ × ℂ) × ℂ => G x.1 x.2) ((U ×ˢ V) ×ˢ ball 0 R))
    (hG₁ : ∀ r ∈ V, DifferentiableOn ℂ (fun x : ℂ × ℂ => G (x.1, r) x.2) (U ×ˢ ball 0 R))
    (hG₂ : ∀ b ∈ U, DifferentiableOn ℂ (fun x : ℂ × ℂ => G (b, x.1) x.2) (V ×ˢ ball 0 R))
    {a b c : (ℂ × ℂ) → ℂ} (ha : DifferentiableOn ℂ a (U ×ˢ V))
    (hb : DifferentiableOn ℂ b (U ×ˢ V)) (hc' : DifferentiableOn ℂ c (U ×ˢ V))
    (hamap : MapsTo a (U ×ˢ V) (ball 0 R)) (hbmap : MapsTo b (U ×ˢ V) (ball 0 R))
    (hcmap : MapsTo c (U ×ˢ V) (ball 0 R)) :
    DifferentiableOn ℂ (fun x => dslope (dslope (G x) (a x)) (b x) (c x)) (U ×ˢ V) := by
  have hd : ∀ x ∈ U ×ˢ V, DifferentiableOn ℂ (G x) (ball 0 R) := by
    intro x hx ξ hξ
    exact (differentiableAt_slice_snd (G := fun y => G (y.1, x.2) y.2) (hU.prod isOpen_ball) (hG₁ x.2 hx.2)
      (show (x.1, ξ) ∈ U ×ˢ ball 0 R from ⟨hx.1, hξ⟩)).differentiableWithinAt
  have hcH := cepsNormal_continuousOn_joint_moving_dslope_general
    (G := G) (a := a) (hU.prod hV) hc hd ha.continuousOn hamap
  have hH₁ : ∀ r ∈ V, DifferentiableOn ℂ
      (fun x : ℂ × ℂ => dslope (G (x.1, r)) (a (x.1, r)) x.2) (U ×ˢ ball 0 R) := by
    intro r hr
    exact cepsNormal_joint_moving_dslope_of_differentiable
      (G := fun z ξ => G (z, r) ξ) (a := fun z => a (z, r)) hU (hG₁ r hr)
      (ha.comp (differentiableOn_id.prodMk (differentiableOn_const r)) (fun _ hz => ⟨hz, hr⟩))
      (fun z hz => hamap ⟨hz, hr⟩)
  have hH₂ : ∀ z ∈ U, DifferentiableOn ℂ
      (fun x : ℂ × ℂ => dslope (G (z, x.1)) (a (z, x.1)) x.2) (V ×ˢ ball 0 R) := by
    intro z hz
    exact cepsNormal_joint_moving_dslope_of_differentiable
      (G := fun r ξ => G (z, r) ξ) (a := fun r => a (z, r)) hV (hG₂ z hz)
      (ha.comp ((differentiableOn_const z).prodMk differentiableOn_id) (fun _ hr => ⟨hz, hr⟩))
      (fun r hr => hamap ⟨hz, hr⟩)
  exact cepsNormal_differentiableOn_two_parameter_moving_dslope
    (G := fun x ξ => dslope (G x) (a x) ξ) (a := b) (b := c) hU hV hcH hH₁ hH₂ hb hc' hbmap hcmap

end PGM
