import PLAStochastic.Index.CEPS.Normal.MovingJointSlope
import PLAStochastic.Index.CEPS.Normal.JointSpatialDerivative
import Mathlib.Analysis.Complex.RemovableSingularity

/-! # Moving divided differences from joint holomorphy -/

noncomputable section
open Complex Set Metric
namespace PGM

theorem cepsNormal_joint_moving_dslope_of_differentiable
    {U : Set ℂ} (hU : IsOpen U) {R : ℝ} {G : ℂ → ℂ → ℂ}
    (hG : DifferentiableOn ℂ (fun x : ℂ × ℂ => G x.1 x.2) (U ×ˢ ball 0 R))
    {a : ℂ → ℂ} (ha : DifferentiableOn ℂ a U) (hamap : MapsTo a U (ball 0 R)) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => dslope (G x.1) (a x.1) x.2)
      (U ×ˢ ball 0 R) :=
  cepsNormal_differentiableOn_joint_moving_dslope hU
    (fun r hr z hz => (differentiableAt_slice_snd (hU.prod isOpen_ball) hG
      (show (r, z) ∈ U ×ˢ ball 0 R from ⟨hr, hz⟩)).differentiableWithinAt)
    (cepsNormal_differentiableOn_spatial_deriv hU hG) ha hamap

theorem cepsNormal_joint_moving_second_dslope_of_differentiable
    {U : Set ℂ} (hU : IsOpen U) {R : ℝ} {G : ℂ → ℂ → ℂ}
    (hG : DifferentiableOn ℂ (fun x : ℂ × ℂ => G x.1 x.2) (U ×ˢ ball 0 R))
    {a b : ℂ → ℂ} (ha : DifferentiableOn ℂ a U) (hb : DifferentiableOn ℂ b U)
    (hamap : MapsTo a U (ball 0 R)) (hbmap : MapsTo b U (ball 0 R)) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => dslope (dslope (G x.1) (a x.1)) (b x.1) x.2)
      (U ×ˢ ball 0 R) :=
  cepsNormal_joint_moving_dslope_of_differentiable (G := fun r => dslope (G r) (a r)) hU
    (cepsNormal_joint_moving_dslope_of_differentiable hU hG ha hamap) hb hbmap

end PGM
