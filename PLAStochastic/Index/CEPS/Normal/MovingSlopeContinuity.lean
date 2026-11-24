import PLAStochastic.Index.CEPS.Normal.CompactParameterContinuity
import PLAStochastic.Index.CEPS.Normal.MovingSlope
import PLAStochastic.ForMathlib.Analysis.Complex.ParameterSpatialDerivative

/-! # Joint continuity of actual moving spatial divided differences -/

noncomputable section
open Complex Set Metric
namespace PGM

variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]

theorem cepsNormal_continuousOn_joint_moving_dslope_general
    {U : Set E} (hU : IsOpen U) {R : ℝ} {G : E → ℂ → ℂ}
    (hG : ContinuousOn (fun x : E × ℂ => G x.1 x.2) (U ×ˢ ball 0 R))
    (hd : ∀ x ∈ U, DifferentiableOn ℂ (G x) (ball 0 R))
    {a : E → ℂ} (ha : ContinuousOn a U) (hamap : MapsTo a U (ball 0 R)) :
    ContinuousOn (fun x : E × ℂ => dslope (G x.1) (a x.1) x.2) (U ×ˢ ball 0 R) := by
  have hD := continuousOn_parameter_spatial_deriv hU hG hd
  let V := U ×ˢ ball (0 : ℂ) R
  let F : (E × ℂ) → ℝ → ℂ := fun x s =>
    deriv (G x.1) (a x.1 + (s : ℂ) * (x.2 - a x.1))
  have hca : ContinuousOn (fun y : (E × ℂ) × ℝ => a y.1.1) (V ×ˢ Icc 0 1) :=
    ha.comp (by fun_prop) (fun _ hy => hy.1.1)
  have hcs : ContinuousOn (fun y : (E × ℂ) × ℝ => (y.2 : ℂ)) (V ×ˢ Icc 0 1) := by fun_prop
  have hcb : ContinuousOn (fun y : (E × ℂ) × ℝ => y.1.2) (V ×ˢ Icc 0 1) := by fun_prop
  have hp : ContinuousOn (fun y : (E × ℂ) × ℝ =>
      (y.1.1, a y.1.1 + (y.2 : ℂ) * (y.1.2 - a y.1.1))) (V ×ˢ Icc 0 1) :=
    (by fun_prop : ContinuousOn (fun y : (E × ℂ) × ℝ => y.1.1) _).prodMk
      (hca.add (hcs.mul (hcb.sub hca)))
  have hcF : ContinuousOn (fun y : (E × ℂ) × ℝ => F y.1 y.2) (V ×ˢ Icc 0 1) :=
    hD.comp hp (fun y hy =>
      ⟨hy.1.1, cepsNormal_segment_mem_ball (hamap hy.1.1) hy.1.2 hy.2⟩)
  have hI := cepsNormal_continuousOn_parameterIntegral_general (hU.prod isOpen_ball) hcF
  apply hI.congr
  intro x hx
  exact cepsNormal_dslope_eq_integral (hd x.1 hx.1) (hamap hx.1) hx.2

theorem cepsNormal_continuousOn_joint_moving_second_dslope_general
    {U : Set E} (hU : IsOpen U) {R : ℝ} {G : E → ℂ → ℂ}
    (hG : ContinuousOn (fun x : E × ℂ => G x.1 x.2) (U ×ˢ ball 0 R))
    (hd : ∀ x ∈ U, DifferentiableOn ℂ (G x) (ball 0 R))
    {a b : E → ℂ} (ha : ContinuousOn a U) (hb : ContinuousOn b U)
    (hamap : MapsTo a U (ball 0 R)) (hbmap : MapsTo b U (ball 0 R)) :
    ContinuousOn (fun x : E × ℂ => dslope (dslope (G x.1) (a x.1)) (b x.1) x.2)
      (U ×ˢ ball 0 R) := by
  have hH := cepsNormal_continuousOn_joint_moving_dslope_general hU hG hd ha hamap
  have hHd : ∀ x ∈ U, DifferentiableOn ℂ (dslope (G x) (a x)) (ball 0 R) := fun x hx =>
    (differentiableOn_dslope (isOpen_ball.mem_nhds (hamap hx))).mpr (hd x hx)
  exact cepsNormal_continuousOn_joint_moving_dslope_general hU hH hHd hb hbmap

end PGM
