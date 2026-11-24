import PLAStochastic.Index.CEPS.Normal.MovingSlopeContinuity

/-! # Continuous moving divided differences of entire spatial families -/

noncomputable section
open Complex Set Metric
namespace PGM

set_option maxHeartbeats 600000 in
theorem cepsNormal_continuous_moving_second_dslope_entire
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E] {G : E → ℂ → ℂ}
    (hG : Continuous (fun x : E × ℂ => G x.1 x.2))
    (hd : ∀ x, Differentiable ℂ (G x))
    {a b t : E → ℂ} (ha : Continuous a) (hb : Continuous b) (ht : Continuous t) :
    Continuous (fun x => dslope (dslope (G x) (a x)) (b x) (t x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  let R : ℝ := ‖a x‖ + ‖b x‖ + ‖t x‖ + 1
  let U : Set E := {u | ‖a u‖ < R} ∩ {u | ‖b u‖ < R}
  have hU : IsOpen U := (isOpen_lt ha.norm continuous_const).inter (isOpen_lt hb.norm continuous_const)
  have hx : x ∈ U := by
    constructor <;> dsimp [R] <;> linarith [norm_nonneg (a x), norm_nonneg (b x), norm_nonneg (t x)]
  have htx : t x ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff]
    dsimp [R]
    linarith [norm_nonneg (a x), norm_nonneg (b x)]
  have hS := cepsNormal_continuousOn_joint_moving_second_dslope_general
    (G := G) (U := U) (R := R) (a := a) (b := b) hU
    hG.continuousOn (fun u _ => (hd u).differentiableOn) ha.continuousOn hb.continuousOn
    (fun _ hu => mem_ball_zero_iff.mpr hu.1) (fun _ hu => mem_ball_zero_iff.mpr hu.2)
  have hSc : ContinuousAt
      (fun w : E × ℂ => dslope (dslope (G w.1) (a w.1)) (b w.1) w.2) (x, t x) :=
    hS.continuousAt ((hU.prod isOpen_ball).mem_nhds ⟨hx, htx⟩)
  exact hSc.comp (f := fun u : E => (u, t u)) (x := x)
    (show ContinuousAt (fun u : E => (u, t u)) x from
    continuousAt_id.prodMk ht.continuousAt)

end PGM
