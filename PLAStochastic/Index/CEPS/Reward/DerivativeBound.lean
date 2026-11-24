import PLAStochastic.Index.CEPS.Reward.Derivative
import PLAStochastic.Index.CEPS.Reward.Vanishing
import PLAStochastic.Index.CEPS.Reward.MomentFormula

/-! # Spatial derivative remainder with the same vanishing factor -/

noncomputable section
open MeasureTheory Set Complex Filter
namespace PGM.WienerHopf

def rewardRemainder (g : ℝ → ℂ) (β a : ℂ) (x : ℝ) : ℂ :=
  rewardSolution g (rewardSource g a) x -
    renewalRes g β * cexp (-β * x) * rewardMoment β (rewardSource g a)

def rewardMomentBound (D θ c : ℝ) : ℝ := D / (θ - c / 2) / (θ - c / 4)

def rewardDerivativeBound (D θ c K : ℝ) : ℝ :=
  (c / 2) * (4 * rewardLinearBound D θ c K * D / (θ - c / 2) ^ 2) +
    rewardMomentBound D θ c * rewardRenewalBound D θ c K

variable {g : ℝ → ℂ} {D θ c K : ℝ} {β : ℂ} {L : ℂ → ℂ}

theorem norm_rewardMoment_le (h : ExpRenewalData g D θ c β L K)
    {a : ℂ} (ha : ‖a‖ ≤ c / 2) :
    ‖rewardMoment β (rewardSource g a)‖ ≤ rewardMomentBound D θ c := by
  have hb := norm_rewardMoment_tail_le (measurable_rewardSource h.density a)
    (fun z _ => norm_rewardSource_le h.density ha (by linarith [h.c₀_lt, h.c₀_pos]) z)
    h.root_le (by linarith [h.c₀_lt, h.c₀_pos]) (x := 0) le_rfl
  simpa only [rewardMoment, rewardMomentBound, mul_zero, neg_zero, Real.exp_zero, mul_one] using hb

theorem norm_one_sub_laplace_reward_le (h : ExpRenewalData g D θ c β L K)
    {a : ℂ} (ha : ‖a‖ ≤ c / 2) :
    ‖1 - laplaceC g (-a)‖ ≤ ‖a + β‖ * rewardMomentBound D θ c := by
  rw [h.one_sub_laplace_eq (-a), ← rewardMoment_eq_dslope h ha, norm_mul]
  have he : β - -a = a + β := by ring
  rw [he]
  exact mul_le_mul_of_nonneg_left (norm_rewardMoment_le h ha) (norm_nonneg _)

theorem hasDerivAt_rewardRemainder (h : ExpRenewalData g D θ c β L K)
    {a : ℂ} (ha : ‖a‖ ≤ c / 2) {x : ℝ} (hx : 0 < x)
    (hux : ContinuousAt (renewalDensity g) x) :
    HasDerivAt (rewardRemainder g β a)
      (a * rewardRemainder g β a x - (1 - laplaceC g (-a)) *
        (renewalDensity g x - renewalRes g β * cexp (-β * x))) x := by
  have hR := hasDerivAt_rewardSolution h.density h.θ_pos.le
    (ha.trans_lt (by linarith [h.c₀_lt, h.c₀_pos])) hx hux
  have hlin : HasDerivAt (fun y : ℝ => -β * y) (-β) x := by
    simpa only [mul_one] using! ((hasDerivAt_id (x : ℂ)).const_mul (-β)).comp_ofReal
  have hE : HasDerivAt (fun y : ℝ => cexp (-β * y)) (-β * cexp (-β * x)) x := by
    simpa only [mul_comm] using! (Complex.hasDerivAt_exp (-β * x)).comp x hlin
  have hf := hR.sub ((hE.const_mul (renewalRes g β)).mul_const
    (rewardMoment β (rewardSource g a)))
  have hm : 1 - laplaceC g (-a) = (a + β) * rewardMoment β (rewardSource g a) := by
    rw [h.one_sub_laplace_eq (-a), ← rewardMoment_eq_dslope h ha]
    ring
  have hd : a * rewardSolution g (rewardSource g a) x - (1 - laplaceC g (-a)) * renewalDensity g x -
      (renewalRes g β * (-β * cexp (-β * x))) * rewardMoment β (rewardSource g a) =
      a * rewardRemainder g β a x - (1 - laplaceC g (-a)) *
        (renewalDensity g x - renewalRes g β * cexp (-β * x)) := by
    rw [rewardRemainder, hm]
    ring
  exact hd ▸ hf

theorem norm_deriv_rewardRemainder_le (h : ExpRenewalData g D θ c β L K)
    {a : ℂ} (ha : ‖a‖ ≤ c / 2) {x : ℝ} (hx : 0 < x)
    (hux : ContinuousAt (renewalDensity g) x) :
    ‖deriv (rewardRemainder g β a) x‖ ≤ rewardDerivativeBound D θ c K *
      ‖a + β‖ * Real.exp (-(c / 2) * x) := by
  rw [(hasDerivAt_rewardRemainder h ha hx hux).deriv]
  have hD := h.density.nonneg_D
  have hc := h.c₀_pos
  have ht := h.c₀_lt
  have hd2 : 0 < θ - c / 2 := by linarith
  have hd4 : 0 < θ - c / 4 := by linarith
  have hM0 : 0 ≤ rewardMomentBound D θ c := by unfold rewardMomentBound; positivity
  have hr := h.norm_renewalDensity_sub_le hx
  change ‖renewalDensity g x - renewalRes g β * cexp (-β * x)‖ ≤
    rewardRenewalBound D θ c K * Real.exp (-(c / 2) * x) at hr
  have hε := norm_rewardSolution_sub_pole_vanishing h ha hx.le
  change ‖rewardRemainder g β a x‖ ≤ _ at hε
  calc
    _ ≤ ‖a‖ * ‖rewardRemainder g β a x‖ +
        ‖1 - laplaceC g (-a)‖ * ‖renewalDensity g x - renewalRes g β * cexp (-β * x)‖ := by
      simpa only [norm_mul] using norm_sub_le (a * rewardRemainder g β a x)
        ((1 - laplaceC g (-a)) * (renewalDensity g x - renewalRes g β * cexp (-β * x)))
    _ ≤ (c / 2) * ((4 * rewardLinearBound D θ c K * D / (θ - c / 2) ^ 2) *
          ‖a + β‖ * Real.exp (-(c / 2) * x)) +
        (‖a + β‖ * rewardMomentBound D θ c) *
          (rewardRenewalBound D θ c K * Real.exp (-(c / 2) * x)) :=
      add_le_add (mul_le_mul ha hε (norm_nonneg _) (by positivity))
        (mul_le_mul (norm_one_sub_laplace_reward_le h ha) hr (norm_nonneg _) (by positivity))
    _ = _ := by unfold rewardDerivativeBound; ring

end PGM.WienerHopf
