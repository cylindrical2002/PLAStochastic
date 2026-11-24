import PLAStochastic.Index.CEPS.Reward.Core
import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Normalization of the root-parameter reward moment -/

noncomputable section
open MeasureTheory Set Complex Filter Topology
namespace PGM.WienerHopf

variable {g : ℝ → ℂ} {D θ c K : ℝ} {β : ℂ} {L : ℂ → ℂ}

theorem rewardLinearBound_pos (h : ExpRenewalData g D θ c β L K) :
    0 < rewardLinearBound D θ c K := by
  have hc := h.c₀_pos
  have ht := h.c₀_lt
  have hD := h.density.nonneg_D
  have hf := h.factorBound_pos
  have hden : 0 < θ - c / 2 := by linarith
  have hden' : 0 < θ - c / 4 := by linarith
  unfold rewardLinearBound rewardRenewalBound
  positivity

/-- `res M_{b_{-β}} = 1`, deduced from exact cancellation and the linear core estimate. -/
theorem rewardMoment_root_normalized (h : ExpRenewalData g D θ c β L K) :
    renewalRes g β * rewardMoment β (rewardSource g (-β)) = 1 := by
  let B := D / (θ - c / 4)
  let C := rewardLinearBound D θ c K * B
  let A := 1 - renewalRes g β * rewardMoment β (rewardSource g (-β))
  have hc := h.c₀_pos
  have ht := h.c₀_lt
  have hD := h.density.nonneg_D
  have hden : 0 < θ - c / 4 := by linarith
  have hB : 0 ≤ B := div_nonneg hD hden.le
  have hC : 0 ≤ C := mul_nonneg (rewardLinearBound_pos h).le hB
  have hβ : ‖β‖ < θ := h.root_le.trans_lt (by linarith)
  have hbound : ∀ x : ℝ, 0 ≤ x → ‖A‖ ≤ C * Real.exp (-(c / 4) * x) := by
    intro x hx
    have hsource : ∀ z, 0 ≤ z → ‖rewardSource g (-β) z‖ ≤ B * Real.exp (-θ * z) :=
      fun z _ => norm_rewardSource_le h.density (a := -β) (a₀ := c / 4)
        (by simpa using h.root_le) (by linarith) z
    have hineq := norm_rewardSolution_sub_pole_le h
      (measurable_rewardSource h.density (-β)) hB hsource hx
    rw [rewardSolution_at_root h.density h.θ_pos.le hβ h.laplace_root hx] at hineq
    have hfac : cexp (-β * x) - renewalRes g β * cexp (-β * x) *
        rewardMoment β (rewardSource g (-β)) = A * cexp (-β * x) := by dsimp [A]; ring
    rw [hfac, norm_mul, norm_cexp_mul_ofReal', neg_re, neg_neg] at hineq
    have hepos : 0 < Real.exp (-β.re * x) := Real.exp_pos _
    have hdiv := (le_div_iff₀ hepos).mpr hineq
    change ‖A‖ ≤ C * Real.exp (-(c / 2) * x) / Real.exp (-β.re * x) at hdiv
    have hex : Real.exp (-(c / 2) * x) / Real.exp (-β.re * x) =
        Real.exp ((β.re - c / 2) * x) := by rw [← Real.exp_sub]; congr 1; ring
    rw [mul_div_assoc, hex] at hdiv
    exact hdiv.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
      have hb := (re_le_norm β).trans h.root_le
      nlinarith)) hC)
  have hex : Tendsto (fun x : ℝ => Real.exp (-(c / 4) * x)) atTop (𝓝 0) := by
    have hm : Tendsto (fun x : ℝ => (c / 4) * x) atTop atTop :=
      tendsto_id.const_mul_atTop (by positivity)
    exact (Real.tendsto_exp_neg_atTop_nhds_zero.comp hm).congr
      (fun x => by simp only [Function.comp_apply, neg_mul])
  have hz : Tendsto (fun _ : ℝ => ‖A‖) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg A)
      ((eventually_ge_atTop 0).mono fun x hx => hbound x hx)
      (by simpa using hex.const_mul C)
  have hA : ‖A‖ = 0 := tendsto_nhds_unique tendsto_const_nhds hz
  have ha := norm_eq_zero.mp hA
  dsimp [A] at ha
  exact (sub_eq_zero.mp ha).symm

end PGM.WienerHopf
