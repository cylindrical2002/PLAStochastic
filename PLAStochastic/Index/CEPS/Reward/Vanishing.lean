import PLAStochastic.Index.CEPS.Reward.Normalization
import PLAStochastic.Index.CEPS.Reward.Difference

/-! # Exponential reward remainder with the vanishing factor

This is the analytic renewal reward. Its identification with the original
random-walk first-passage expectation is a separate probabilistic step.
-/

noncomputable section
open MeasureTheory Set Complex Filter
namespace PGM.WienerHopf

theorem rewardSolution_sub {g b d : ℝ → ℂ} {D θ : ℝ} (hg : IsExpDensity g D θ)
    (hθ : 0 ≤ θ) (hb : HalfBdd (halfLine b)) (hd : HalfBdd (halfLine d)) :
    rewardSolution g (b - d) = rewardSolution g b - rewardSolution g d := by
  have he : halfLine (b - d) = halfLine b - halfLine d := by
    funext x
    by_cases hx : 0 ≤ x
    · simp only [Pi.sub_apply, halfLine_of_nonneg _ hx]
    · simp only [Pi.sub_apply, halfLine_of_neg _ (not_le.mp hx), sub_self]
  funext x
  simp only [rewardSolution, he, Pi.add_apply, Pi.sub_apply,
    convC_sub_right (halfBdd_renewalDensity hg hθ) hb hd]
  ring

theorem rewardMoment_sub {β : ℂ} {b d : ℝ → ℂ}
    (hb : IntegrableOn (fun z : ℝ => cexp (β * z) * b z) (Ioi 0))
    (hd : IntegrableOn (fun z : ℝ => cexp (β * z) * d z) (Ioi 0)) :
    rewardMoment β (b - d) = rewardMoment β b - rewardMoment β d := by
  rw [rewardMoment, rewardMoment, rewardMoment, ← integral_sub hb hd]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro z _
  simp only [Pi.sub_apply]
  ring

variable {g : ℝ → ℂ} {D θ c K : ℝ} {β : ℂ} {L : ℂ → ℂ}

/-- The vanishing-factor reward estimate, including `a=-β` without any division. -/
theorem norm_rewardSolution_sub_pole_vanishing (h : ExpRenewalData g D θ c β L K)
    {a : ℂ} (ha : ‖a‖ ≤ c / 2) {x : ℝ} (hx : 0 ≤ x) :
    ‖rewardSolution g (rewardSource g a) x -
      renewalRes g β * cexp (-β * x) * rewardMoment β (rewardSource g a)‖ ≤
      (4 * rewardLinearBound D θ c K * D / (θ - c / 2) ^ 2) *
        ‖a + β‖ * Real.exp (-(c / 2) * x) := by
  have hc := h.c₀_pos
  have ht := h.c₀_lt
  have hD := h.density.nonneg_D
  have hden : 0 < θ - c / 2 := by linarith
  have hβ : ‖β‖ ≤ c / 2 := h.root_le.trans (by linarith)
  let b := rewardSource g a
  let d := rewardSource g (-β)
  let B := 4 * D / (θ - c / 2) ^ 2 * ‖a + β‖
  have hB0 : 0 ≤ B := by unfold B; positivity
  have hB : ∀ z, 0 ≤ z → ‖(b - d) z‖ ≤ B * Real.exp (-θ * z) := fun z _ =>
    norm_rewardSource_sub_root_le h.density ha hβ (by linarith) z
  have hb := halfBdd_rewardSource h.density h.θ_pos.le ha (by linarith : c / 2 < θ)
  have hd := halfBdd_rewardSource h.density h.θ_pos.le (a := -β)
    (by simpa using hβ) (by linarith : c / 2 < θ)
  have hbound := norm_rewardSolution_sub_pole_le h
    ((measurable_rewardSource h.density a).sub (measurable_rewardSource h.density (-β))) hB0 hB hx
  have hmb := integrableOn_rewardMoment_tail (measurable_rewardSource h.density a)
    (B := D / (θ - c / 2)) (θ := θ)
    (fun z _ => norm_rewardSource_le h.density ha (by linarith) z)
    h.root_le (by linarith : c / 4 < θ) (x := 0) le_rfl
  have hmd := integrableOn_rewardMoment_tail (measurable_rewardSource h.density (-β))
    (B := D / (θ - c / 2)) (θ := θ)
    (fun z _ => norm_rewardSource_le h.density (a := -β) (by simpa using hβ) (by linarith) z)
    h.root_le (by linarith : c / 4 < θ) (x := 0) le_rfl
  rw [rewardSolution_sub h.density h.θ_pos.le hb hd, Pi.sub_apply,
    rewardSolution_at_root h.density h.θ_pos.le (h.root_le.trans_lt (by linarith)) h.laplace_root hx,
    rewardMoment_sub hmb hmd] at hbound
  have he : rewardSolution g b x - cexp (-β * x) -
      renewalRes g β * cexp (-β * x) * (rewardMoment β b - rewardMoment β d) =
      rewardSolution g b x - renewalRes g β * cexp (-β * x) * rewardMoment β b := by
    have hn := rewardMoment_root_normalized h
    change renewalRes g β * rewardMoment β d = 1 at hn
    linear_combination cexp (-β * x) * hn
  change ‖rewardSolution g b x - cexp (-β * x) -
    renewalRes g β * cexp (-β * x) * (rewardMoment β b - rewardMoment β d)‖ ≤ _ at hbound
  rw [he] at hbound
  convert hbound using 1; ring

end PGM.WienerHopf
