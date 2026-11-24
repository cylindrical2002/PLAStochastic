import PLAStochastic.Index.CEPS.Reward.Source
import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.ExpRenewal

/-! # The exact reward at the root parameter

The exponential solves the renewal equation directly. Uniqueness supplies
the root-parameter identity used to obtain a vanishing remainder factor.
-/

noncomputable section
open MeasureTheory Set Complex Filter
namespace PGM.WienerHopf

theorem halfBdd_exponential (β : ℂ) : HalfBdd (halfLine (fun x : ℝ => cexp (-β * x))) := by
  refine halfBdd_halfLine (by fun_prop) (fun X => ?_)
  refine ⟨Real.exp (‖β‖ * max X 0), (Real.exp_pos _).le, fun y hy hyX => ?_⟩
  rw [norm_cexp_mul_ofReal', neg_re, neg_neg]
  apply Real.exp_le_exp.mpr
  calc
    -β.re * y ≤ ‖β‖ * y := mul_le_mul_of_nonneg_right
      ((neg_le_abs _).trans (abs_re_le_norm _)) hy
    _ ≤ ‖β‖ * max X 0 := mul_le_mul_of_nonneg_left (hyX.trans (le_max_left _ _)) (norm_nonneg _)

variable {g : ℝ → ℂ} {D θ : ℝ}

theorem reward_exponential_renewal (hg : IsExpDensity g D θ) (hθ : 0 ≤ θ)
    {β : ℂ} (hβ : ‖β‖ < θ) (hroot : laplaceC g β = 1) {x : ℝ} (_hx : 0 ≤ x) :
    cexp (-β * x) = rewardSource g (-β) x +
      convC g (halfLine (fun y : ℝ => cexp (-β * y))) x := by
  have hi : Integrable (fun h : ℝ => if x < h then cexp (β * (h - x : ℝ)) * g h else 0) := by
    have hIo : IntegrableOn (fun h : ℝ => cexp (β * (h - x : ℝ)) * g h) (Ioi x) := by
      simpa only [neg_neg] using integrableOn_rewardSource_integrand hg
        (a := -β) (a₀ := ‖β‖) (by simp) hβ x
    change Integrable ((Ioi x).indicator (fun h : ℝ => cexp (β * (h - x : ℝ)) * g h))
    exact hIo.integrable_indicator measurableSet_Ioi
  have hc := (hg.halfBdd hθ).integrable_convC_integrand (halfBdd_exponential β) x
  rw [rewardSource, neg_neg, convC, ← integral_add hi hc]
  have he : (∫ h : ℝ, (if x < h then cexp (β * (h - x : ℝ)) * g h else 0) +
      g h * halfLine (fun y : ℝ => cexp (-β * y)) (x - h)) =
        cexp (-β * x) * laplaceC g β := by
    rw [laplaceC, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun h => ?_)
    dsimp only
    have he : cexp (β * (h - x : ℝ)) = cexp (-β * x) * cexp (β * h) := by
      rw [← exp_add]
      congr 1
      push_cast
      ring
    by_cases hh : x < h
    · rw [if_pos hh, halfLine_of_neg _ (by linarith), mul_zero, add_zero, he]
      ring
    · rw [if_neg hh, zero_add, halfLine_of_nonneg _ (by linarith)]
      have he' : cexp (-β * (x - h : ℝ)) = cexp (β * (h - x : ℝ)) := by
        congr 1
        push_cast
        ring
      rw [he', he]
      ring
  rw [he, hroot, mul_one]

/-- Exact cancellation at `a=-β`, proved at the renewal-equation level. -/
theorem rewardSolution_at_root (hg : IsExpDensity g D θ) (hθ : 0 ≤ θ)
    {β : ℂ} (hβ : ‖β‖ < θ) (hroot : laplaceC g β = 1) {x : ℝ} (hx : 0 ≤ x) :
    rewardSolution g (rewardSource g (-β)) x = cexp (-β * x) := by
  have hb := halfBdd_rewardSource hg hθ (a := -β) (a₀ := ‖β‖) (by simp) hβ
  have he := eq_rewardSolution_of_renewal hg hθ hb (halfBdd_exponential β) (fun y hy => by
    rw [halfLine_of_nonneg _ hy]
    exact reward_exponential_renewal hg hθ hβ hroot hy)
  rw [← he, halfLine_of_nonneg _ hx]

end PGM.WienerHopf
