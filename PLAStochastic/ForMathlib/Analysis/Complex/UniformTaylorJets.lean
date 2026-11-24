import PLAStochastic.ForMathlib.Analysis.Complex.PartialDeriv
import PLAStochastic.ForMathlib.Analysis.Complex.TaylorSeriesBudget
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! # Uniform spatial-disc budgets from exact scalar Taylor-jet equality -/

noncomputable section
open Complex Set Metric Filter Topology Finset PowerSeries
namespace PGM

theorem norm_sub_le_of_uniform_taylorJets {F G : ℂ → ℂ → ℂ} {B R M : ℝ}
    (hB : 0 < B)
    (hF : DifferentiableOn ℂ (fun x : ℂ × ℂ => F x.1 x.2) (ball 0 B ×ˢ ball 0 R))
    (hG : DifferentiableOn ℂ (fun x : ℂ × ℂ => G x.1 x.2) (ball 0 B ×ˢ ball 0 R))
    (hbound : ∀ b ∈ ball (0 : ℂ) B, ∀ ξ ∈ ball (0 : ℂ) R, ‖F b ξ - G b ξ‖ ≤ M)
    (N : ℕ) (he : ∀ ξ ∈ ball (0 : ℂ) R, ∀ j ≤ N,
      coeff j (complexTaylorSeries (fun b => F b ξ) 0) =
        coeff j (complexTaylorSeries (fun b => G b ξ) 0))
    {b ξ : ℂ} (hb : b ∈ ball (0 : ℂ) (B / 2)) (hξ : ξ ∈ ball (0 : ℂ) R) :
    ‖F b ξ - G b ξ‖ ≤ (((N + 1).factorial : ℝ) * M / (B / 4) ^ (N + 1)) * ‖b‖ ^ (N + 1) := by
  have hdF : DifferentiableOn ℂ (fun b => F b ξ) (ball 0 B) := fun b hb =>
    (differentiableAt_slice_fst (isOpen_ball.prod isOpen_ball) hF ⟨hb, hξ⟩).differentiableWithinAt
  have hdG : DifferentiableOn ℂ (fun b => G b ξ) (ball 0 B) := fun b hb =>
    (differentiableAt_slice_fst (isOpen_ball.prod isOpen_ball) hG ⟨hb, hξ⟩).differentiableWithinAt
  have haF := hdF.analyticAt (ball_mem_nhds _ hB)
  have haG := hdG.analyticAt (ball_mem_nhds _ hB)
  have hz : complexTaylorSum (fun b => F b ξ - G b ξ) (N + 1) 0 b = 0 := by
    unfold complexTaylorSum
    apply sum_eq_zero
    intro j hj
    have hjN : j ≤ N := by have := mem_range.mp hj; omega
    have hc := he ξ hξ j hjN
    simp only [complexTaylorSeries, coeff_mk] at hc
    have hfac : (j.factorial : ℂ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero j)
    have heD := mul_left_cancel₀ hfac hc
    have hCF : ContDiffAt ℂ j (fun b => F b ξ) 0 := haF.contDiffAt
    have hCG : ContDiffAt ℂ j (fun b => G b ξ) 0 := haG.contDiffAt
    rw [iteratedDeriv_fun_sub hCF hCG, heD, sub_self, mul_zero]
  have ht := norm_sub_complexTaylorSum_le_of_ball (f := fun b => F b ξ - G b ξ)
    (N + 1) hB (hdF.sub hdG)
    (fun b hb => hbound b hb ξ hξ) hb
  simpa only [hz, sub_zero] using ht

end PGM
