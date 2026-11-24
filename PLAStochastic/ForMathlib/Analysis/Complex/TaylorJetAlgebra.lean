import PLAStochastic.ForMathlib.Analysis.Complex.AnalyticJetComposition
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! # Algebra and analytic composition of exact finite Taylor jets -/

noncomputable section
open Complex Set Metric Filter Topology Finset PowerSeries Asymptotics
namespace PGM

theorem isBigO_difference_of_complexTaylorSeries_coeff_eq {f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (N : ℕ)
    (he : ∀ j ≤ N, coeff j (complexTaylorSeries f 0) = coeff j (complexTaylorSeries g 0)) :
    (fun b => f b - g b) =O[𝓝 0] (fun b : ℂ => b ^ (N + 1)) := by
  have hd := hf.sub hg
  have hev : ∀ᶠ b : ℂ in 𝓝 0, DifferentiableAt ℂ (fun b => f b - g b) b ∧
      ‖f b - g b‖ < ‖f 0 - g 0‖ + 1 :=
    (analyticAt_iff_eventually_differentiableAt.mp hd).and
      (hd.continuousAt.norm.eventually (isOpen_Iio.mem_nhds
        (show ‖f 0 - g 0‖ < ‖f 0 - g 0‖ + 1 by linarith)))
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp hev
  have hz : ∀ b : ℂ, complexTaylorSum (fun b => f b - g b) (N + 1) 0 b = 0 := by
    intro b
    unfold complexTaylorSum
    apply sum_eq_zero
    intro j hj
    have hjN : j ≤ N := by have := mem_range.mp hj; omega
    have hc := he j hjN
    simp only [complexTaylorSeries, coeff_mk] at hc
    have hfac : (j.factorial : ℂ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero j)
    have heD := mul_left_cancel₀ hfac hc
    have hCF : ContDiffAt ℂ j f 0 := hf.contDiffAt
    have hCG : ContDiffAt ℂ j g 0 := hg.contDiffAt
    rw [iteratedDeriv_fun_sub hCF hCG, heD, sub_self, mul_zero]
  apply Asymptotics.IsBigO.of_bound (((N + 1).factorial : ℝ) * (‖f 0 - g 0‖ + 1) / (R / 4) ^ (N + 1))
  filter_upwards [ball_mem_nhds (0 : ℂ) (half_pos hR)] with b hb
  have ht := norm_sub_complexTaylorSum_le_of_ball (f := fun b => f b - g b)
    (N + 1) hR (fun b hb => (hball hb).1.differentiableWithinAt)
    (fun b hb => (hball hb).2.le) hb
  simpa only [hz, sub_zero, norm_pow] using ht

theorem complexTaylorSeries_coeff_eq_mul {f g a c : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (ha : AnalyticAt ℂ a 0) (hc : AnalyticAt ℂ c 0) (N : ℕ)
    (hfa : ∀ j ≤ N, coeff j (complexTaylorSeries f 0) = coeff j (complexTaylorSeries a 0))
    (hgc : ∀ j ≤ N, coeff j (complexTaylorSeries g 0) = coeff j (complexTaylorSeries c 0)) :
    ∀ j ≤ N, coeff j (complexTaylorSeries (fun b => f b * g b) 0) =
      coeff j (complexTaylorSeries (fun b => a b * c b) 0) := by
  have heF := isBigO_difference_of_complexTaylorSeries_coeff_eq hf ha N hfa
  have heG := isBigO_difference_of_complexTaylorSeries_coeff_eq hg hc N hgc
  have hfb := hf.continuousAt.tendsto.isBigO_one ℂ
  have hcb := hc.continuousAt.tendsto.isBigO_one ℂ
  have he1 : (fun b => f b * (g b - c b)) =O[𝓝 0] (fun b : ℂ => b ^ (N + 1)) := by
    simpa only [one_mul] using hfb.mul heG
  have he2 : (fun b => (f b - a b) * c b) =O[𝓝 0] (fun b : ℂ => b ^ (N + 1)) := by
    simpa only [mul_one] using heF.mul hcb
  have he := he1.add he2
  have herr : (fun b => f b * g b - a b * c b) =O[𝓝 0] (fun b : ℂ => b ^ (N + 1)) := by
    apply he.congr' (Eventually.of_forall fun b => ?_) Filter.EventuallyEq.rfl
    ring
  exact complexTaylorSeries_coeff_eq_of_isBigO (hf.mul hg) (ha.mul hc) N herr

theorem complexTaylorSeries_coeff_eq_composition {F f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (hF : AnalyticAt ℂ F (f 0)) (N : ℕ)
    (he : ∀ j ≤ N, coeff j (complexTaylorSeries f 0) = coeff j (complexTaylorSeries g 0)) :
    ∀ j ≤ N, coeff j (complexTaylorSeries (fun b => F (f b)) 0) =
      coeff j (complexTaylorSeries (fun b => F (g b)) 0) := by
  have h0 : f 0 = g 0 := by
    simpa [complexTaylorSeries] using he 0 (Nat.zero_le N)
  exact complexTaylorSeries_coeff_eq_of_analytic_composition hF hf hg rfl h0.symm N
    (isBigO_difference_of_complexTaylorSeries_coeff_eq hf hg N he)

end PGM
