import PLAStochastic.ForMathlib.Analysis.Complex.TaylorDisc

/-! # Cauchy budgets on reciprocal polynomial discs -/

noncomputable section
open Complex Set Metric
namespace PGM

theorem norm_sub_complexTaylorSum_le_polynomial_disc {F : ℂ → ℂ} {R X K E : ℝ}
    (hR : 0 < R) (hX : 0 < X)
    (hd : DifferentiableOn ℂ F (ball 0 (R / X)))
    (hm : ∀ b ∈ ball (0 : ℂ) (R / X), ‖F b‖ ≤ K * X * E)
    (n : ℕ) {b : ℂ} (hb : b ∈ ball (0 : ℂ) ((R / X) / 2)) :
    ‖F b - complexTaylorSum F n 0 b‖ ≤
      ((n.factorial : ℝ) * K / (R / 4) ^ n) * X ^ (n + 1) * E * ‖b‖ ^ n := by
  have h := norm_sub_complexTaylorSum_le_of_ball n (div_pos hR hX) hd hm hb
  simp only [sub_zero] at h
  have he : (R / X / 4) ^ n = (R / 4) ^ n / X ^ n := by
    rw [show R / X / 4 = (R / 4) / X by ring, div_pow]
  rw [he, div_div_eq_mul_div] at h
  apply h.trans_eq
  rw [pow_succ]
  ring

end PGM
