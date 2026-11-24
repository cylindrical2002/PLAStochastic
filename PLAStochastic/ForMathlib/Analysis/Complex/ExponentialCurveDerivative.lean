import PLAStochastic.ForMathlib.Analysis.Complex.PartialDerivChain
import PLAStochastic.ForMathlib.Analysis.Complex.PartialDeriv

/-! # Cauchy budgets for an exponential times a moving two-variable value -/

noncomputable section
open Complex Set Metric
namespace PGM

theorem norm_deriv_exponential_curve_le {F : ℂ × ℂ → ℂ} {R S B : ℝ}
    (hR : 0 < R) (hS : 0 < S)
    (hF : DifferentiableOn ℂ F (ball 0 R ×ˢ ball 0 S))
    (hB : ∀ x ∈ ball 0 R ×ˢ ball 0 S, ‖F x‖ ≤ B)
    {q r : ℂ → ℂ} {z b w : ℂ} (hq : DifferentiableAt ℂ q z)
    (hr : DifferentiableAt ℂ r z) (hq0 : ‖q z‖ ≤ R / 2) (hr0 : ‖b * r z‖ ≤ S / 2) :
    ‖deriv (fun u => exp (-r u * w) * F (q u, b * r u)) z‖ ≤
      Real.exp (-(r z * w).re) * B *
        (‖deriv r z‖ * ‖w‖ + ‖deriv q z‖ / (R / 4) + ‖b‖ * ‖deriv r z‖ / (S / 4)) := by
  have hx : (q z, b * r z) ∈ ball (0 : ℂ) R ×ˢ ball (0 : ℂ) S :=
    ⟨mem_ball_zero_iff.mpr (hq0.trans_lt (by linarith)),
      mem_ball_zero_iff.mpr (hr0.trans_lt (by linarith))⟩
  have hqsub : ball (q z) (R / 2) ⊆ ball (0 : ℂ) R := by
    intro u hu
    have hn := norm_add_le (u - q z) (q z)
    rw [sub_add_cancel] at hn
    exact mem_ball_zero_iff.mpr (by have := mem_ball.mp hu; rw [dist_eq_norm] at this; linarith)
  have hrsub : ball (b * r z) (S / 2) ⊆ ball (0 : ℂ) S := by
    intro u hu
    have hn := norm_add_le (u - b * r z) (b * r z)
    rw [sub_add_cancel] at hn
    exact mem_ball_zero_iff.mpr (by have := mem_ball.mp hu; rw [dist_eq_norm] at this; linarith)
  have hdq : DifferentiableOn ℂ (fun u => F (u, b * r z)) (ball (q z) (R / 2)) :=
    fun u hu => (differentiableAt_slice_fst (G := F) (z := u) (w := b * r z)
      (isOpen_ball.prod isOpen_ball) hF ⟨hqsub hu, hx.2⟩).differentiableWithinAt
  have hdr : DifferentiableOn ℂ (fun u => F (q z, u)) (ball (b * r z) (S / 2)) :=
    fun u hu => (differentiableAt_slice_snd (G := F) (z := q z) (w := u)
      (isOpen_ball.prod isOpen_ball) hF ⟨hx.1, hrsub hu⟩).differentiableWithinAt
  have hqjet := norm_iteratedDeriv_le_of_ball 1 (half_pos hR) hdq
    (fun u hu => hB (u, b * r z) ⟨hqsub hu, hx.2⟩)
  have hrjet := norm_iteratedDeriv_le_of_ball 1 (half_pos hS) hdr
    (fun u hu => hB (q z, u) ⟨hx.1, hrsub hu⟩)
  simp only [iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, one_mul, pow_one,
    show R / 2 / 2 = R / 4 by ring, show S / 2 / 2 = S / 4 by ring] at hqjet hrjet
  have hF0 := (hF _ hx).differentiableAt ((isOpen_ball.prod isOpen_ball).mem_nhds hx)
  have hcurve := hasDerivAt_comp_complex_partials hF0 hq.hasDerivAt (hr.hasDerivAt.const_mul b)
  have hnorm : ‖deriv (fun u => F (q u, b * r u)) z‖ ≤
      B * (‖deriv q z‖ / (R / 4) + ‖b‖ * ‖deriv r z‖ / (S / 4)) := by
    rw [hcurve.deriv]
    apply (norm_add_le _ _).trans
    rw [norm_mul, norm_mul, norm_mul]
    apply (add_le_add (mul_le_mul_of_nonneg_right hqjet (norm_nonneg _))
      (mul_le_mul_of_nonneg_right hrjet (by positivity : 0 ≤ ‖b‖ * ‖deriv r z‖))).trans_eq
    ring
  have hExp := ((hr.hasDerivAt.neg).mul_const w).cexp
  have hd := hExp.mul hcurve
  simp only [Pi.mul_def, Pi.neg_def] at hd
  rw [hd.deriv]
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_neg, norm_exp, neg_mul, neg_re]
  rw [← hcurve.deriv]
  apply (add_le_add
    (mul_le_mul_of_nonneg_left (hB _ hx)
      (by positivity : 0 ≤ Real.exp (-(r z * w).re) * (‖deriv r z‖ * ‖w‖)))
    (mul_le_mul_of_nonneg_left hnorm (Real.exp_pos _).le)).trans_eq
  ring

end PGM
