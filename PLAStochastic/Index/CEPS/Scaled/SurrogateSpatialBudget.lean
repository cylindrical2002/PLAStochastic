import PLAStochastic.Index.CEPS.Scaled.SurrogateGJoint

/-! # Spatial derivative budgets retaining the surrogate exponential weight -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSurrogateG_spatial_deriv_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) (n : ℕ) {ξ : ℂ}
    (hξ : ‖ξ‖ ≤ dom.entranceSpatialScaleRadius lam z / 2) :
    ‖iteratedDeriv n (cepsScaledSurrogateG dom ρW N lam z b) ξ‖ ≤
      ((n.factorial : ℝ) * (Real.exp 2 *
        (v * Real.exp (2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8)))) / (1 / 2 : ℝ) ^ n) *
          Real.exp (-(ξ * (1 + b * lam)).re) := by
  let R := dom.entranceSpatialScaleRadius lam z
  let G := cepsScaledSurrogateG dom ρW N lam z b
  let w : ℂ := 1 + b * lam
  let F : ℝ := v * Real.exp (2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8))
  have hC : 0 ≤ dom.actualScaledRootBound lam z := (norm_nonneg _).trans
    ((cepsScaledSignedRoot_budget dom hW hθ hD lam hz (by norm_num : ‖(1 : ℂ)‖ ≤ 1)).2 0
      (mem_ball_self (actualRootScaleRadius_pos dom hW hθ hD lam z)))
  have hR : 2 ≤ R := by dsimp [R, CepsCanonDomain.entranceSpatialScaleRadius]; nlinarith [abs_nonneg lam, Real.sqrt_nonneg ‖z‖]
  have hsub : ball ξ (1 : ℝ) ⊆ ball (0 : ℂ) R := by
    intro ζ hζ
    have hn := norm_add_le (ζ - ξ) ξ
    rw [sub_add_cancel] at hn
    have hz1 : ‖ζ - ξ‖ < 1 := by simpa only [dist_eq_norm] using mem_ball.mp hζ
    apply mem_ball_zero_iff.mpr
    nlinarith
  have hdJ := cepsScaledSurrogateG_differentiableOn_joint dom hW hθ hD (M := M) hf hη N hN lam hz
  have hdG : DifferentiableOn ℂ G (ball 0 R) := fun ζ hζ =>
    (differentiableAt_slice_snd (isOpen_ball.prod isOpen_ball) hdJ
      (show (b, ζ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z) ×ˢ ball (0 : ℂ) R from ⟨hb, hζ⟩)).differentiableWithinAt
  have ht := entranceScaleCurve_product_bound dom hD N M lam hb
  have hbase : dom.canonScaleBase ≤ 1 := min_le_left _ _
  have hμ1 : ‖b * (lam : ℂ)‖ ≤ 1 := by
    rw [norm_mul, norm_real, Real.norm_eq_abs]
    nlinarith [norm_nonneg b, abs_nonneg lam, Real.sqrt_nonneg ‖z‖]
  have hw : ‖w‖ ≤ 2 := by
    have hn := norm_add_le (1 : ℂ) (b * (lam : ℂ))
    rw [norm_one] at hn
    exact hn.trans (by linarith)
  have hF : 0 ≤ F := mul_nonneg (CepsCanonDomain.v_pos hW hθ hD).le (Real.exp_pos _).le
  have hm : ∀ ζ ∈ ball ξ (1 : ℝ), ‖G ζ‖ ≤ Real.exp (-(ξ * w).re) * (Real.exp 2 * F) := by
    intro ζ hζ
    obtain ⟨hbC, hsp⟩ := entranceScaleCurve_spatial_bounds dom hW hθ hD N M lam hb (hsub hζ)
    obtain ⟨hμ, hq, _⟩ := canonScaleCurve_bounds dom hW hθ hD lam hz (sign := 1) (by norm_num) hbC
    have hWgt := (cepsCanonSurrogateWeight_bounds dom hW hθ hD hf hη hM N hN hμ.le hq.le hsp.le).2
    have hExp : ‖exp (-(ζ - ξ) * w)‖ ≤ Real.exp 2 := by
      rw [norm_exp]
      apply Real.exp_le_exp.mpr
      have hr := re_le_norm (-(ζ - ξ) * w)
      rw [norm_mul, norm_neg] at hr
      have hz1 : ‖ζ - ξ‖ ≤ 1 := by simpa only [dist_eq_norm] using (mem_ball.mp hζ).le
      exact hr.trans (by nlinarith [norm_nonneg (ζ - ξ)])
    have he : -ζ * w = -ξ * w + -(ζ - ξ) * w := by ring
    change ‖exp (-ζ * w) * cepsCanonSurrogateWeight dom ρW N (b * lam)
      (cepsComplexScaledDiscount lam z b) (b * ζ)‖ ≤ _
    rw [he, exp_add, norm_mul, norm_mul]
    apply (mul_le_mul (mul_le_mul_of_nonneg_left hExp (norm_nonneg _)) hWgt
      (norm_nonneg _) (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)).trans_eq
    rw [norm_exp, neg_mul, neg_re]
    ring
  have h := norm_iteratedDeriv_le_of_ball n (by norm_num : (0 : ℝ) < 1) (hdG.mono hsub) hm
  apply h.trans_eq
  ring

end PGM
