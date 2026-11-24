import PLAStochastic.Index.CEPS.Scaled.SurrogateSlopeInverse
import PLAStochastic.Index.CEPS.Scaled.SurrogateBridgeCorrection

/-! # Bridge weights without division by the root gap -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.surrogateBridgeWeightedConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  (v * Real.exp (2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8))) ^ 2 *
    dom.surrogateSlopePolynomialConstant N M

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSurrogateG_root_weighted_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {sign b : ℂ} (hsign : ‖sign‖ ≤ 1)
    (hb : b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z)) :
    ‖cepsScaledSurrogateG dom ρW N lam z b (cepsScaledSignedRoot D θ ρW lam z sign b)‖ ≤
      (v * Real.exp (2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8))) *
        Real.exp (-(cepsScaledSignedRoot D θ ρW lam z sign b * (1 + b * lam)).re) := by
  obtain ⟨hμ, hq, hζ⟩ := canonScaleCurve_bounds dom hW hθ hD lam hz hsign hb
  have hF := (cepsCanonSurrogateWeight_bounds dom hW hθ hD hf hη hM N hN hμ.le hq.le hζ.le).2
  rw [cepsScaledSurrogateG, norm_mul, norm_exp, neg_mul, neg_re]
  exact (mul_le_mul_of_nonneg_left hF (Real.exp_pos _).le).trans_eq (by ring)

include hW hθ hD in
theorem cepsScaledSurrogateBridgeCorrection_eq_square {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.surrogateRegularScaleRadius N M lam z)) :
    cepsScaledSurrogateBridgeCorrection dom ρW N lam z b =
      -(cepsScaledSurrogateG dom ρW N lam z b (cepsScaledSignedRoot D θ ρW lam z 1 b)) ^ 2 /
        cepsScaledSurrogateDenominator dom ρW N lam z b := by
  have hS0 := cepsScaledSurrogateDenominator_ne_zero dom hW hθ hD hf hη hM N hN lam hz hb
  have hid := sub_smul_dslope (cepsScaledSurrogateG dom ρW N lam z b)
    (cepsScaledSignedRoot D θ ρW lam z (-1) b) (cepsScaledSignedRoot D θ ρW lam z 1 b)
  simp only [smul_eq_mul] at hid
  change (_ - _) * cepsScaledSurrogateDenominator dom ρW N lam z b = _ at hid
  unfold cepsScaledSurrogateBridgeCorrection cepsScaledSurrogateBridge cepsScaledSurrogateHalfBridge
  field_simp
  linear_combination -(cepsScaledSurrogateG dom ρW N lam z b (cepsScaledSignedRoot D θ ρW lam z 1 b)) * hid

include hW hθ hD in
theorem cepsScaledSurrogateBridge_weighted_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.surrogateRegularScaleRadius N M lam z)) :
    ‖cepsScaledSurrogateBridge dom ρW N lam z b‖ ≤
      dom.surrogateBridgeWeightedConstant N M * (1 + |lam| + Real.sqrt ‖z‖) *
        Real.exp (-(cepsScaledSignedRoot D θ ρW lam z 1 b * (1 + b * lam)).re) := by
  have hbC : b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z) := ball_subset_ball
    ((min_le_left _ _).trans ((min_le_left _ _).trans (half_le_self (canonScaleRadius_pos dom hW hθ hD lam z).le))) hb
  have hp := cepsScaledSurrogateG_root_weighted_budget dom hW hθ hD hf hη hM N hN lam hz (by norm_num : ‖(1 : ℂ)‖ ≤ 1) hbC
  have hm := cepsScaledSurrogateG_root_weighted_budget dom hW hθ hD hf hη hM N hN lam hz (by norm_num : ‖(-1 : ℂ)‖ ≤ 1) hbC
  have hs := cepsScaledSurrogateDenominator_inverse_weighted_bound dom hW hθ hD hf hη hM N hN lam hz hb
  unfold cepsScaledSurrogateBridge
  rw [div_eq_mul_inv, norm_mul, norm_mul, norm_neg]
  apply (mul_le_mul (mul_le_mul hp hm (norm_nonneg _) ((norm_nonneg _).trans hp)) hs
    (norm_nonneg _) (mul_nonneg ((norm_nonneg _).trans hp) ((norm_nonneg _).trans hm))).trans_eq
  have he : Real.exp (-(cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + b * lam)).re) *
      Real.exp (cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + b * lam)).re = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  unfold CepsCanonDomain.surrogateBridgeWeightedConstant
  calc
    _ = (v * Real.exp (2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8))) ^ 2 *
        dom.surrogateSlopePolynomialConstant N M * (1 + |lam| + Real.sqrt ‖z‖) *
          Real.exp (-(cepsScaledSignedRoot D θ ρW lam z 1 b * (1 + b * lam)).re) *
            (Real.exp (-(cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + b * lam)).re) *
              Real.exp (cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + b * lam)).re) := by ring
    _ = _ := by rw [he, mul_one]

end PGM
