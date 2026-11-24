import PLAStochastic.Index.CEPS.Scaled.SurrogateBridgeWeighted
import PLAStochastic.Index.CEPS.Scaled.CanonPolynomialRadius

/-! # Weighted square and half-line bridge bounds without singular root gaps -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

private theorem square_exp_weight (p m : ℝ) :
    (Real.exp (-p)) ^ 2 * Real.exp m = Real.exp (-(2 * p - m)) := by
  rw [pow_two, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

def CepsCanonDomain.surrogateHalfBridgeWeightedConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  dom.scaledGapBound * dom.scaledCoordinateRatioBound *
    (v * Real.exp (2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8)))

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSurrogateBridgeCorrection_weighted_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.surrogateRegularScaleRadius N M lam z)) :
    ‖cepsScaledSurrogateBridgeCorrection dom ρW N lam z b‖ ≤
      dom.surrogateBridgeWeightedConstant N M * (1 + |lam| + Real.sqrt ‖z‖) *
        Real.exp (-((2 * cepsScaledSignedRoot D θ ρW lam z 1 b -
          cepsScaledSignedRoot D θ ρW lam z (-1) b) * (1 + b * lam)).re) := by
  let p := (cepsScaledSignedRoot D θ ρW lam z 1 b * (1 + b * lam)).re
  let m := (cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + b * lam)).re
  have hbC : b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z) := ball_subset_ball
    ((min_le_left _ _).trans ((min_le_left _ _).trans (half_le_self (canonScaleRadius_pos dom hW hθ hD lam z).le))) hb
  have hp := cepsScaledSurrogateG_root_weighted_budget dom hW hθ hD hf hη hM N hN lam hz (by norm_num : ‖(1 : ℂ)‖ ≤ 1) hbC
  have hs := cepsScaledSurrogateDenominator_inverse_weighted_bound dom hW hθ hD hf hη hM N hN lam hz hb
  rw [cepsScaledSurrogateBridgeCorrection_eq_square dom hW hθ hD hf hη hM N hN lam hz hb,
    div_eq_mul_inv, norm_mul, norm_neg, norm_pow]
  apply (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hp 2) hs (norm_nonneg _) (by positivity)).trans_eq
  have hRe : ((2 * cepsScaledSignedRoot D θ ρW lam z 1 b -
      cepsScaledSignedRoot D θ ρW lam z (-1) b) * (1 + b * lam)).re = 2 * p - m := by
    rw [sub_mul, sub_re, mul_assoc]
    congr 1
    exact re_ofReal_mul 2 _
  rw [hRe]
  unfold CepsCanonDomain.surrogateBridgeWeightedConstant
  calc
    _ = (v * Real.exp (2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8))) ^ 2 *
        dom.surrogateSlopePolynomialConstant N M * (1 + |lam| + Real.sqrt ‖z‖) *
          ((Real.exp (-p)) ^ 2 * Real.exp m) := by ring
    _ = _ := by rw [square_exp_weight]

include hW hθ hD in
theorem cepsScaledSurrogateHalfBridge_weighted_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z)) :
    ‖cepsScaledSurrogateHalfBridge dom ρW N lam z b‖ ≤
      dom.surrogateHalfBridgeWeightedConstant N M * (1 + |lam| + Real.sqrt ‖z‖) *
        Real.exp (-(cepsScaledSignedRoot D θ ρW lam z 1 b * (1 + b * lam)).re) := by
  have hbRad := ball_subset_ball (min_le_left _ _) (ball_subset_ball (min_le_left _ _) hb)
  have hK := (cepsScaledSurrogate_constants dom hW hθ hD N M).1.le
  have hgap := (cepsScaledRootGap_norm_le dom hW hθ hD lam hz hb).trans
    (mul_le_mul_of_nonneg_left ((cepsScaledRootCoordinate_budget dom hW hθ hD lam hz).2 b hbRad) hK)
  have hgapPoly := hgap.trans (mul_le_mul_of_nonneg_left
    (scaledRootCoordinateBound_le_polynomial dom hW hθ hD lam z) hK)
  have hp := cepsScaledSurrogateG_root_weighted_budget dom hW hθ hD hf hη hM N hN lam hz (by norm_num : ‖(1 : ℂ)‖ ≤ 1) hb
  unfold cepsScaledSurrogateHalfBridge
  rw [norm_mul]
  exact (mul_le_mul hgapPoly hp (norm_nonneg _) ((norm_nonneg _).trans hgapPoly)).trans_eq
    (by unfold CepsCanonDomain.surrogateHalfBridgeWeightedConstant CepsCanonDomain.scaledGapBound; ring)

end PGM
