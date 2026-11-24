import PLAStochastic.Index.CEPS.Scaled.SurrogateSecondSlopeBudget
import PLAStochastic.Index.CEPS.Scaled.SurrogateSlopeInverse
import PLAStochastic.Index.CEPS.Scaled.SurrogateEntrance

/-! # Weighted entrance bounds through all root and marker collisions -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.surrogateEntrancePolynomialConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  Real.exp (dom.canonDriftTaylorBound N M (dom.μ₀ / 8)) *
    dom.surrogateSpatialSecondBound N M * (4 / cepsVarLo D) *
      dom.surrogateSlopePolynomialConstant N M

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem surrogateEntrancePolynomialConstant_pos (N : ℕ) (M : ℝ) :
    0 < dom.surrogateEntrancePolynomialConstant N M := by
  have := CepsCanonDomain.v_pos hW hθ hD
  have := cepsVarLo_pos hD
  have := surrogateSlopePolynomialConstant_pos dom hW hθ hD N M
  unfold CepsCanonDomain.surrogateEntrancePolynomialConstant
    CepsCanonDomain.surrogateSpatialSecondBound
  positivity

include hW hθ hD in
theorem cepsScaledSurrogateEntrance_weighted_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    ‖cepsScaledSurrogateEntrance dom ρW N lam z b‖ ≤
      dom.surrogateEntrancePolynomialConstant N M * (1 + |lam| + Real.sqrt ‖z‖) *
        (1 + Real.exp (((cepsScaledSignedRoot D θ ρW lam z (-1) b -
          cepsScaledSignedRoot D θ ρW lam z 1 b) * (1 + b * lam)).re) +
            Real.exp (((cepsScaledSignedRoot D θ ρW lam z (-1) b - b * z) * (1 + b * lam)).re)) := by
  let B := dom.canonDriftTaylorBound N M (dom.μ₀ / 8)
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let xm := cepsScaledSignedRoot D θ ρW lam z (-1) b
  let xp := cepsScaledSignedRoot D θ ρW lam z 1 b
  let w : ℂ := 1 + b * lam
  let E := Real.exp (-(xm * w).re) + Real.exp (-(xp * w).re) + Real.exp (-((b * z) * w).re)
  have hbase := entranceScaleCurve_spatial_bounds dom hW hθ hD N M lam hb
    (entranceScaleCurve_mark_mem dom hD N M lam hb)
  obtain ⟨hμ, hq, _⟩ := canonScaleCurve_bounds dom hW hθ hD lam hz (sign := 1) (by norm_num) hbase.1
  have hζ : ‖b ^ 2 * z‖ ≤ dom.c₀ / 2 := by simpa only [pow_two, mul_assoc] using hbase.2.le
  have hL := cepsCanonDriftTaylor_norm_le dom hW hθ hD hf hη hM N hN hμ.le hq.le hζ
  have heL : ‖exp (cepsCanonDriftTaylor dom ρW N (b * lam)
      (cepsComplexScaledDiscount lam z b) (b ^ 2 * z))‖ ≤ Real.exp B := by
    rw [norm_exp]
    exact Real.exp_le_exp.mpr ((re_le_norm _).trans hL)
  have hQ := (cepsScaledSurrogateMarkQuotient_budget dom hW hθ hD N M lam hz).2 b hb
  have hQinv : ‖(cepsQ D θ ρW (b * lam) (cepsComplexScaledDiscount lam z b) (b ^ 2 * z))⁻¹‖ ≤
      4 / cepsVarLo D := by
    rw [norm_inv]
    have hv := div_pos (cepsVarLo_pos hD) (by norm_num : (0 : ℝ) < 4)
    exact ((inv_le_inv₀ (hv.trans_le hQ) hv).mpr hQ).trans_eq (by ring)
  have hS := cepsScaledSurrogateDenominator_inverse_weighted_bound dom hW hθ hD hf hη hM N hN lam hz
    (ball_subset_ball (min_le_left _ _) hb)
  have hDD := cepsScaledSurrogateG_second_dslope_weighted_budget dom hW hθ hD hf hη hM N hN lam hz hb
  have hC : 0 ≤ dom.surrogateSpatialSecondBound N M := by
    unfold CepsCanonDomain.surrogateSpatialSecondBound
    have := CepsCanonDomain.v_pos hW hθ hD
    positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hDDpos : 0 ≤ dom.surrogateSpatialSecondBound N M * E := mul_nonneg hC hE
  have hQpos : 0 ≤ 4 / cepsVarLo D := div_nonneg (by norm_num) (cepsVarLo_pos hD).le
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hSpos : 0 ≤ dom.surrogateSlopePolynomialConstant N M * X * Real.exp (xm * w).re :=
    mul_nonneg (mul_nonneg (surrogateSlopePolynomialConstant_pos dom hW hθ hD N M).le hX) (Real.exp_pos _).le
  unfold cepsScaledSurrogateEntrance
  rw [div_eq_mul_inv, mul_inv, norm_mul, norm_mul, norm_mul, norm_neg]
  rw [← mul_assoc]
  apply (mul_le_mul (mul_le_mul (mul_le_mul heL hDD (norm_nonneg _) (Real.exp_pos B).le)
    hQinv (norm_nonneg _) (mul_nonneg (Real.exp_pos B).le hDDpos))
      hS (norm_nonneg _) (mul_nonneg (mul_nonneg (Real.exp_pos B).le hDDpos) hQpos)).trans_eq
  have hExp : E * Real.exp (xm * w).re =
      1 + Real.exp (((xm - xp) * w).re) + Real.exp (((xm - b * z) * w).re) := by
    dsimp only [E]
    rw [add_mul, add_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    simp only [neg_add_cancel, Real.exp_zero, sub_mul, sub_re]
    ring_nf
  change Real.exp B * (dom.surrogateSpatialSecondBound N M * E) * (4 / cepsVarLo D) *
    (dom.surrogateSlopePolynomialConstant N M * X * Real.exp (xm * w).re) = _
  unfold CepsCanonDomain.surrogateEntrancePolynomialConstant
  calc
    _ = (Real.exp B * dom.surrogateSpatialSecondBound N M * (4 / cepsVarLo D) *
        dom.surrogateSlopePolynomialConstant N M * X) * (E * Real.exp (xm * w).re) := by ring
    _ = _ := by rw [hExp]

include hW hθ hD in
theorem cepsScaledSurrogateEntrance_polynomial_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    ‖cepsScaledSurrogateEntrance dom ρW N lam z b‖ ≤
      dom.surrogateEntrancePolynomialConstant N M * (1 + |lam| + Real.sqrt ‖z‖) *
        (2 + Real.exp (((cepsScaledSignedRoot D θ ρW lam z (-1) b - b * z) * (1 + b * lam)).re)) := by
  have hc := (cepsScaledSurrogate_constants dom hW hθ hD N M).2.1.le
  have hg := cepsScaledEffectiveGap_sector dom hW hθ hD N M lam hz
    (ball_subset_ball (min_le_left _ _) (ball_subset_ball (min_le_left _ _) hb))
  have hgr : 0 ≤ (cepsScaledEffectiveGap D θ ρW lam z b).re :=
    (mul_nonneg hc (norm_nonneg _)).trans hg
  have he : (((cepsScaledSignedRoot D θ ρW lam z (-1) b -
      cepsScaledSignedRoot D θ ρW lam z 1 b) * (1 + b * lam)).re) =
      -(cepsScaledEffectiveGap D θ ρW lam z b).re := by
    unfold cepsScaledEffectiveGap
    rw [← neg_sub, neg_mul, neg_re]
  have hexp : Real.exp (((cepsScaledSignedRoot D θ ρW lam z (-1) b -
      cepsScaledSignedRoot D θ ρW lam z 1 b) * (1 + b * lam)).re) ≤ 1 := by
    rw [he]
    exact (Real.exp_le_exp.mpr (neg_nonpos.mpr hgr)).trans_eq Real.exp_zero
  apply (cepsScaledSurrogateEntrance_weighted_budget dom hW hθ hD hf hη hM N hN lam hz hb).trans
  apply mul_le_mul_of_nonneg_left (by linarith)
  exact mul_nonneg (surrogateEntrancePolynomialConstant_pos dom hW hθ hD N M).le (by positivity)

end PGM
