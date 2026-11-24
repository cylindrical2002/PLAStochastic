import PLAStochastic.Index.CEPS.Scaled.SurrogateHalfEntrance
import PLAStochastic.Index.CEPS.Scaled.SurrogateEntranceBudget
import PLAStochastic.Index.CEPS.Scaled.PositiveMarkerGap

/-! # Uniform positive-side half-line and regular entrance budgets -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.surrogateHalfEntranceBound {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  Real.exp (dom.canonDriftTaylorBound N M (dom.μ₀ / 8)) * (4 / cepsVarLo D) /
    dom.positiveMarkerGapLower

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSurrogateMarkExp_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    ‖exp (cepsCanonDriftTaylor dom ρW N (b * lam)
      (cepsComplexScaledDiscount lam z b) (b ^ 2 * z))‖ ≤
        Real.exp (dom.canonDriftTaylorBound N M (dom.μ₀ / 8)) := by
  have hbase := entranceScaleCurve_spatial_bounds dom hW hθ hD N M lam hb
    (entranceScaleCurve_mark_mem dom hD N M lam hb)
  obtain ⟨hμ, hq, _⟩ := canonScaleCurve_bounds dom hW hθ hD lam hz (sign := 1) (by norm_num) hbase.1
  have hζ : ‖b ^ 2 * z‖ ≤ dom.c₀ / 2 := by simpa only [pow_two, mul_assoc] using hbase.2.le
  rw [norm_exp]
  exact Real.exp_le_exp.mpr ((re_le_norm _).trans
    (cepsCanonDriftTaylor_norm_le dom hW hθ hD hf hη hM N hN hμ.le hq.le hζ))

include hW hθ hD in
theorem cepsScaledSurrogateMarkQuotient_inverse_budget (N : ℕ) (M lam : ℝ)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    ‖(cepsQ D θ ρW (b * lam) (cepsComplexScaledDiscount lam z b) (b ^ 2 * z))⁻¹‖ ≤
      4 / cepsVarLo D := by
  have hQ := (cepsScaledSurrogateMarkQuotient_budget dom hW hθ hD N M lam hz).2 b hb
  rw [norm_inv]
  have hv := div_pos (cepsVarLo_pos hD) (by norm_num : (0 : ℝ) < 4)
  exact ((inv_le_inv₀ (hv.trans_le hQ) hv).mpr hQ).trans_eq (by ring)

include hW hθ hD in
theorem surrogateHalfEntranceBound_pos (N : ℕ) (M : ℝ) :
    0 < dom.surrogateHalfEntranceBound N M := by
  have := positiveMarkerGapLower_pos dom hW hθ hD
  have := cepsVarLo_pos hD
  unfold CepsCanonDomain.surrogateHalfEntranceBound
  positivity

include hW hθ hD in
theorem cepsScaledSurrogateHalfEntrance_positive_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) (hlam : 1 ≤ lam) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.pairPolynomialScaleBase N M / (1 + |lam| + Real.sqrt ‖z‖))) :
    ‖cepsScaledSurrogateHalfEntrance dom ρW N lam z b‖ ≤ dom.surrogateHalfEntranceBound N M := by
  have hbE := ball_subset_ball (pairPolynomialScaleRadius_le dom hW hθ hD N M lam z).2 hb
  have hE := cepsScaledSurrogateMarkExp_budget dom hW hθ hD hf hη hM N hN lam hz hbE
  have hQ := cepsScaledSurrogateMarkQuotient_inverse_budget dom hW hθ hD N M lam hz hbE
  have hgap := cepsScaledPositiveMarkerGap_norm_lower dom hW hθ hD N M lam hlam hz hb
  have hl := positiveMarkerGapLower_pos dom hW hθ hD
  have hi : ‖(b * z - cepsScaledSignedRoot D θ ρW lam z (-1) b)⁻¹‖ ≤ dom.positiveMarkerGapLower⁻¹ := by
    rw [norm_inv]
    exact (inv_le_inv₀ (hl.trans_le hgap) hl).mpr hgap
  unfold cepsScaledSurrogateHalfEntrance
  rw [div_eq_mul_inv, mul_inv, norm_mul, norm_mul, ← mul_assoc]
  exact (mul_le_mul (mul_le_mul hE hQ (norm_nonneg _) (Real.exp_pos _).le) hi
    (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le ((norm_nonneg _).trans hQ))).trans_eq
      (by unfold CepsCanonDomain.surrogateHalfEntranceBound; ring)

include hW hθ hD in
theorem cepsScaledSurrogateEntrance_positive_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) (hlam : 0 ≤ lam) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.pairPolynomialScaleBase N M / (1 + |lam| + Real.sqrt ‖z‖))) :
    ‖cepsScaledSurrogateEntrance dom ρW N lam z b‖ ≤
      3 * dom.surrogateEntrancePolynomialConstant N M * (1 + |lam| + Real.sqrt ‖z‖) := by
  have hbE := ball_subset_ball (pairPolynomialScaleRadius_le dom hW hθ hD N M lam z).2 hb
  have hd := (cepsScaledPairRoot_positive_directions dom hW hθ hD N M lam hlam hz hb).1
  have hlo : 0 ≤ ((-cepsScaledSignedRoot D θ ρW lam z (-1) b + b * z) * (1 + b * lam)).re :=
    (div_nonneg (norm_nonneg _) (by positivity)).trans hd
  have he : Real.exp (((cepsScaledSignedRoot D θ ρW lam z (-1) b - b * z) * (1 + b * lam)).re) ≤ 1 := by
    rw [show cepsScaledSignedRoot D θ ρW lam z (-1) b - b * z =
      -(-cepsScaledSignedRoot D θ ρW lam z (-1) b + b * z) by ring, neg_mul, neg_re]
    exact (Real.exp_le_exp.mpr (neg_nonpos.mpr hlo)).trans_eq Real.exp_zero
  apply (cepsScaledSurrogateEntrance_polynomial_budget dom hW hθ hD hf hη hM N hN lam hz hbE).trans
  have hp : 0 ≤ dom.surrogateEntrancePolynomialConstant N M * (1 + |lam| + Real.sqrt ‖z‖) :=
    mul_nonneg (surrogateEntrancePolynomialConstant_pos dom hW hθ hD N M).le (by positivity)
  have hh := mul_le_mul_of_nonneg_left (show 2 + Real.exp
    (((cepsScaledSignedRoot D θ ρW lam z (-1) b - b * z) * (1 + b * lam)).re) ≤ 3 by linarith) hp
  exact hh.trans_eq (by ring)

end PGM
