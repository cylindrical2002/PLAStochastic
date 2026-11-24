import PLAStochastic.Index.CEPS.Scaled.TrueHalfEntrance

/-! # Actual positive-tail entrance correction retains its root weights -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.trueEntranceCorrectionConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (M : ℝ) : ℝ :=
  dom.trueHalfEntranceConstant * dom.trueSpatialBound M 1 *
    (2 * dom.surrogateSlopePolynomialConstant 0 M)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem trueEntranceCorrectionConstant_nonneg {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ dom.trueEntranceCorrectionConstant M := by
  have := trueHalfEntranceConstant_pos dom hW hθ hD
  have := trueSpatialBound_nonneg dom hW hθ hD hM 1
  have := surrogateSlopePolynomialConstant_pos dom hW hθ hD 0 M
  unfold CepsCanonDomain.trueEntranceCorrectionConstant
  positivity

include hW hθ hD in
theorem cepsScaledTrueG_first_dslope_weighted_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m) (lam : ℝ)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDenominatorScaleRadius M lam z)) :
    ‖dslope (cepsScaledTrueG dom ρW lam z b)
      (cepsScaledSignedRoot D θ ρW lam z 1 b) ((b : ℂ) * z)‖ ≤
        dom.trueSpatialBound M 1 *
          (Real.exp (-(cepsScaledSignedRoot D θ ρW lam z 1 b * (1 + (b : ℂ) * lam)).re) +
            Real.exp (-(((b : ℂ) * z) * (1 + (b : ℂ) * lam)).re)) := by
  have hbE := ball_subset_ball (trueDenominatorScaleRadius_le dom hW hθ hD M lam z) hb
  have hR := (entranceScale_constants dom hW hθ hD 0 M lam z).2
  have hC := trueSpatialBound_nonneg dom hW hθ hD ((cepsSobolev_nonneg m η fW).trans hM) 1
  have hG := cepsScaledTrueG_spatial_differentiableOn dom hW hθ hD 0 M lam hz hbE
  apply cepsNormal_norm_dslope_le_weighted hR hC hG _
    (entranceScaleCurve_root_norm_le_half dom hW hθ hD 0 M lam hz hbE (by norm_num))
    (entranceScaleCurve_mark_norm_le_half dom hW hθ hD 0 M lam hz hbE)
  intro ξ hξ
  simpa only [iteratedDeriv_one] using
    cepsScaledTrueG_spatial_budget dom hW hθ hD hf hη hM hm lam hz hb 1 hξ

include hW hθ hD in
theorem cepsScaledTrueEntranceCorrection_positive_weighted_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m) (lam : ℝ) (hlam : 1 ≤ lam)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDenominatorScaleRadius M lam z)) :
    ‖cepsScaledTrueEntranceCorrection dom ρW lam z b‖ ≤
      dom.trueEntranceCorrectionConstant M * (1 + |lam| + Real.sqrt ‖z‖) *
        (Real.exp (((cepsScaledSignedRoot D θ ρW lam z (-1) b -
          cepsScaledSignedRoot D θ ρW lam z 1 b) * (1 + (b : ℂ) * lam)).re) +
            Real.exp (((cepsScaledSignedRoot D θ ρW lam z (-1) b - (b : ℂ) * z) *
              (1 + (b : ℂ) * lam)).re)) := by
  let p := (cepsScaledSignedRoot D θ ρW lam z 1 b * (1 + (b : ℂ) * lam)).re
  let a := (cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + (b : ℂ) * lam)).re
  let t := (((b : ℂ) * z) * (1 + (b : ℂ) * lam)).re
  have hbP : (b : ℂ) ∈ ball (0 : ℂ) (dom.pairPolynomialScaleBase 0 M /
      (1 + |lam| + Real.sqrt ‖z‖)) :=
    ball_subset_ball (div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)) hb
  have hhalf := cepsScaledTrueHalfEntrance_positive_budget dom hW hθ hD M lam hlam hz hb
  have hfirst := cepsScaledTrueG_first_dslope_weighted_budget dom hW hθ hD hf hη hM hm lam hz hb
  have hS := cepsScaledTrueDenominator_inverse_weighted_budget dom hW hθ hD hf hη hM hm lam hz hb
  rw [cepsScaledTrueEntranceCorrection_eq_firstSlope dom hW hθ hD hf hη hM hm lam hz hb
    (cepsScaledPositiveMarkerGap_ne_zero dom hW hθ hD 0 M lam hlam hz hbP),
      div_eq_mul_inv, norm_mul, norm_mul, norm_neg]
  apply (mul_le_mul (mul_le_mul hhalf hfirst (norm_nonneg _) ((norm_nonneg _).trans hhalf)) hS
    (norm_nonneg _) (mul_nonneg ((norm_nonneg _).trans hhalf) ((norm_nonneg _).trans hfirst))).trans_eq
  have he : (Real.exp (-p) + Real.exp (-t)) * Real.exp a =
      Real.exp (a - p) + Real.exp (a - t) := by
    rw [add_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1 <;> congr 1 <;> ring
  unfold CepsCanonDomain.trueEntranceCorrectionConstant
  simp only [sub_mul, sub_re]
  calc
    _ = (dom.trueHalfEntranceConstant * dom.trueSpatialBound M 1 *
        (2 * dom.surrogateSlopePolynomialConstant 0 M) * (1 + |lam| + Real.sqrt ‖z‖)) *
          ((Real.exp (-p) + Real.exp (-t)) * Real.exp a) := by ring
    _ = _ := by rw [he]

end PGM
