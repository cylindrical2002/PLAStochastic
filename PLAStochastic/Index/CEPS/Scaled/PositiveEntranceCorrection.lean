import PLAStochastic.Index.CEPS.Scaled.SurrogateHalfEntranceBudget
import PLAStochastic.Index.CEPS.Scaled.SurrogateFirstSlopeBudget

/-! # The positive entrance correction retains both decaying combinations -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.positiveEntranceCorrectionConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  dom.surrogateHalfEntranceBound N M * dom.surrogateSpatialFirstBound N M *
    dom.surrogateSlopePolynomialConstant N M

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem positiveEntranceCorrectionConstant_pos (N : ℕ) (M : ℝ) :
    0 < dom.positiveEntranceCorrectionConstant N M := by
  have := surrogateHalfEntranceBound_pos dom hW hθ hD N M
  have := surrogateSlopePolynomialConstant_pos dom hW hθ hD N M
  have := CepsCanonDomain.v_pos hW hθ hD
  unfold CepsCanonDomain.positiveEntranceCorrectionConstant CepsCanonDomain.surrogateSpatialFirstBound
  positivity

include hW hθ hD in
theorem cepsScaledSurrogateEntranceCorrection_positive_weighted_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) (hlam : 1 ≤ lam) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.pairPolynomialScaleBase N M / (1 + |lam| + Real.sqrt ‖z‖))) :
    ‖cepsScaledSurrogateEntranceCorrection dom ρW N lam z b‖ ≤
      dom.positiveEntranceCorrectionConstant N M * (1 + |lam| + Real.sqrt ‖z‖) *
        (Real.exp (((cepsScaledSignedRoot D θ ρW lam z (-1) b -
          cepsScaledSignedRoot D θ ρW lam z 1 b) * (1 + b * lam)).re) +
            Real.exp (((cepsScaledSignedRoot D θ ρW lam z (-1) b - b * z) * (1 + b * lam)).re)) := by
  let p := (cepsScaledSignedRoot D θ ρW lam z 1 b * (1 + b * lam)).re
  let m := (cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + b * lam)).re
  let t := ((b * z) * (1 + b * lam)).re
  have hbE := ball_subset_ball (pairPolynomialScaleRadius_le dom hW hθ hD N M lam z).2 hb
  have hhalf := cepsScaledSurrogateHalfEntrance_positive_budget dom hW hθ hD hf hη hM N hN lam hlam hz hb
  have hfirst := cepsScaledSurrogateG_first_dslope_weighted_budget dom hW hθ hD hf hη hM N hN lam hz hbE
  have hS := cepsScaledSurrogateDenominator_inverse_weighted_bound dom hW hθ hD hf hη hM N hN lam hz
    (ball_subset_ball (min_le_left _ _) hbE)
  rw [cepsScaledSurrogateEntranceCorrection_eq_firstSlope dom hW hθ hD hf hη hM N hN lam hz hbE
    (cepsScaledPositiveMarkerGap_ne_zero dom hW hθ hD N M lam hlam hz hb),
      div_eq_mul_inv, norm_mul, norm_mul, norm_neg]
  apply (mul_le_mul (mul_le_mul hhalf hfirst (norm_nonneg _) ((norm_nonneg _).trans hhalf)) hS
    (norm_nonneg _) (mul_nonneg ((norm_nonneg _).trans hhalf) ((norm_nonneg _).trans hfirst))).trans_eq
  have he : (Real.exp (-p) + Real.exp (-t)) * Real.exp m =
      Real.exp (m - p) + Real.exp (m - t) := by
    rw [add_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1 <;> congr 1 <;> ring
  unfold CepsCanonDomain.positiveEntranceCorrectionConstant
  simp only [sub_mul, sub_re]
  calc
    _ = (dom.surrogateHalfEntranceBound N M * dom.surrogateSpatialFirstBound N M *
        dom.surrogateSlopePolynomialConstant N M * (1 + |lam| + Real.sqrt ‖z‖)) *
          ((Real.exp (-p) + Real.exp (-t)) * Real.exp m) := by ring
    _ = _ := by rw [he]

end PGM
