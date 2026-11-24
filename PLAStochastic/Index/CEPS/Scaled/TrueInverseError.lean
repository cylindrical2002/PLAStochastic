import PLAStochastic.Index.CEPS.Scaled.TrueDenominatorStable

/-! # Arbitrary-order inverse errors on the fixed actual denominator disc -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrueDenominator_inverse_error_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDenominatorScaleRadius M lam z))
    (hbN : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    ‖(cepsScaledTrueDenominator dom ρW lam z b)⁻¹ -
      (cepsScaledSurrogateDenominator dom ρW N lam z b)⁻¹‖ ≤
        (2 * dom.trueDenominatorRelativeConstant N M * dom.surrogateSlopePolynomialConstant 0 M) *
          (1 + |lam| + Real.sqrt ‖z‖) *
            Real.exp ((cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + (b : ℂ) * lam)).re) *
              |b * lam| ^ (N + 1) := by
  have hA := cepsScaledTrueDenominator_ne_zero dom hW hθ hD hf hη hM (by omega) lam hz hb
  have hB := cepsScaledSurrogateDenominator_ne_zero dom hW hθ hD hf hη hM N (by omega) lam hz
    (ball_subset_ball (min_le_left _ _) hbN)
  have hE := cepsScaledTrueDenominator_relative_error_budget dom hW hθ hD hf hη hM N hN lam hz hbN
  have hAI := cepsScaledTrueDenominator_inverse_weighted_budget dom hW hθ hD hf hη hM (by omega) lam hz hb
  have hC := trueDenominatorRelativeConstant_nonneg dom hW hθ hD
    ((cepsSobolev_nonneg m η fW).trans hM) N
  exact (cepsNorm_inverse_error_le_mul hA hB hE).trans
    ((mul_le_mul_of_nonneg_left hAI (mul_nonneg hC (pow_nonneg (abs_nonneg _) _))).trans_eq (by ring))

end PGM
