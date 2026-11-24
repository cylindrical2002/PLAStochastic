import PLAStochastic.Index.CEPS.Scaled.OuterDenominatorFrequency

/-! # The lower-root weight is preserved by the inverse frequency derivative -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.outerInverseFrequencyConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  dom.outerDenominatorFrequencyConstant N M * (dom.surrogateSlopePolynomialConstant N M) ^ 2

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem outerInverseFrequencyConstant_pos (N : ℕ) (M : ℝ) :
    0 < dom.outerInverseFrequencyConstant N M := by
  have := (outerDenominator_constants dom hW hθ hD N M).2
  have := surrogateSlopePolynomialConstant_pos dom hW hθ hD N M
  unfold CepsCanonDomain.outerInverseFrequencyConstant
  positivity

include hW hθ hD in
theorem cepsScaledSurrogateDenominator_outer_inverse_frequency_profile {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    (houter : dom.centralFrequencyDriftRadius N M < |lam| ∨ dom.centralFrequencyRadius N M ≤ ‖z‖)
    {b : ℂ} (hb : b ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    DifferentiableAt ℂ (fun ζ => (cepsScaledSurrogateDenominator dom ρW N lam ζ b)⁻¹) z ∧
      ‖deriv (fun ζ => (cepsScaledSurrogateDenominator dom ρW N lam ζ b)⁻¹) z‖ ≤
        dom.outerInverseFrequencyConstant N M * (1 + |lam| + Real.sqrt ‖z‖) ^ 2 *
          Real.exp ((cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + b * lam)).re) := by
  let S : ℂ → ℂ := fun ζ => cepsScaledSurrogateDenominator dom ρW N lam ζ b
  let a := (cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + b * lam)).re
  let X := 1 + |lam| + Real.sqrt ‖z‖
  have hbReg := ball_subset_ball (min_le_left _ _) hb
  obtain ⟨hS, _, hDs⟩ := cepsScaledSurrogateDenominator_outer_frequency_profile dom hW hθ hD hf hη hM N hN lam hz houter hb
  have hS0 := cepsScaledSurrogateDenominator_ne_zero dom hW hθ hD hf hη hM N hN lam hz hbReg
  have hI := cepsScaledSurrogateDenominator_inverse_weighted_bound dom hW hθ hD hf hη hM N hN lam hz hbReg
  have hd : HasDerivAt (fun ζ => (cepsScaledSurrogateDenominator dom ρW N lam ζ b)⁻¹)
      (-deriv S z / (S z) ^ 2) z := hS.hasDerivAt.inv hS0
  refine ⟨hd.differentiableAt, ?_⟩
  rw [hd.deriv, div_eq_mul_inv, ← inv_pow, norm_mul, norm_neg, norm_pow]
  have hSq := pow_le_pow_left₀ (norm_nonneg _) hI 2
  apply (mul_le_mul hDs hSq (sq_nonneg _) ((norm_nonneg _).trans hDs)).trans_eq
  have he : Real.exp (-a) * (Real.exp a) ^ 2 = Real.exp a := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  change dom.outerDenominatorFrequencyConstant N M * Real.exp (-a) *
      (dom.surrogateSlopePolynomialConstant N M * X * Real.exp a) ^ 2 = _
  calc
    _ = dom.outerInverseFrequencyConstant N M * X ^ 2 * (Real.exp (-a) * (Real.exp a) ^ 2) := by
      unfold CepsCanonDomain.outerInverseFrequencyConstant
      ring
    _ = _ := by rw [he]

end PGM
