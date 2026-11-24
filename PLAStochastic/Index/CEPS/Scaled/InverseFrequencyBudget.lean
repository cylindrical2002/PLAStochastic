import PLAStochastic.Index.CEPS.Scaled.InverseFrequencyError

/-! # Actual inverse-denominator frequency budget with cancelling root weight -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.trueInverseFrequencyConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (M : ℝ) : ℝ :=
  dom.trueDenominatorFrequencyConstant M * (2 * dom.surrogateSlopePolynomialConstant 0 M) ^ 2

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrueDenominator_inverse_frequency_deriv_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m) (lam : ℝ) (hlam : lam ≠ 0)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z)) :
    ‖deriv (fun ζ => (cepsScaledTrueDenominator dom ρW lam ζ b)⁻¹) z‖ * |lam| ^ 2 ≤
      dom.trueInverseFrequencyConstant M * (1 + |lam|) * (1 + |lam| + Real.sqrt ‖z‖) ^ 2 *
        Real.exp ((cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + (b : ℂ) * lam)).re) := by
  let S : ℂ → ℂ := fun ζ => cepsScaledTrueDenominator dom ρW lam ζ b
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let t := (cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + (b : ℂ) * lam)).re
  let K := 2 * dom.surrogateSlopePolynomialConstant 0 M
  have hbD := ball_subset_ball (truePairScaleRadius_le dom M lam z)
    (ball_subset_ball (trueFrequencyScaleRadius_le dom M lam z) hbs)
  have hS := (cepsScaledDenominators_frequency_differentiableAt dom hW hθ hD hf hη 0
    (by omega) M lam hlam hz hb hbs).1
  have hS0 := cepsScaledTrueDenominator_ne_zero dom hW hθ hD hf hη hM hm lam hz hbD
  have hd := cepsScaledTrueDenominator_frequency_deriv_budget dom hW hθ hD hf hη hM hm lam hlam hz hb hbs
  have hI := cepsScaledTrueDenominator_inverse_weighted_budget dom hW hθ hD hf hη hM hm lam hz hbD
  have hSI : HasDerivAt (fun ζ => (S ζ)⁻¹) (-deriv S z / (S z) ^ 2) z := hS.hasDerivAt.inv hS0
  rw [hSI.deriv]
  simp only [div_eq_mul_inv, ← inv_pow, norm_mul, norm_neg, norm_pow]
  have hD0 : 0 ≤ dom.trueDenominatorFrequencyConstant M * (1 + |lam|) * Real.exp (-t) :=
    (mul_nonneg (norm_nonneg _) (sq_nonneg |lam|)).trans hd
  have hK0 : 0 ≤ K * X * Real.exp t := (norm_nonneg _).trans hI
  have hecancel : Real.exp (-t) * Real.exp t ^ 2 = Real.exp t := by
    rw [pow_two, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  calc
    _ = (‖deriv S z‖ * |lam| ^ 2) * ‖(S z)⁻¹‖ ^ 2 := by rw [norm_inv]; ring
    _ ≤ (dom.trueDenominatorFrequencyConstant M * (1 + |lam|) * Real.exp (-t)) *
        (K * X * Real.exp t) ^ 2 := by gcongr
    _ = dom.trueDenominatorFrequencyConstant M * K ^ 2 * (1 + |lam|) * X ^ 2 *
        (Real.exp (-t) * Real.exp t ^ 2) := by ring
    _ = _ := by rw [hecancel]; unfold CepsCanonDomain.trueInverseFrequencyConstant; dsimp only [K, X, t]

end PGM
