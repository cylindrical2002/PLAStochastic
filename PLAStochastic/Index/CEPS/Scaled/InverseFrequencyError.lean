import PLAStochastic.Index.CEPS.Scaled.DenominatorFrequencyBudget
import PLAStochastic.ForMathlib.Analysis.Complex.InverseDerivativeError

/-! # Frequency errors of the actual inverse divided denominator -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.inverseFrequencyErrorConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  dom.denominatorFrequencyErrorConstant N M * (2 * dom.surrogateSlopePolynomialConstant 0 M) ^ 2 +
    (dom.trueDenominatorFrequencyConstant M + dom.denominatorFrequencyErrorConstant N M) *
      (dom.trueDenominatorRelativeConstant N M * (2 * dom.surrogateSlopePolynomialConstant 0 M)) *
        (2 * dom.surrogateSlopePolynomialConstant 0 M + dom.surrogateSlopePolynomialConstant N M)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrueDenominator_inverse_frequency_deriv_error_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z))
    (hbN : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    ‖deriv (fun ζ => (cepsScaledTrueDenominator dom ρW lam ζ b)⁻¹ -
      (cepsScaledSurrogateDenominator dom ρW N lam ζ b)⁻¹) z‖ * |lam| ^ 2 ≤
        dom.inverseFrequencyErrorConstant N M * (1 + |lam|) * (1 + |lam| + Real.sqrt ‖z‖) ^ 2 *
          Real.exp ((cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + (b : ℂ) * lam)).re) *
            |b * lam| ^ (N + 1) := by
  by_cases hl : lam = 0
  · subst lam
    simp
  let S : ℂ → ℂ := fun ζ => cepsScaledTrueDenominator dom ρW lam ζ b
  let T : ℂ → ℂ := fun ζ => cepsScaledSurrogateDenominator dom ρW N lam ζ b
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let e := |b * lam| ^ (N + 1)
  let t := (cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + (b : ℂ) * lam)).re
  let A := dom.trueDenominatorFrequencyConstant M
  let B := dom.denominatorFrequencyErrorConstant N M
  let KA := 2 * dom.surrogateSlopePolynomialConstant 0 M
  let KB := dom.surrogateSlopePolynomialConstant N M
  let C := dom.trueDenominatorRelativeConstant N M
  have hbD := ball_subset_ball (truePairScaleRadius_le dom M lam z)
    (ball_subset_ball (trueFrequencyScaleRadius_le dom M lam z) hbs)
  obtain ⟨hS, hT⟩ := cepsScaledDenominators_frequency_differentiableAt dom hW hθ hD hf hη N
    (by omega) M lam hl hz hb hbs
  change DifferentiableAt ℂ S z at hS
  change DifferentiableAt ℂ T z at hT
  have hS0 := cepsScaledTrueDenominator_ne_zero dom hW hθ hD hf hη hM (by omega) lam hz hbD
  have hT0 := cepsScaledSurrogateDenominator_ne_zero dom hW hθ hD hf hη hM N (by omega) lam hz
    (ball_subset_ball (min_le_left _ _) hbN)
  have hDSabs := cepsScaledTrueDenominator_frequency_deriv_budget dom hW hθ hD hf hη hM (by omega) lam hl hz hb hbs
  have hDE := cepsScaledTrueDenominator_frequency_deriv_error_budget dom hW hθ hD hf hη hM N hN lam hz hb hbs hbN
  have hepos : 0 < e := pow_pos (abs_pos.mpr (mul_ne_zero hb.ne' hl)) _
  have hEcoeff : 0 ≤ B * (1 + |lam|) * Real.exp (-t) :=
    nonneg_of_mul_nonneg_left ((mul_nonneg (norm_nonneg _) (sq_nonneg |lam|)).trans hDE) hepos
  have he1 : e ≤ 1 := pow_le_one₀ (abs_nonneg _) (cepsScaledTrueScale_drift_le_one dom hW hθ hD M lam hz hbD)
  have hDE1 : ‖deriv (fun ζ => S ζ - T ζ) z‖ * |lam| ^ 2 ≤ B * (1 + |lam|) * Real.exp (-t) :=
    hDE.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left he1 hEcoeff)
  have hDT : ‖deriv T z‖ * |lam| ^ 2 ≤ (A + B) * (1 + |lam|) * Real.exp (-t) := by
    have heq : deriv T z = deriv S z - deriv (fun ζ => S ζ - T ζ) z := by
      have hder : deriv (fun ζ => S ζ - T ζ) z = deriv S z - deriv T z := by
        simpa only [Pi.sub_def] using deriv_sub hS hT
      rw [hder]
      ring
    calc
      _ ≤ (‖deriv S z‖ + ‖deriv (fun ζ => S ζ - T ζ) z‖) * |lam| ^ 2 := by
        conv_lhs => rw [heq]
        exact mul_le_mul_of_nonneg_right (norm_sub_le _ _) (sq_nonneg _)
      _ = ‖deriv S z‖ * |lam| ^ 2 + ‖deriv (fun ζ => S ζ - T ζ) z‖ * |lam| ^ 2 := by ring
      _ ≤ A * (1 + |lam|) * Real.exp (-t) + B * (1 + |lam|) * Real.exp (-t) := add_le_add hDSabs hDE1
      _ = _ := by ring
  have hI : ‖(S z)⁻¹‖ ≤ KA * X * Real.exp t :=
    cepsScaledTrueDenominator_inverse_weighted_budget dom hW hθ hD hf hη hM (by omega) lam hz hbD
  have hJ : ‖(T z)⁻¹‖ ≤ KB * X * Real.exp t :=
    cepsScaledSurrogateDenominator_inverse_weighted_bound dom hW hθ hD hf hη hM N (by omega) lam hz
      (ball_subset_ball (min_le_left _ _) hbN)
  have hIJ : ‖(S z)⁻¹ - (T z)⁻¹‖ ≤ C * KA * X * Real.exp t * e := by
    apply (cepsScaledTrueDenominator_inverse_error_budget dom hW hθ hD hf hη hM N hN lam hz hbD hbN).trans_eq
    dsimp only [C, KA, X, t, e]
    ring
  have h := norm_deriv_inverse_difference_mul_sq_le hS hT hS0 hT0 hDE hDT hI hJ hIJ
  have hecancel : Real.exp (-t) * Real.exp t ^ 2 = Real.exp t := by
    rw [pow_two, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  apply h.trans_eq
  calc
    _ = (B * KA ^ 2 + (A + B) * (C * KA) * (KA + KB)) *
        (1 + |lam|) * X ^ 2 * (Real.exp (-t) * Real.exp t ^ 2) * e := by ring
    _ = _ := by
      rw [hecancel]
      unfold CepsCanonDomain.inverseFrequencyErrorConstant
      dsimp only [A, B, C, KA, KB, X, t, e]

end PGM
