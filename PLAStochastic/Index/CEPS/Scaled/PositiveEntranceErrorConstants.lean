import PLAStochastic.Index.CEPS.Scaled.EntranceImaginaryError

/-! # Common profiles for entrance half-line cancellation errors -/

noncomputable section
open Complex Set Metric MeasureTheory
namespace PGM

def CepsCanonDomain.positiveEntranceErrorConstants {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : Finset ℝ :=
  {dom.trueHalfEntranceConstant,
    dom.trueMarkPrefactorErrorConstant N M / dom.positiveMarkerGapLower,
    dom.trueSpatialBound M 1, dom.trueSpatialErrorConstant N M 1,
    2 * dom.surrogateSlopePolynomialConstant 0 M,
    dom.trueDenominatorRelativeConstant N M * (2 * dom.surrogateSlopePolynomialConstant 0 M),
    dom.trueEntranceCorrectionConstant M}

def CepsCanonDomain.positiveEntranceErrorConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  1 + ∑ c ∈ dom.positiveEntranceErrorConstants N M, |c|

variable {D θ v : ℝ} (dom : CepsCanonDomain D θ v)

theorem positiveEntranceErrorConstant_pos (N : ℕ) (M : ℝ) : 0 < dom.positiveEntranceErrorConstant N M := by
  have h := Finset.sum_nonneg (fun c (_ : c ∈ dom.positiveEntranceErrorConstants N M) => abs_nonneg c)
  unfold CepsCanonDomain.positiveEntranceErrorConstant
  linarith

theorem positiveEntranceErrorConstant_le (N : ℕ) (M : ℝ) {c : ℝ}
    (hc : c ∈ dom.positiveEntranceErrorConstants N M) : c ≤ dom.positiveEntranceErrorConstant N M := by
  have h := Finset.single_le_sum (fun c (_ : c ∈ dom.positiveEntranceErrorConstants N M) => abs_nonneg c) hc
  apply (le_abs_self c).trans (h.trans _)
  unfold CepsCanonDomain.positiveEntranceErrorConstant
  linarith

theorem cepsNorm_three_factor_error_entrance_profile {A B I a b i : ℂ} {K X Q T e : ℝ}
    (hB : ‖B‖ ≤ K * Q) (hI : ‖I‖ ≤ K * X * T)
    (ha : ‖a‖ ≤ 2 * K) (hb : ‖b‖ ≤ 2 * K * Q)
    (hAe : ‖A - a‖ ≤ K * e) (hBe : ‖B - b‖ ≤ K * Q * e)
    (hIe : ‖I - i‖ ≤ K * X * T * e) :
    ‖A * B * I - a * b * i‖ ≤ 7 * K ^ 3 * X * Q * T * e := by
  have h1 : ‖(A - a) * B * I‖ ≤ K ^ 3 * X * Q * T * e := by
    have ht := cepsNorm_three_product_mul_le (by norm_num : (0 : ℝ) ≤ 1)
      (by simpa only [mul_one] using hAe) hB hI
    simp only [mul_one] at ht
    exact ht.trans_eq (by ring)
  have h2 : ‖a * (B - b) * I‖ ≤ 2 * K ^ 3 * X * Q * T * e := by
    rw [mul_comm a (B - b)]
    have ht := cepsNorm_three_product_mul_le (by norm_num : (0 : ℝ) ≤ 1)
      (by simpa only [mul_one] using hBe) ha hI
    simp only [mul_one] at ht
    exact ht.trans_eq (by ring)
  have h3 : ‖a * b * (I - i)‖ ≤ 4 * K ^ 3 * X * Q * T * e := by
    rw [mul_comm (a * b) (I - i), ← mul_assoc]
    have ht := cepsNorm_three_product_mul_le (by norm_num : (0 : ℝ) ≤ 1)
      (by simpa only [mul_one] using hIe) ha hb
    simp only [mul_one] at ht
    exact ht.trans_eq (by ring)
  exact ((cepsNorm_three_factor_error_le A B I a b i).trans
    (add_le_add (add_le_add h1 h2) h3)).trans_eq (by ring)

end PGM
