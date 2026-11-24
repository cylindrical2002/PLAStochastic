import PLAStochastic.Index.CEPS.Scaled.HalfTimeOperatorError
import PLAStochastic.Index.CEPS.Scaled.PairValueErrorBudget

/-! # One class constant for positive-tail pair error propagation -/

noncomputable section
open Complex Set Metric MeasureTheory
namespace PGM

def CepsCanonDomain.positivePairErrorConstants {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : Finset ℝ :=
  {dom.entranceComparisonConstant N M,
    dom.entranceComparisonConstant N M + 2 * dom.positiveEntranceErrorConstant N M,
    2 * dom.positiveEntranceErrorConstant N M,
    2 * dom.positiveEntranceErrorConstant N M + 14 * dom.positiveEntranceErrorConstant N M ^ 3,
    14 * dom.positiveEntranceErrorConstant N M ^ 3,
    dom.truePositiveOperatorConstant M,
    42 * dom.kernelFrequencyConstant N M ^ 3,
    dom.trueHalfOperatorConstant,
    dom.bridgeTimeErrorConstant N M + 21 * dom.kernelFrequencyConstant N M ^ 3}

def CepsCanonDomain.positivePairComparisonConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  1 + ∑ c ∈ dom.positivePairErrorConstants N M, |c|

variable {D θ v : ℝ} (dom : CepsCanonDomain D θ v)

theorem positivePairComparisonConstant_pos (N : ℕ) (M : ℝ) : 0 < dom.positivePairComparisonConstant N M := by
  have h := Finset.sum_nonneg (fun c (_ : c ∈ dom.positivePairErrorConstants N M) => abs_nonneg c)
  unfold CepsCanonDomain.positivePairComparisonConstant
  linarith

theorem positivePairComparisonConstant_le (N : ℕ) (M : ℝ) {c : ℝ}
    (hc : c ∈ dom.positivePairErrorConstants N M) : c ≤ dom.positivePairComparisonConstant N M := by
  have h := Finset.single_le_sum (fun c (_ : c ∈ dom.positivePairErrorConstants N M) => abs_nonneg c) hc
  apply (le_abs_self c).trans (h.trans _)
  unfold CepsCanonDomain.positivePairComparisonConstant
  linarith

theorem cepsNorm_three_factor_taylor_error_le {A B I a b i : ℂ} {K X beta E : ℝ} (N : ℕ)
    (hB : ‖B‖ ≤ K * X) (hI : ‖I‖ ≤ K * X) (ha : ‖a‖ ≤ K * X * E) (hb : ‖b‖ ≤ K * X)
    (hAe : ‖A - a‖ ≤ K * beta * X ^ (N + 3) * E)
    (hBe : ‖B - b‖ ≤ K * beta * X ^ (N + 3))
    (hIe : ‖I - i‖ ≤ K * beta * X ^ (N + 3)) :
    ‖A * B * I - a * b * i‖ ≤ 3 * K ^ 3 * beta * X ^ (N + 5) * E := by
  have hx : X ^ (N + 5) = X ^ (N + 3) * X ^ 2 := by rw [← pow_add]
  have h1 : ‖(A - a) * B * I‖ ≤ K ^ 3 * beta * X ^ (N + 5) * E := by
    have ht := cepsNorm_three_product_mul_le (by norm_num : (0 : ℝ) ≤ 1)
      (by simpa only [mul_one] using hAe) hB hI
    simp only [mul_one] at ht
    exact ht.trans_eq (by rw [hx]; ring)
  have h2 : ‖a * (B - b) * I‖ ≤ K ^ 3 * beta * X ^ (N + 5) * E := by
    rw [mul_comm a (B - b)]
    have ht := cepsNorm_three_product_mul_le (by norm_num : (0 : ℝ) ≤ 1)
      (by simpa only [mul_one] using hBe) ha hI
    simp only [mul_one] at ht
    exact ht.trans_eq (by rw [hx]; ring)
  have h3 : ‖a * b * (I - i)‖ ≤ K ^ 3 * beta * X ^ (N + 5) * E := by
    rw [mul_comm (a * b) (I - i), ← mul_assoc]
    have ht := cepsNorm_three_product_mul_le (by norm_num : (0 : ℝ) ≤ 1)
      (by simpa only [mul_one] using hIe) ha hb
    simp only [mul_one] at ht
    exact ht.trans_eq (by rw [hx]; ring)
  exact ((cepsNorm_three_factor_error_le A B I a b i).trans
    (add_le_add (add_le_add h1 h2) h3)).trans_eq (by ring)

end PGM
