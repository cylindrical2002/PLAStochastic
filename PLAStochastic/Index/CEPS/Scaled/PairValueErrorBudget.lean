import PLAStochastic.Index.CEPS.Scaled.ProductDerivativeBudget

/-! # Taylor error propagation through an entrance square and a time operator -/

noncomputable section
open Complex
namespace PGM

theorem cepsNorm_square_product_taylor_error_le {H h O o : ℂ} {K X B C beta E : ℝ} (N : ℕ)
    (hH : ‖H‖ ≤ K * X) (hh : ‖h‖ ≤ K * X)
    (hE : ‖H - h‖ ≤ K * beta * X ^ (N + 3)) (hO : ‖O‖ ≤ C * X * E)
    (hOE : ‖O - o‖ ≤ B * beta * X ^ (N + 3) * E) :
    ‖H ^ 2 * O - h ^ 2 * o‖ ≤ K ^ 2 * (2 * C + B) * beta * X ^ (N + 5) * E := by
  have hx : X ^ (N + 5) = X ^ (N + 3) * X ^ 2 := by rw [← pow_add]
  have h1 : ‖(H - h) * H * O‖ ≤ K ^ 2 * C * beta * X ^ (N + 5) * E := by
    have ht := cepsNorm_three_product_mul_le (by norm_num : (0 : ℝ) ≤ 1)
      (by simpa only [mul_one] using hE) hH hO
    simp only [mul_one] at ht
    exact ht.trans_eq (by rw [hx]; ring)
  have h2 : ‖h * (H - h) * O‖ ≤ K ^ 2 * C * beta * X ^ (N + 5) * E := by
    rw [mul_comm h (H - h)]
    have ht := cepsNorm_three_product_mul_le (by norm_num : (0 : ℝ) ≤ 1)
      (by simpa only [mul_one] using hE) hh hO
    simp only [mul_one] at ht
    exact ht.trans_eq (by rw [hx]; ring)
  have h3 : ‖h * h * (O - o)‖ ≤ K ^ 2 * B * beta * X ^ (N + 5) * E := by
    rw [mul_comm (h * h) (O - o), ← mul_assoc]
    have ht := cepsNorm_three_product_mul_le (by norm_num : (0 : ℝ) ≤ 1)
      (by simpa only [mul_one] using hOE) hh hh
    simp only [mul_one] at ht
    exact ht.trans_eq (by rw [hx]; ring)
  rw [pow_two, pow_two]
  exact ((cepsNorm_three_factor_error_le H H O h h o).trans
    (add_le_add (add_le_add h1 h2) h3)).trans_eq (by ring)

end PGM
