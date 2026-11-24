import PLAStochastic.Index.CEPS.Scaled.ProductDerivativeError

/-! # Common exponential envelopes for three-factor derivative errors -/

noncomputable section
open Complex
namespace PGM

theorem cepsNorm_three_product_mul_le {a b c : ℂ} {L A B C : ℝ} (hL : 0 ≤ L)
    (ha : ‖a‖ * L ≤ A) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ C) :
    ‖a * b * c‖ * L ≤ A * B * C := by
  have hA : 0 ≤ A := (mul_nonneg (norm_nonneg _) hL).trans ha
  have hB : 0 ≤ B := (norm_nonneg _).trans hb
  rw [norm_mul, norm_mul]
  calc
    _ = (‖a‖ * L) * ‖b‖ * ‖c‖ := by ring
    _ ≤ _ := mul_le_mul (mul_le_mul ha hb (norm_nonneg _) hA) hc
      (norm_nonneg _) (mul_nonneg hA hB)

theorem cepsNorm_deriv_three_factor_error_common_budget {A B I a b i : ℂ → ℂ} {z : ℂ}
    (hA : DifferentiableAt ℂ A z) (hB : DifferentiableAt ℂ B z)
    (hI : DifferentiableAt ℂ I z) (ha : DifferentiableAt ℂ a z)
    (hb : DifferentiableAt ℂ b z) (hi : DifferentiableAt ℂ i z)
    {L K X P Q T e : ℝ}
    (hBv : ‖B z‖ ≤ K * Q) (hIv : ‖I z‖ ≤ K * X * T)
    (hav : ‖a z‖ ≤ K * P) (hbv : ‖b z‖ ≤ K * Q)
    (hAe : ‖A z - a z‖ ≤ K * P * e) (hBe : ‖B z - b z‖ ≤ K * Q * e)
    (hIe : ‖I z - i z‖ ≤ K * X * T * e)
    (hBd : ‖deriv B z‖ * L ^ 2 ≤ K * X ^ 2 * Q)
    (hId : ‖deriv I z‖ * L ^ 2 ≤ K * X ^ 3 * T)
    (had : ‖deriv a z‖ * L ^ 2 ≤ K * X ^ 2 * P)
    (hbd : ‖deriv b z‖ * L ^ 2 ≤ K * X ^ 2 * Q)
    (hAde : ‖deriv A z - deriv a z‖ * L ^ 2 ≤ K * X ^ 2 * P * e)
    (hBde : ‖deriv B z - deriv b z‖ * L ^ 2 ≤ K * X ^ 2 * Q * e)
    (hIde : ‖deriv I z - deriv i z‖ * L ^ 2 ≤ K * X ^ 3 * T * e) :
    ‖deriv (fun u => A u * B u * I u - a u * b u * i u) z‖ * L ^ 2 ≤
      9 * K ^ 3 * X ^ 3 * P * Q * T * e := by
  let Y := K ^ 3 * X ^ 3 * P * Q * T * e
  have h1 : ‖(deriv A z - deriv a z) * B z * I z‖ * L ^ 2 ≤ Y :=
    (cepsNorm_three_product_mul_le (sq_nonneg L) hAde hBv hIv).trans_eq (by dsimp [Y]; ring)
  have h2 : ‖deriv a z * (B z - b z) * I z‖ * L ^ 2 ≤ Y :=
    (cepsNorm_three_product_mul_le (sq_nonneg L) had hBe hIv).trans_eq (by dsimp [Y]; ring)
  have h3 : ‖deriv a z * b z * (I z - i z)‖ * L ^ 2 ≤ Y :=
    (cepsNorm_three_product_mul_le (sq_nonneg L) had hbv hIe).trans_eq (by dsimp [Y]; ring)
  have h4 : ‖(A z - a z) * deriv B z * I z‖ * L ^ 2 ≤ Y := by
    rw [mul_comm (A z - a z) (deriv B z)]
    exact (cepsNorm_three_product_mul_le (sq_nonneg L) hBd hAe hIv).trans_eq (by dsimp [Y]; ring)
  have h5 : ‖a z * (deriv B z - deriv b z) * I z‖ * L ^ 2 ≤ Y := by
    rw [mul_comm (a z) (deriv B z - deriv b z)]
    exact (cepsNorm_three_product_mul_le (sq_nonneg L) hBde hav hIv).trans_eq (by dsimp [Y]; ring)
  have h6 : ‖a z * deriv b z * (I z - i z)‖ * L ^ 2 ≤ Y := by
    rw [mul_comm (a z) (deriv b z)]
    exact (cepsNorm_three_product_mul_le (sq_nonneg L) hbd hav hIe).trans_eq (by dsimp [Y]; ring)
  have h7 : ‖(A z - a z) * B z * deriv I z‖ * L ^ 2 ≤ Y := by
    rw [show (A z - a z) * B z * deriv I z = deriv I z * (A z - a z) * B z by ring]
    exact (cepsNorm_three_product_mul_le (sq_nonneg L) hId hAe hBv).trans_eq (by dsimp [Y]; ring)
  have h8 : ‖a z * (B z - b z) * deriv I z‖ * L ^ 2 ≤ Y := by
    rw [show a z * (B z - b z) * deriv I z = deriv I z * a z * (B z - b z) by ring]
    exact (cepsNorm_three_product_mul_le (sq_nonneg L) hId hav hBe).trans_eq (by dsimp [Y]; ring)
  have h9 : ‖a z * b z * (deriv I z - deriv i z)‖ * L ^ 2 ≤ Y := by
    rw [show a z * b z * (deriv I z - deriv i z) = (deriv I z - deriv i z) * a z * b z by ring]
    exact (cepsNorm_three_product_mul_le (sq_nonneg L) hIde hav hbv).trans_eq (by dsimp [Y]; ring)
  have h := mul_le_mul_of_nonneg_right (cepsNorm_deriv_three_factor_error_le hA hB hI ha hb hi) (sq_nonneg L)
  simp only [add_mul] at h
  exact h.trans ((add_le_add (add_le_add (add_le_add (add_le_add h1 h2) h3)
    (add_le_add (add_le_add h4 h5) h6)) (add_le_add (add_le_add h7 h8) h9)).trans_eq (by dsimp [Y]; ring))

end PGM
