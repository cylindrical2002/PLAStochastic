import PLAStochastic.Index.CEPS.Scaled.WeightedErrorCancellation

/-! # Quantitative inversion from a relative error below one half -/

noncomputable section
open Complex
namespace PGM

theorem cepsNorm_half_le_of_relative_error {A B : ℂ} (hB : B ≠ 0)
    (herror : ‖(A - B) / B‖ ≤ 1 / 2) : ‖B‖ / 2 ≤ ‖A‖ := by
  rw [norm_div] at herror
  have h := (div_le_iff₀ (norm_pos_iff.mpr hB)).mp herror
  have ht := norm_sub_norm_le B A
  rw [norm_sub_rev] at ht
  linarith

theorem ceps_ne_zero_of_relative_error {A B : ℂ} (hB : B ≠ 0)
    (herror : ‖(A - B) / B‖ ≤ 1 / 2) : A ≠ 0 :=
  norm_pos_iff.mp ((half_pos (norm_pos_iff.mpr hB)).trans_le
    (cepsNorm_half_le_of_relative_error hB herror))

theorem cepsNorm_inverse_le_of_relative_error {A B : ℂ} (hB : B ≠ 0)
    (herror : ‖(A - B) / B‖ ≤ 1 / 2) : ‖A⁻¹‖ ≤ 2 * ‖B⁻¹‖ := by
  have hA := ceps_ne_zero_of_relative_error hB herror
  rw [norm_inv, norm_inv]
  apply ((inv_le_inv₀ (norm_pos_iff.mpr hA) (half_pos (norm_pos_iff.mpr hB))).mpr
    (cepsNorm_half_le_of_relative_error hB herror)).trans_eq
  ring

theorem cepsNorm_inverse_error_le {A B : ℂ} {C : ℝ} (hB : B ≠ 0)
    (hsmall : ‖(A - B) / B‖ ≤ 1 / 2) (herror : ‖(A - B) / B‖ ≤ C) :
    ‖A⁻¹ - B⁻¹‖ ≤ 2 * C * ‖B⁻¹‖ := by
  have hA := ceps_ne_zero_of_relative_error hB hsmall
  have hC : 0 ≤ C := (norm_nonneg _).trans herror
  have hid : A⁻¹ - B⁻¹ = -((A - B) / B) * A⁻¹ := by field_simp; ring
  rw [hid, norm_mul, norm_neg]
  exact (mul_le_mul herror (cepsNorm_inverse_le_of_relative_error hB hsmall)
    (norm_nonneg _) hC).trans_eq (by ring)

theorem cepsNorm_inverse_error_le_mul {A B : ℂ} {C : ℝ} (hA : A ≠ 0) (hB : B ≠ 0)
    (herror : ‖(A - B) / B‖ ≤ C) : ‖A⁻¹ - B⁻¹‖ ≤ C * ‖A⁻¹‖ := by
  have hid : A⁻¹ - B⁻¹ = -((A - B) / B) * A⁻¹ := by field_simp; ring
  rw [hid, norm_mul, norm_neg]
  exact mul_le_mul_of_nonneg_right herror (norm_nonneg _)

end PGM
