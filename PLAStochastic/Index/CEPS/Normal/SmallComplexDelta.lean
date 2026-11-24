import PLAStochastic.Index.CEPS.Normal.DenominatorBound

/-! # The normal denominator near a merged root without a sector hypothesis -/

noncomputable section
open Complex
namespace PGM

theorem cepsNormal_delta_lower_bound_small {η P : ℂ} {l C : ℝ}
    (hl : 0 ≤ l) (hsmall : ‖η‖ * l ≤ 1 / 4)
    (hfactor : ‖P - 1‖ ≤ C * ‖η‖) (hwidth : 6 * C ≤ l) :
    ‖η‖ * l / 2 ≤ ‖1 - exp (-η * (l : ℂ)) * P‖ := by
  let z : ℂ := -η * (l : ℂ)
  have hn : ‖z‖ = ‖η‖ * l := by simp [z, abs_of_nonneg hl]
  have hz : ‖z‖ ≤ 1 := by rw [hn]; linarith
  have ht := norm_exp_sub_one_sub_id_le hz
  have hlow : ‖z‖ - ‖z‖ ^ 2 ≤ ‖1 - exp z‖ := by
    have he : z = (exp z - 1) - (exp z - 1 - z) := by ring
    have hh := norm_sub_le (exp z - 1) (exp z - 1 - z)
    rw [← he, norm_sub_rev (exp z)] at hh
    linarith
  have he : ‖exp z‖ ≤ 3 / 2 := by
    have hh := norm_add_le (exp z - 1) (1 : ℂ)
    rw [sub_add_cancel, norm_one] at hh
    have hb := norm_exp_sub_one_le hz
    rw [hn] at hb
    linarith
  have hid : 1 - exp z = (1 - exp z * P) + exp z * (P - 1) := by ring
  have hh := norm_add_le (1 - exp z * P) (exp z * (P - 1))
  rw [← hid, norm_mul] at hh
  have hC : 0 ≤ C * ‖η‖ := (norm_nonneg (P - 1)).trans hfactor
  have herr : ‖exp z‖ * ‖P - 1‖ ≤ (3 / 2) * (C * ‖η‖) :=
    mul_le_mul he hfactor (norm_nonneg _) (by norm_num)
  have hwidth' : 6 * C * ‖η‖ ≤ ‖η‖ * l := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hwidth) (norm_nonneg η)]
  have hsquare : (‖η‖ * l) ^ 2 ≤ (‖η‖ * l) / 4 := by
    nlinarith [mul_nonneg (norm_nonneg η) hl,
      mul_nonneg (sub_nonneg.mpr hsmall) (mul_nonneg (norm_nonneg η) hl)]
  rw [hn] at hlow
  change ‖η‖ * l / 2 ≤ ‖1 - exp z * P‖
  linarith

end PGM
