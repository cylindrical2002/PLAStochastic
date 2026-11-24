import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! # Actual derivative errors of two nonzero inverses -/

noncomputable section
open Complex
namespace PGM

theorem norm_deriv_inverse_difference_mul_sq_le {S T : ℂ → ℂ} {z : ℂ}
    (hS : DifferentiableAt ℂ S z) (hT : DifferentiableAt ℂ T z)
    (hS0 : S z ≠ 0) (hT0 : T z ≠ 0) {L DS DT I J E : ℝ}
    (hDS : ‖deriv (fun u => S u - T u) z‖ * L ^ 2 ≤ DS)
    (hDT : ‖deriv T z‖ * L ^ 2 ≤ DT)
    (hI : ‖(S z)⁻¹‖ ≤ I) (hJ : ‖(T z)⁻¹‖ ≤ J)
    (hE : ‖(S z)⁻¹ - (T z)⁻¹‖ ≤ E) :
    ‖deriv (fun u => (S u)⁻¹ - (T u)⁻¹) z‖ * L ^ 2 ≤ DS * I ^ 2 + DT * E * (I + J) := by
  have hI0 : 0 ≤ I := (norm_nonneg _).trans hI
  have hJ0 : 0 ≤ J := (norm_nonneg _).trans hJ
  have hE0 : 0 ≤ E := (norm_nonneg _).trans hE
  have hDS0 : 0 ≤ DS := (mul_nonneg (norm_nonneg _) (sq_nonneg L)).trans hDS
  have hDT0 : 0 ≤ DT := (mul_nonneg (norm_nonneg _) (sq_nonneg L)).trans hDT
  have hSI : HasDerivAt (fun u => (S u)⁻¹) (-deriv S z / (S z) ^ 2) z := hS.hasDerivAt.inv hS0
  have hTI : HasDerivAt (fun u => (T u)⁻¹) (-deriv T z / (T z) ^ 2) z := hT.hasDerivAt.inv hT0
  have hd : HasDerivAt (fun u => (S u)⁻¹ - (T u)⁻¹)
      (-deriv S z / (S z) ^ 2 - -deriv T z / (T z) ^ 2) z := hSI.sub hTI
  rw [hd.deriv]
  have he : -deriv S z / (S z) ^ 2 - -deriv T z / (T z) ^ 2 =
      -(deriv S z - deriv T z) * ((S z)⁻¹) ^ 2 -
        deriv T z * ((S z)⁻¹ - (T z)⁻¹) * ((S z)⁻¹ + (T z)⁻¹) := by
    simp only [div_eq_mul_inv, ← inv_pow]
    ring
  rw [he]
  apply (mul_le_mul_of_nonneg_right (norm_sub_le _ _) (sq_nonneg L)).trans
  simp only [norm_mul, norm_neg, norm_pow]
  rw [← deriv_sub hS hT]
  calc
    _ = (‖deriv (S - T) z‖ * L ^ 2) * ‖(S z)⁻¹‖ ^ 2 +
        (‖deriv T z‖ * L ^ 2) * ‖(S z)⁻¹ - (T z)⁻¹‖ * ‖(S z)⁻¹ + (T z)⁻¹‖ := by ring
    _ ≤ DS * I ^ 2 + DT * E * (I + J) := by
      have hsum := (norm_add_le (S z)⁻¹ (T z)⁻¹).trans (add_le_add hI hJ)
      gcongr
      exact hDS

end PGM
