import PLAStochastic.Index.CEPS.Scaled.WeightedErrorCancellation

/-! # Three-factor errors with cancelling endpoint exponentials -/

noncomputable section
open Complex
namespace PGM

theorem cepsNorm_three_factor_error_le (A B I a b i : ℂ) :
    ‖A * B * I - a * b * i‖ ≤
      ‖(A - a) * B * I‖ + ‖a * (B - b) * I‖ + ‖a * b * (I - i)‖ := by
  have he : A * B * I - a * b * i =
      (A - a) * B * I + a * (B - b) * I + a * b * (I - i) := by ring
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)

theorem cepsNorm_weighted_three_product_le {A B I p m w : ℂ} {P M K : ℝ}
    (hP : 0 ≤ P) (hM : 0 ≤ M) (_hK : 0 ≤ K)
    (hA : ‖A‖ ≤ P * Real.exp (-(p * w).re))
    (hB : ‖B‖ ≤ M * Real.exp (-(m * w).re))
    (hI : ‖I‖ ≤ K * Real.exp ((m * w).re)) :
    ‖A * B * I‖ ≤ P * M * K * Real.exp (-(p * w).re) := by
  rw [norm_mul, norm_mul]
  apply (mul_le_mul (mul_le_mul hA hB (norm_nonneg _) (by positivity)) hI
    (norm_nonneg _) (by positivity)).trans_eq
  have he : Real.exp (-(m * w).re) * Real.exp ((m * w).re) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  calc
    _ = P * M * K * Real.exp (-(p * w).re) *
        (Real.exp (-(m * w).re) * Real.exp ((m * w).re)) := by ring
    _ = _ := by rw [he, mul_one]

end PGM
