import PLAStochastic.Index.CEPS.Scaled.WeightedProductError

/-! # Cancellation of the three entrance numerator endpoint weights -/

noncomputable section
open Complex
namespace PGM

theorem cepsNorm_weighted_entrance_product_le {P E I a p t w : ℂ} {C A K : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) (_hK : 0 ≤ K)
    (hP : ‖P‖ ≤ C)
    (hE : ‖E‖ ≤ A * (Real.exp (-(a * w).re) + Real.exp (-(p * w).re) + Real.exp (-(t * w).re)))
    (hI : ‖I‖ ≤ K * Real.exp ((a * w).re)) :
    ‖P * E * I‖ ≤ C * A * K *
      (1 + Real.exp (((a - p) * w).re) + Real.exp (((a - t) * w).re)) := by
  rw [norm_mul, norm_mul]
  apply (mul_le_mul (mul_le_mul hP hE (norm_nonneg _) hC) hI
    (norm_nonneg _) (by positivity)).trans_eq
  have he : (Real.exp (-(a * w).re) + Real.exp (-(p * w).re) + Real.exp (-(t * w).re)) *
      Real.exp ((a * w).re) = 1 + Real.exp (((a - p) * w).re) + Real.exp (((a - t) * w).re) := by
    rw [add_mul, add_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    simp only [neg_add_cancel, Real.exp_zero, sub_mul, sub_re]
    ring_nf
  calc
    _ = C * A * K * ((Real.exp (-(a * w).re) + Real.exp (-(p * w).re) + Real.exp (-(t * w).re)) *
        Real.exp ((a * w).re)) := by ring
    _ = _ := by rw [he]

end PGM
