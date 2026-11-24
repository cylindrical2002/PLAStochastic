import PLAStochastic.ForMathlib.Analysis.Complex.EvenSqrt

/-! # A square-root Holder bound along horizontal lines -/

noncomputable section
open Complex
namespace PGM

theorem norm_sqrt_sub_sqrt_le_of_im_eq {z w : ℂ} (him : z.im = w.im) :
    ‖Complex.sqrt z - Complex.sqrt w‖ ≤ Real.sqrt ‖z - w‖ := by
  let a := Complex.sqrt z
  let b := Complex.sqrt w
  have har : 0 ≤ a.re := by
    dsimp only [a]
    rw [Complex.sqrt, cpow_inv_two_re]
    exact Real.sqrt_nonneg _
  have hbr : 0 ≤ b.re := by
    dsimp only [b]
    rw [Complex.sqrt, cpow_inv_two_re]
    exact Real.sqrt_nonneg _
  have himprod : 0 ≤ a.im * b.im := by
    by_cases hz : 0 ≤ z.im
    · have hw : 0 ≤ w.im := by rwa [him] at hz
      have ha : 0 ≤ a.im := by
        dsimp only [a]
        rw [Complex.sqrt, cpow_inv_two_im_eq_sqrt hz]
        exact Real.sqrt_nonneg _
      have hb : 0 ≤ b.im := by
        dsimp only [b]
        rw [Complex.sqrt, cpow_inv_two_im_eq_sqrt hw]
        exact Real.sqrt_nonneg _
      exact mul_nonneg ha hb
    · have hz' : z.im < 0 := lt_of_not_ge hz
      have hw : w.im < 0 := by rwa [him] at hz'
      have ha : a.im ≤ 0 := by
        dsimp only [a]
        rw [Complex.sqrt, cpow_inv_two_im_eq_neg_sqrt hz']
        exact neg_nonpos.mpr (Real.sqrt_nonneg _)
      have hb : b.im ≤ 0 := by
        dsimp only [b]
        rw [Complex.sqrt, cpow_inv_two_im_eq_neg_sqrt hw]
        exact neg_nonpos.mpr (Real.sqrt_nonneg _)
      exact mul_nonneg_of_nonpos_of_nonpos ha hb
  have hsum := Complex.sq_norm_sub_sq_re (a + b)
  have hdiff := Complex.sq_norm_sub_sq_re (a - b)
  simp only [add_re, add_im, sub_re, sub_im] at hsum hdiff
  have hnorm : ‖a - b‖ ≤ ‖a + b‖ := by
    nlinarith [mul_nonneg har hbr, norm_nonneg (a - b), norm_nonneg (a + b)]
  have he : (a - b) * (a + b) = z - w := by
    have ha : a ^ 2 = z := sqrt_sq_eq z
    have hb : b ^ 2 = w := sqrt_sq_eq w
    linear_combination ha - hb
  have hmul := congrArg norm he
  rw [norm_mul] at hmul
  have hs := Real.sq_sqrt (norm_nonneg (z - w))
  nlinarith [norm_nonneg (a - b), Real.sqrt_nonneg ‖z - w‖,
    mul_nonneg (sub_nonneg.mpr hnorm) (norm_nonneg (a - b))]

end PGM
