import PLAStochastic.Index.CEPS.Normal.SecondSlopeBound
import PLAStochastic.Index.CEPS.Scaled.SurrogateSpatialBudget

/-! # Convex divided-difference budgets retaining endpoint exponential weights -/

noncomputable section
open Complex Set Metric MeasureTheory
namespace PGM

private theorem exp_neg_min_three_le (x y z : ℝ) :
    Real.exp (-min x (min y z)) ≤ Real.exp (-x) + Real.exp (-y) + Real.exp (-z) := by
  by_cases hx : x ≤ min y z
  · rw [min_eq_left hx]
    linarith [Real.exp_pos (-y), Real.exp_pos (-z)]
  · rw [min_eq_right (le_of_not_ge hx)]
    by_cases hy : y ≤ z
    · rw [min_eq_left hy]
      linarith [Real.exp_pos (-x), Real.exp_pos (-z)]
    · rw [min_eq_right (le_of_not_ge hy)]
      linarith [Real.exp_pos (-x), Real.exp_pos (-y)]

theorem cepsNormal_norm_second_dslope_le_weighted {g : ℂ → ℂ} {R C : ℝ} {w : ℂ}
    (hR : 0 < R) (hC : 0 ≤ C) (hg : DifferentiableOn ℂ g (ball 0 R))
    (hderiv : ∀ ξ : ℂ, ‖ξ‖ ≤ R / 2 → ‖deriv (deriv g) ξ‖ ≤ C * Real.exp (-(ξ * w).re))
    {a b t : ℂ} (ha : ‖a‖ ≤ R / 2) (hb : ‖b‖ ≤ R / 2) (ht : ‖t‖ ≤ R / 2) :
    ‖dslope (dslope g a) b t‖ ≤ C *
      (Real.exp (-(a * w).re) + Real.exp (-(b * w).re) + Real.exp (-(t * w).re)) := by
  let A := min (a * w).re (min (b * w).re (t * w).re)
  let S : Set ℂ := closedBall 0 (R / 2) ∩ {ξ | A ≤ (ξ * w).re}
  have hlin : IsLinearMap ℝ (fun ξ : ℂ => (ξ * w).re) := by
    constructor
    · intro x y
      simp [add_mul]
    · intro k x
      simp only [Complex.real_smul]
      rw [mul_assoc]
      simp
  have hS : Convex ℝ S := (convex_closedBall (0 : ℂ) (R / 2)).inter (convex_halfSpace_ge hlin A)
  have hsub : S ⊆ ball (0 : ℂ) R := by
    intro ξ hξ
    exact mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hξ.1).trans_lt (half_lt_self hR))
  have hbound : ∀ ξ ∈ S, ‖deriv (deriv g) ξ‖ ≤ C * Real.exp (-A) := by
    intro ξ hξ
    exact (hderiv ξ (mem_closedBall_zero_iff.mp hξ.1)).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hξ.2)) hC)
  have haS : a ∈ S := ⟨mem_closedBall_zero_iff.mpr ha,
    show A ≤ (a * w).re from min_le_left (a * w).re (min (b * w).re (t * w).re)⟩
  have hbS : b ∈ S := ⟨mem_closedBall_zero_iff.mpr hb,
    show A ≤ (b * w).re from (min_le_right _ _).trans (min_le_left _ _)⟩
  have htS : t ∈ S := ⟨mem_closedBall_zero_iff.mpr ht,
    show A ≤ (t * w).re from (min_le_right _ _).trans (min_le_right _ _)⟩
  exact (cepsNormal_norm_second_dslope_le hg hS hsub (mul_nonneg hC (Real.exp_pos _).le)
    hbound haS hbS htS).trans (mul_le_mul_of_nonneg_left (exp_neg_min_three_le _ _ _) hC)

end PGM
