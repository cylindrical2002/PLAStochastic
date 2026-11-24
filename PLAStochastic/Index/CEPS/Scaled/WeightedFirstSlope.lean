import PLAStochastic.Index.CEPS.Normal.MovingSlope
import Mathlib.Analysis.Convex.Function

/-! # First divided differences retain both endpoint exponential weights -/

noncomputable section
open Complex Set Metric MeasureTheory
namespace PGM

theorem cepsNormal_norm_dslope_le_weighted {g : ℂ → ℂ} {R C : ℝ} {w : ℂ}
    (hR : 0 < R) (hC : 0 ≤ C) (hg : DifferentiableOn ℂ g (ball 0 R))
    (hderiv : ∀ ξ : ℂ, ‖ξ‖ ≤ R / 2 → ‖deriv g ξ‖ ≤ C * Real.exp (-(ξ * w).re))
    {a t : ℂ} (ha : ‖a‖ ≤ R / 2) (ht : ‖t‖ ≤ R / 2) :
    ‖dslope g a t‖ ≤ C * (Real.exp (-(a * w).re) + Real.exp (-(t * w).re)) := by
  let A := min (a * w).re (t * w).re
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
  have haS : a ∈ S := ⟨mem_closedBall_zero_iff.mpr ha,
    show A ≤ (a * w).re from min_le_left _ _⟩
  have htS : t ∈ S := ⟨mem_closedBall_zero_iff.mpr ht,
    show A ≤ (t * w).re from min_le_right _ _⟩
  have hsub : S ⊆ ball (0 : ℂ) R := fun ξ hξ => mem_ball_zero_iff.mpr
    ((mem_closedBall_zero_iff.mp hξ.1).trans_lt (half_lt_self hR))
  have hbound : ∀ ξ ∈ S, ‖deriv g ξ‖ ≤ C * Real.exp (-A) := fun ξ hξ =>
    (hderiv ξ (mem_closedBall_zero_iff.mp hξ.1)).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hξ.2)) hC)
  rw [cepsNormal_dslope_eq_integral hg (hsub haS) (hsub htS)]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := C * Real.exp (-A))
    (f := fun s : ℝ => deriv g (a + (s : ℂ) * (t - a))) (by
      intro s hs
      rw [uIoc_of_le (by norm_num)] at hs
      apply hbound
      simpa [AffineMap.lineMap_apply, Complex.real_smul, add_comm] using
        hS.lineMap_mem haS htS (show s ∈ Icc (0 : ℝ) 1 from ⟨hs.1.le, hs.2⟩))
  simp only [sub_zero, abs_one, mul_one] at hi
  apply hi.trans (mul_le_mul_of_nonneg_left ?_ hC)
  by_cases he : (a * w).re ≤ (t * w).re
  · dsimp only [A]
    rw [min_eq_left he]
    linarith [Real.exp_pos (-(t * w).re)]
  · dsimp only [A]
    rw [min_eq_right (le_of_not_ge he)]
    linarith [Real.exp_pos (-(a * w).re)]

end PGM
