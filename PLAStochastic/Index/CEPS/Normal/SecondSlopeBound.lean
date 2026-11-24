import PLAStochastic.Index.CEPS.Normal.SlopeDerivative
import Mathlib.Analysis.Complex.RemovableSingularity

/-! # A convex-domain bound for second divided differences

The two segment integrals remain valid on all diagonals. A uniform second
derivative bound on a convex subset therefore bounds the second slope.
-/

noncomputable section
open Complex Set Metric MeasureTheory
namespace PGM

theorem cepsNormal_norm_second_dslope_le {g : ℂ → ℂ} {R M : ℝ}
    (hg : DifferentiableOn ℂ g (ball 0 R)) {S : Set ℂ}
    (hS : Convex ℝ S) (hsub : S ⊆ ball 0 R) (hM : 0 ≤ M)
    (hbound : ∀ z ∈ S, ‖deriv (deriv g) z‖ ≤ M)
    {a b t : ℂ} (ha : a ∈ S) (hb : b ∈ S) (ht : t ∈ S) :
    ‖dslope (dslope g a) b t‖ ≤ M := by
  have hsegment : ∀ {x y : ℂ}, x ∈ S → y ∈ S →
      ∀ s ∈ Icc (0 : ℝ) 1, x + (s : ℂ) * (y - x) ∈ S := by
    intro x y hx hy s hs
    simpa [AffineMap.lineMap_apply, Complex.real_smul, add_comm] using hS.lineMap_mem hx hy hs
  have hfirst : ∀ z ∈ S, ‖deriv (dslope g a) z‖ ≤ M := by
    intro z hz
    rw [cepsNormal_deriv_dslope_eq_integral hg (hsub ha) (hsub hz)]
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (C := M)
      (f := fun s : ℝ => (s : ℂ) * deriv (deriv g) (a + (s : ℂ) * (z - a)))
      (by
        intro s hs
        rw [uIoc_of_le (by norm_num)] at hs
        have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2⟩
        rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hs'.1]
        exact (mul_le_mul_of_nonneg_left (hbound _ (hsegment ha hz s hs')) hs'.1).trans
          (mul_le_of_le_one_left hM hs'.2))
    simpa only [sub_zero, abs_one, mul_one] using hi
  have hd : DifferentiableOn ℂ (dslope g a) (ball 0 R) :=
    (differentiableOn_dslope (isOpen_ball.mem_nhds (hsub ha))).mpr hg
  rw [cepsNormal_dslope_eq_integral hd (hsub hb) (hsub ht)]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := M)
    (f := fun s : ℝ => deriv (dslope g a) (b + (s : ℂ) * (t - b)))
    (by
      intro s hs
      rw [uIoc_of_le (by norm_num)] at hs
      exact hfirst _ (hsegment hb ht s ⟨hs.1.le, hs.2⟩))
  simpa only [sub_zero, abs_one, mul_one] using hi

end PGM
