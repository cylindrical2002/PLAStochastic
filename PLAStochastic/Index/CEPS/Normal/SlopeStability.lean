import PLAStochastic.Index.CEPS.Normal.SecondSlopeBound
import PLAStochastic.Index.CEPS.Normal.DividedDifferenceSymmetry
import PLAStochastic.ForMathlib.Analysis.Complex.CauchyBound

/-! # Quantitative divided-denominator stability near merged roots -/

noncomputable section
open Complex Set Metric
namespace PGM

theorem cepsNormal_norm_dslope_sub_deriv_zero_le {g : ℂ → ℂ} {R M : ℝ}
    (hR : 0 < R) (hg : DifferentiableOn ℂ g (ball 0 R))
    (hbound : ∀ z ∈ ball (0 : ℂ) R, ‖g z‖ ≤ M) {a p : ℂ}
    (ha : a ∈ ball (0 : ℂ) (R / 2)) (hp : p ∈ ball (0 : ℂ) (R / 2)) :
    ‖dslope g a p - deriv g 0‖ ≤ (32 * M / R ^ 2) * (‖a‖ + ‖p‖) := by
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) (R / 2) := mem_ball_self (half_pos hR)
  have hM : 0 ≤ M := (norm_nonneg (g 0)).trans (hbound 0 (mem_ball_self hR))
  have hK : 0 ≤ 32 * M / R ^ 2 := by positivity
  have hsub : ball (0 : ℂ) (R / 2) ⊆ ball 0 R := ball_subset_ball (half_le_self hR.le)
  have h2 : ∀ z ∈ ball (0 : ℂ) (R / 2), ‖deriv (deriv g) z‖ ≤ 32 * M / R ^ 2 := by
    intro z hz
    have hh := norm_iteratedDeriv_le_of_ball_half 2 hR hg hbound hz
    rw [iteratedDeriv_succ, iteratedDeriv_one] at hh
    exact hh.trans_eq (by simp only [Nat.factorial, Nat.cast_mul, mul_one]; field_simp; ring)
  have hfirst := cepsNormal_norm_second_dslope_le hg (convex_ball (0 : ℂ) (R / 2)) hsub hK h2 hp h0 ha
  have hsecond := cepsNormal_norm_second_dslope_le hg (convex_ball (0 : ℂ) (R / 2)) hsub hK h2 h0 h0 hp
  have he1 := sub_smul_dslope (dslope g p) 0 a
  rw [smul_eq_mul, sub_zero, cepsNormal_dslope_swap g p a, cepsNormal_dslope_swap g p 0] at he1
  have he2 := sub_smul_dslope (dslope g 0) 0 p
  rw [smul_eq_mul, sub_zero, dslope_same] at he2
  have hn1 : ‖dslope g a p - dslope g 0 p‖ ≤ ‖a‖ * (32 * M / R ^ 2) := by
    rw [← he1, norm_mul]
    exact mul_le_mul_of_nonneg_left hfirst (norm_nonneg _)
  have hn2 : ‖dslope g 0 p - deriv g 0‖ ≤ ‖p‖ * (32 * M / R ^ 2) := by
    rw [← he2, norm_mul]
    exact mul_le_mul_of_nonneg_left hsecond (norm_nonneg _)
  calc
    _ = ‖(dslope g a p - dslope g 0 p) + (dslope g 0 p - deriv g 0)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _
    _ ≤ ‖a‖ * (32 * M / R ^ 2) + ‖p‖ * (32 * M / R ^ 2) := add_le_add hn1 hn2
    _ = _ := by ring

theorem cepsNormal_dslope_norm_lower_of_near_origin {g : ℂ → ℂ} {R M L : ℝ}
    (hR : 0 < R) (hg : DifferentiableOn ℂ g (ball 0 R))
    (hbound : ∀ z ∈ ball (0 : ℂ) R, ‖g z‖ ≤ M) {a p : ℂ}
    (ha : a ∈ ball (0 : ℂ) (R / 2)) (hp : p ∈ ball (0 : ℂ) (R / 2))
    (hL : L ≤ ‖deriv g 0‖) (hsmall : (32 * M / R ^ 2) * (‖a‖ + ‖p‖) ≤ L / 2) :
    L / 2 ≤ ‖dslope g a p‖ := by
  have h := cepsNormal_norm_dslope_sub_deriv_zero_le hR hg hbound ha hp
  have ht := norm_sub_norm_le (deriv g 0) (dslope g a p)
  rw [norm_sub_rev] at ht
  linarith

end PGM
