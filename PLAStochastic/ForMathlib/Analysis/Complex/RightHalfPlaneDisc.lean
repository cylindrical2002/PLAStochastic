import Mathlib.Analysis.Complex.Basic

/-! # A relative disc about a nonzero right-half-plane point avoids the negative cut -/

noncomputable section
open Complex
namespace PGM

theorem mem_slitPlane_of_norm_sub_lt {a z : ℂ} (ha : 0 ≤ a.re) (hz : ‖z - a‖ < ‖a‖) :
    z ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_cases hi : z.im ≠ 0
  · exact Or.inr hi
  · left
    have hi' : z.im = 0 := not_ne_iff.mp hi
    by_contra hr
    have hr' : z.re ≤ 0 := not_lt.mp hr
    have hn : ‖z - a‖ ^ 2 < ‖a‖ ^ 2 := pow_lt_pow_left₀ hz (norm_nonneg _) (by norm_num)
    rw [Complex.sq_norm, Complex.sq_norm] at hn
    simp only [normSq_apply, sub_re, sub_im, hi', zero_sub] at hn
    nlinarith [sq_nonneg z.re, mul_nonpos_of_nonpos_of_nonneg hr' ha]

theorem norm_nonneg_real_add_ge {a : ℝ} (ha : 0 ≤ a) {z : ℂ} (hz : 0 ≤ z.re) :
    a ≤ ‖(a : ℂ) + z‖ ∧ ‖z‖ ≤ 2 * ‖(a : ℂ) + z‖ := by
  have h1 : a ≤ ‖(a : ℂ) + z‖ := by
    have hr := re_le_norm ((a : ℂ) + z)
    rw [add_re, ofReal_re] at hr
    linarith
  refine ⟨h1, ?_⟩
  have h2 : ‖z‖ ≤ ‖(a : ℂ) + z‖ + a := by
    have hn := norm_sub_le ((a : ℂ) + z) (a : ℂ)
    simpa only [add_sub_cancel_left, norm_real, Real.norm_eq_abs, abs_of_nonneg ha] using hn
  linarith

end PGM
