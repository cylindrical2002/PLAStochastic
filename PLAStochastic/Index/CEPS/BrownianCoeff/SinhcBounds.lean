import PLAStochastic.Index.CEPS.BrownianCoeff.Entire
import PLAStochastic.ForMathlib.Analysis.Complex.Hadamard
import PLAStochastic.ForMathlib.Analysis.Complex.CauchyBound
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Bounds for the entire Brownian hyperbolic functions

The bounds use the real part of a square root. A nearby squared argument admits
one of the two square roots within distance one, which pays for Cauchy estimates.
-/

noncomputable section

open Complex Set Metric

namespace PGM

theorem cepsBrownian_cosh_norm (s : ℂ) : ‖Complex.cosh s‖ ≤ Real.exp |s.re| := by
  have hp := Real.exp_le_exp.mpr (le_abs_self s.re)
  have hn := Real.exp_le_exp.mpr (neg_le_abs s.re)
  rw [Complex.cosh, norm_div, Complex.norm_ofNat]
  have ht := norm_add_le (Complex.exp s) (Complex.exp (-s))
  rw [Complex.norm_exp, Complex.norm_exp, neg_re] at ht
  nlinarith

theorem cepsBrownian_sinhc_norm (s : ℂ) : ‖cepsBrownianSinhc (s ^ 2)‖ ≤ Real.exp |s.re| := by
  rw [cepsBrownianSinhc_sq]
  by_cases hs : s = 0
  · simp [hs, Complex.deriv_sinh]
  · have hderiv (t : ℝ) : HasDerivAt (fun t : ℝ => Complex.sinh ((t : ℂ) * s))
        (Complex.cosh ((t : ℂ) * s) * s) t := by
      simpa using hasDerivAt_comp_affine (b := 0) (u := s)
        (Complex.hasDerivAt_sinh (0 + (t : ℂ) * s))
    have hbound : ‖Complex.sinh s‖ ≤ Real.exp |s.re| * ‖s‖ := by
      have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
        (fun t _ => (hderiv t).hasDerivWithinAt) (C := Real.exp |s.re| * ‖s‖) ?_
      · simpa using h
      · intro t ht
        rw [norm_mul]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg s)
        refine (cepsBrownian_cosh_norm _).trans (Real.exp_le_exp.mpr ?_)
        simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, abs_mul,
          abs_of_nonneg ht.1]
        exact mul_le_of_le_one_left (abs_nonneg _) ht.2.le
    rw [dslope_of_ne _ hs, slope_def_field]
    simp only [Complex.sinh_zero, sub_zero, norm_div]
    exact (div_le_iff₀ (norm_pos_iff.mpr hs)).mpr hbound

private theorem sqrt_near_sign (s w : ℂ) (hw : ‖w - s ^ 2‖ ≤ 1) :
    ‖Complex.sqrt w - s‖ ≤ 1 ∨ ‖Complex.sqrt w + s‖ ≤ 1 := by
  have heq : (Complex.sqrt w - s) * (Complex.sqrt w + s) = w - s ^ 2 := by
    calc
      (Complex.sqrt w - s) * (Complex.sqrt w + s) = Complex.sqrt w ^ 2 - s ^ 2 := by ring
      _ = _ := by rw [sqrt_sq_eq]
  have hp := congrArg norm heq
  rw [norm_mul] at hp
  by_contra h
  push Not at h
  nlinarith

theorem cepsBrownianSinhc_near_norm (s w : ℂ) (hw : ‖w - s ^ 2‖ ≤ 1) :
    ‖cepsBrownianSinhc w‖ ≤ Real.exp (|s.re| + 1) := by
  have hbase : ‖cepsBrownianSinhc w‖ ≤ Real.exp |(Complex.sqrt w).re| := by
    simpa only [sqrt_sq_eq] using cepsBrownian_sinhc_norm (Complex.sqrt w)
  apply hbase.trans
  apply Real.exp_le_exp.mpr
  rcases sqrt_near_sign s w hw with h | h
  · have hr := (Complex.abs_re_le_norm (Complex.sqrt w - s)).trans h
    rw [sub_re] at hr
    have ht := abs_add_le ((Complex.sqrt w).re - s.re) s.re
    rw [sub_add_cancel] at ht
    linarith
  · have hr := (Complex.abs_re_le_norm (Complex.sqrt w + s)).trans h
    rw [add_re] at hr
    have ht := abs_sub ((Complex.sqrt w).re + s.re) s.re
    rw [add_sub_cancel_right] at ht
    linarith

theorem cepsBrownianSinhc_deriv_norm (s : ℂ) :
    ‖deriv cepsBrownianSinhc (s ^ 2)‖ ≤ 2 * Real.exp (|s.re| + 1) := by
  have h := norm_iteratedDeriv_le_of_ball (f := cepsBrownianSinhc) (c := s ^ 2)
    (r := 1) (M := Real.exp (|s.re| + 1)) 1 (by norm_num)
    cepsBrownianSinhc_differentiable.differentiableOn ?_
  · simpa [iteratedDeriv_one, mul_comm] using h
  · intro w hw
    exact cepsBrownianSinhc_near_norm s w (mem_ball_iff_norm.mp hw).le

theorem cepsBrownianSinhc_sub_one (s : ℂ) (hs : ‖s‖ ≤ 1 / 8) :
    ‖cepsBrownianSinhc (s ^ 2) - 1‖ ≤ 1 / 2 := by
  have hderiv : ∀ w ∈ ball (0 : ℂ) 1, ‖deriv cepsBrownianSinhc w‖ ≤ 18 := by
    intro w hw
    have h := cepsBrownianSinhc_deriv_norm (Complex.sqrt w)
    rw [sqrt_sq_eq] at h
    have hroot : ‖Complex.sqrt w‖ ≤ 1 := by
      have hsq : ‖Complex.sqrt w‖ ^ 2 = ‖w‖ := by rw [← norm_pow, sqrt_sq_eq]
      have hw' := mem_ball_iff_norm.mp hw
      simp only [sub_zero] at hw'
      nlinarith [norm_nonneg (Complex.sqrt w)]
    have hre := (Complex.abs_re_le_norm (Complex.sqrt w)).trans hroot
    have hexp : Real.exp (|(Complex.sqrt w).re| + 1) ≤ 9 := by
      calc
        Real.exp (|(Complex.sqrt w).re| + 1) ≤ Real.exp (1 + 1) :=
          Real.exp_le_exp.mpr (by linarith)
        _ = Real.exp 1 * Real.exp 1 := Real.exp_add 1 1
        _ ≤ 9 := by nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
    linarith
  have hw : s ^ 2 ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_iff_norm, sub_zero, norm_pow]
    nlinarith [norm_nonneg s]
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self zero_lt_one
  have h := (convex_ball (0 : ℂ) 1).norm_image_sub_le_of_norm_deriv_le
    (fun w _ => cepsBrownianSinhc_differentiable w) hderiv h0 hw
  rw [cepsBrownianSinhc_zero, sub_zero, norm_pow] at h
  nlinarith [norm_nonneg s]

end PGM
