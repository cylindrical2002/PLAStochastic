import PLAStochastic.Affine.Moments.Optimal.Survival.Image.Modes
import PLAStochastic.ForMathlib.Analysis.SpecialFunctions.GaussianPowerSeries
import PLAStochastic.ForMathlib.Analysis.SpecialFunctions.FlatGlueJets
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Smooth optimal image modes through time zero

The inverse exponential integral has a smooth zero extension. Its first
derivative is a polynomial-in-the-reciprocal multiple of the standard flat glue.
-/

namespace BrownianAffine

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ContDiff Polynomial

set_option backward.isDefEq.respectTransparency false

theorem hasDerivAt_inverseExponentialIntegral {c : ℝ} (hc : 0 < c) (x : ℝ) :
    HasDerivAt (inverseExponentialIntegral c) (x⁻¹ * expNegInvGlue (x / c)) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have he : inverseExponentialIntegral c =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact inverseExponentialIntegral_of_nonpos c hy.le
    rw [expNegInvGlue.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hx.le hc.le), mul_zero]
    exact (hasDerivAt_const x 0).congr_of_eventuallyEq he
  · have hnonneg (y : ℝ) : 0 ≤ y⁻¹ * inverseExponentialIntegral c y := by
      by_cases hy : 0 < y
      · exact mul_nonneg (inv_pos.mpr hy).le (inverseExponentialIntegral_nonneg c y)
      · rw [inverseExponentialIntegral_of_nonpos c (le_of_not_gt hy), mul_zero]
    have hbound (y : ℝ) : y⁻¹ * inverseExponentialIntegral c y ≤ expNegInvGlue (y / c) / c := by
      by_cases hy : 0 < y
      · have hb := mul_le_mul_of_nonneg_left (inverseExponentialIntegral_le hc hy) (inv_pos.mpr hy).le
        rw [expNegInvGlue_div hc hy]
        have heq : y⁻¹ * ((y / c) * Real.exp (-c / y)) = Real.exp (-c / y) / c := by
          field_simp
        rw [heq] at hb
        exact hb
      · rw [inverseExponentialIntegral_of_nonpos c (le_of_not_gt hy), mul_zero,
          expNegInvGlue.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hy) hc.le), zero_div]
    have hlim : Tendsto (fun y : ℝ => y⁻¹ * inverseExponentialIntegral c y) (𝓝 0) (𝓝 0) := by
      apply squeeze_zero hnonneg hbound
      have hg := (((expNegInvGlue.contDiff (n := ⊤)).continuous.comp (continuous_id.div_const c)).div_const c).tendsto (0 : ℝ)
      simpa only [Function.comp_apply, id_eq, zero_div, expNegInvGlue.zero] using hg
    rw [inv_zero, zero_mul, hasDerivAt_iff_tendsto_slope]
    have heq : slope (inverseExponentialIntegral c) 0 = fun y => y⁻¹ * inverseExponentialIntegral c y := by
      funext y
      rw [slope_def_field, inverseExponentialIntegral_of_nonpos c le_rfl]
      simp only [sub_zero, div_eq_mul_inv, mul_comm]
    rw [heq]
    exact hlim.mono_left inf_le_left
  · have hd := (hasDerivAt_exponentialIntegralE1 (div_pos hc hx)).comp x
      ((hasDerivAt_const x c).div (hasDerivAt_id x) hx.ne')
    have he : inverseExponentialIntegral c =ᶠ[𝓝 x] fun y => exponentialIntegralE1 (c / y) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      change 0 < y at hy
      simp only [inverseExponentialIntegral, if_pos hy]
    convert! hd.congr_of_eventuallyEq he using 1
    rw [expNegInvGlue_div hc hx]
    field_simp
    ring

/-- Smoothness includes the matching of every derivative at time zero. -/
theorem contDiff_inverseExponentialIntegral {c : ℝ} (hc : 0 < c) :
    ContDiff ℝ ∞ (inverseExponentialIntegral c) := by
  have hp := expNegInvGlue.contDiff_polynomial_eval_inv_mul (n := ⊤) (Polynomial.X : ℝ[X])
  have hcomp : ContDiff ℝ ∞ (fun x : ℝ => (x / c)⁻¹ * expNegInvGlue (x / c)) := by
    convert! hp.comp (contDiff_id.div_const c) using 1
    simp only [Polynomial.eval_X, Function.comp_def, id_eq]
  have hg : ContDiff ℝ ∞ (fun x : ℝ => c⁻¹ * ((x / c)⁻¹ * expNegInvGlue (x / c))) := by
    exact contDiff_const.mul hcomp
  have hg' : ContDiff ℝ ∞ (fun x : ℝ => x⁻¹ * expNegInvGlue (x / c)) := by
    convert hg using 1
    funext x
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun x => (hasDerivAt_inverseExponentialIntegral hc x).differentiableAt, ?_⟩
  have he : deriv (inverseExponentialIntegral c) = fun x => x⁻¹ * expNegInvGlue (x / c) := by
    funext x
    exact (hasDerivAt_inverseExponentialIntegral hc x).deriv
  rw [he]
  exact hg'

theorem contDiff_optimalImageMode (n : ℕ) : ContDiff ℝ ∞ (optimalImageMode n) := by
  have h₁ := contDiff_inverseExponentialIntegral (by positivity : 0 < 8 * ((n : ℝ) + 1) ^ 2)
  have h₂ := contDiff_inverseExponentialIntegral
    (by positivity : 0 < 8 * ((n : ℝ) + 1) * ((n : ℝ) + 1 + 1))
  unfold optimalImageMode optimalImageCoefficientA optimalImageCoefficientB
  fun_prop

/-- Every jet of an individual mode vanishes at the zero-extension boundary. -/
theorem iteratedDeriv_optimalImageMode_of_nonpos (n r : ℕ) {t : ℝ} (ht : t ≤ 0) :
    iteratedDeriv r (optimalImageMode n) t = 0 := by
  have he : EqOn (optimalImageMode n) (fun _ => 0) (Iio (0 : ℝ)) :=
    fun x hx => optimalImageMode_of_nonpos n hx.le
  have hd : EqOn (iteratedDeriv r (optimalImageMode n)) (fun _ => 0) (Iio (0 : ℝ)) := by
    intro x hx
    exact (he.iteratedDeriv_of_isOpen isOpen_Iio r hx).trans iteratedDeriv_fun_const_zero
  have hc := hd.closure ((contDiff_optimalImageMode n).continuous_iteratedDeriv r (by
    exact_mod_cast (le_top : (r : ℕ∞) ≤ ⊤)))
    continuous_const
  exact hc (by simpa only [closure_Iio, mem_Iic] using ht)

end

end BrownianAffine
