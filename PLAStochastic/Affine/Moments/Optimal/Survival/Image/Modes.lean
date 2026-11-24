import PLAStochastic.ForMathlib.Analysis.SpecialFunctions.ExponentialIntegral
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! # The explicit optimal image modes and their continuous zero extension

These definitions use the manuscript's index `m = n + 1`. The identification
with the Brownian survival function is a separate theorem.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- The continuous zero extension of `E₁(c/t)` when `c > 0`. -/
def inverseExponentialIntegral (c t : ℝ) : ℝ :=
  if 0 < t then exponentialIntegralE1 (c / t) else 0

theorem inverseExponentialIntegral_nonneg (c t : ℝ) :
    0 ≤ inverseExponentialIntegral c t := by
  unfold inverseExponentialIntegral
  split_ifs <;> simp [exponentialIntegralE1_nonneg]

theorem inverseExponentialIntegral_of_nonpos (c : ℝ) {t : ℝ} (ht : t ≤ 0) :
    inverseExponentialIntegral c t = 0 := by
  simp [inverseExponentialIntegral, not_lt.mpr ht]

theorem inverseExponentialIntegral_le {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    inverseExponentialIntegral c t ≤ (t / c) * Real.exp (-c / t) := by
  rw [inverseExponentialIntegral, if_pos ht]
  convert! exponentialIntegralE1_le (div_pos hc ht) using 1
  rw [neg_div, div_div_eq_mul_div]
  ring

theorem inverseExponentialIntegral_le_abs {c : ℝ} (hc : 0 < c) (t : ℝ) :
    inverseExponentialIntegral c t ≤ |t| / c := by
  by_cases ht : 0 < t
  · calc
      _ ≤ (t / c) * Real.exp (-c / t) := inverseExponentialIntegral_le hc ht
      _ ≤ (t / c) * 1 := mul_le_mul_of_nonneg_left
        (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) ht.le)) (by positivity)
      _ = |t| / c := by rw [abs_of_pos ht, mul_one]
  · rw [inverseExponentialIntegral_of_nonpos _ (le_of_not_gt ht)]
    positivity

theorem continuous_inverseExponentialIntegral {c : ℝ} (hc : 0 < c) :
    Continuous (inverseExponentialIntegral c) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have he : inverseExponentialIntegral c =ᶠ[𝓝 t] (fun _ => 0) := by
      filter_upwards [Iio_mem_nhds ht] with u hu
      exact inverseExponentialIntegral_of_nonpos c hu.le
    exact continuousAt_const.congr_of_eventuallyEq he
  · rw [ContinuousAt, inverseExponentialIntegral_of_nonpos c le_rfl]
    apply squeeze_zero (inverseExponentialIntegral_nonneg c)
      (inverseExponentialIntegral_le_abs hc)
    simpa using ((continuous_abs.continuousAt (x := (0 : ℝ))).div_const c).tendsto
  · have he : inverseExponentialIntegral c =ᶠ[𝓝 t]
        (fun u => exponentialIntegralE1 (c / u)) := by
      filter_upwards [Ioi_mem_nhds ht] with u hu
      simp [inverseExponentialIntegral, show 0 < u from hu]
    have hh := (hasDerivAt_exponentialIntegralE1 (div_pos hc ht)).continuousAt.comp
      ((continuousAt_const (y := c)).div continuousAt_id ht.ne')
    exact hh.congr_of_eventuallyEq he

def optimalImageCoefficientA (n : ℕ) (t : ℝ) : ℝ :=
  let m := (n : ℝ) + 1;
  -8 * (2 * m ^ 2 + 1) / 3 + t / 6 * (1 - 1 / m ^ 2)

def optimalImageCoefficientB (n : ℕ) (t : ℝ) : ℝ :=
  let m := (n : ℝ) + 1;
  (2 * m + 1) ^ 4 / (3 * m * (m + 1)) +
    t / 12 * (-2 + 1 / m ^ 2 + 1 / (m + 1) ^ 2)

def optimalImageMode (n : ℕ) (t : ℝ) : ℝ :=
  let m := (n : ℝ) + 1;
  optimalImageCoefficientA n t * expNegInvGlue (t / (8 * m ^ 2)) +
    optimalImageCoefficientB n t * expNegInvGlue (t / (8 * m * (m + 1))) +
    4 * m ^ 2 * inverseExponentialIntegral (8 * m ^ 2) t -
    4 * m * (m + 1) * inverseExponentialIntegral (8 * m * (m + 1)) t

def optimalImageSeries (t : ℝ) : ℝ := 1 + ∑' n, optimalImageMode n t

theorem optimalImageMode_of_pos (n : ℕ) {t : ℝ} (ht : 0 < t) :
    optimalImageMode n t =
      let m := (n : ℝ) + 1;
      optimalImageCoefficientA n t * Real.exp (-8 * m ^ 2 / t) +
        optimalImageCoefficientB n t * Real.exp (-8 * m * (m + 1) / t) +
        4 * m ^ 2 * exponentialIntegralE1 (8 * m ^ 2 / t) -
        4 * m * (m + 1) * exponentialIntegralE1 (8 * m * (m + 1) / t) := by
  have hm : 0 < (n : ℝ) + 1 := by positivity
  simp only [optimalImageMode, inverseExponentialIntegral, if_pos ht,
    expNegInvGlue_div (by positivity : 0 < 8 * ((n : ℝ) + 1) ^ 2) ht,
    expNegInvGlue_div (by positivity : 0 < 8 * ((n : ℝ) + 1) * ((n : ℝ) + 1 + 1)) ht]
  ring_nf

theorem optimalImageMode_of_nonpos (n : ℕ) {t : ℝ} (ht : t ≤ 0) :
    optimalImageMode n t = 0 := by
  have hm : 0 < (n : ℝ) + 1 := by positivity
  simp only [optimalImageMode, inverseExponentialIntegral_of_nonpos _ ht,
    expNegInvGlue.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg ht
      (by positivity : 0 ≤ 8 * ((n : ℝ) + 1) ^ 2)),
    expNegInvGlue.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg ht
      (by positivity : 0 ≤ 8 * ((n : ℝ) + 1) * ((n : ℝ) + 1 + 1))),
    mul_zero, add_zero, sub_zero]

theorem continuous_optimalImageMode (n : ℕ) : Continuous (optimalImageMode n) := by
  have hm : 0 < (n : ℝ) + 1 := by positivity
  have h₁ := continuous_inverseExponentialIntegral
    (by positivity : 0 < 8 * ((n : ℝ) + 1) ^ 2)
  have h₂ := continuous_inverseExponentialIntegral
    (by positivity : 0 < 8 * ((n : ℝ) + 1) * ((n : ℝ) + 1 + 1))
  unfold optimalImageMode optimalImageCoefficientA optimalImageCoefficientB
  fun_prop

end BrownianAffine
