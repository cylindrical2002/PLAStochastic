import PLAStochastic.Index.GEP.StrongApprox.Quantile.DensitySandwich
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # WP5: tails from a quadratic-linear rate envelope

The bound uses a single exponential majorant on each tail. In particular, it
does not lose half of the rate when the Gaussian and exponential regimes meet.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

/-- On a positive half-line the quadratic-linear rate dominates a linear rate. -/
theorem sa_min_quadratic_linear_lower {R Y x : ℝ} (hY : 0 ≤ Y) (hx : Y ≤ x) :
    min Y R * x ≤ min (x ^ 2) (R * |x|) := by
  have hx0 : 0 ≤ x := hY.trans hx
  rw [abs_of_nonneg hx0]
  apply le_min
  · calc
      min Y R * x ≤ x * x := mul_le_mul_of_nonneg_right
        ((min_le_left Y R).trans hx) hx0
      _ = x ^ 2 := (sq x).symm
  · exact mul_le_mul_of_nonneg_right (min_le_right Y R) hx0

theorem sa_min_quadratic_linear_eq {Y R : ℝ} (hY : 0 ≤ Y) :
    min Y R * Y = min (Y ^ 2) (R * Y) := by
  rw [min_mul_of_nonneg Y R hY, sq]

/-- The rate envelope is integrable on every positive tail. -/
theorem sa_integrableOn_rateEnvelope_Ioi {c R Y : ℝ}
    (hc : 0 < c) (hR : 0 < R) (hY : 0 < Y) :
    IntegrableOn (fun x : ℝ => Real.exp (-c * min (x ^ 2) (R * |x|))) (Ioi Y) := by
  have hm : 0 < c * min Y R := mul_pos hc (lt_min hY hR)
  have hi := integrableOn_exp_mul_Ioi (neg_neg_of_pos hm) Y
  apply hi.mono' (by fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have hb := mul_le_mul_of_nonneg_left
    (sa_min_quadratic_linear_lower (R := R) hY.le (le_of_lt hx)) hc.le
  nlinarith

/-- A uniform tail bound, valid across the quadratic and linear regimes. -/
theorem sa_integral_rateEnvelope_tail {c R Y : ℝ}
    (hc : 0 < c) (hR : 0 < R) (hY : 0 < Y) :
    (∫ x : ℝ in Ioi Y, Real.exp (-c * min (x ^ 2) (R * |x|))) ≤
      Real.exp (-c * min (Y ^ 2) (R * Y)) / (c * min Y R) := by
  have hm : 0 < c * min Y R := mul_pos hc (lt_min hY hR)
  calc
    _ ≤ ∫ x : ℝ in Ioi Y, Real.exp (-(c * min Y R) * x) := by
      apply integral_mono_ae (sa_integrableOn_rateEnvelope_Ioi hc hR hY)
        (integrableOn_exp_mul_Ioi (neg_neg_of_pos hm) Y)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      apply Real.exp_le_exp.mpr
      have hb := mul_le_mul_of_nonneg_left
        (sa_min_quadratic_linear_lower (R := R) hY.le (le_of_lt hx)) hc.le
      nlinarith
    _ = _ := by
      rw [integral_exp_mul_Ioi (neg_neg_of_pos hm), neg_div_neg_eq]
      congr 2
      rw [neg_mul, mul_assoc, sa_min_quadratic_linear_eq hY.le]
      ring

/-- The same estimate for a closed right tail. -/
theorem sa_integral_rateEnvelope_closed_tail {c R Y : ℝ}
    (hc : 0 < c) (hR : 0 < R) (hY : 0 < Y) :
    (∫ x : ℝ in Ici Y, Real.exp (-c * min (x ^ 2) (R * |x|))) ≤
      Real.exp (-c * min (Y ^ 2) (R * Y)) / (c * min Y R) := by
  rw [integral_Ici_eq_integral_Ioi]
  exact sa_integral_rateEnvelope_tail hc hR hY

/-- Reflection transfers the same bound to the left tail. -/
theorem sa_integral_rateEnvelope_left_tail {c R Y : ℝ}
    (hc : 0 < c) (hR : 0 < R) (hY : 0 < Y) :
    (∫ x : ℝ in Iic (-Y), Real.exp (-c * min (x ^ 2) (R * |x|))) ≤
      Real.exp (-c * min (Y ^ 2) (R * Y)) / (c * min Y R) := by
  have he : (fun x : ℝ => Real.exp (-c * min ((-x) ^ 2) (R * |-x|))) =
      fun x : ℝ => Real.exp (-c * min (x ^ 2) (R * |x|)) := by
    funext x
    rw [neg_sq, abs_neg]
  rw [← integral_comp_neg_Ioi Y, he]
  exact sa_integral_rateEnvelope_tail hc hR hY

/-- The right CDF tail of the actual density inherits its pointwise envelope. -/
theorem SADensity.tail_le_rateEnvelope {p : ℝ → ℝ} (hp : SADensity p)
    {A c R Y : ℝ} (hA : 0 ≤ A) (hc : 0 < c) (hR : 0 < R) (hY : 0 < Y)
    (hb : ∀ x, Y ≤ x → p x ≤ A * Real.exp (-c * min (x ^ 2) (R * |x|))) :
    1 - cdf (hp.law : Measure ℝ) Y ≤
      A * Real.exp (-c * min (Y ^ 2) (R * Y)) / (c * min Y R) := by
  rw [hp.tail_eq_integral]
  calc
    _ ≤ ∫ x : ℝ in Ioi Y, A * Real.exp (-c * min (x ^ 2) (R * |x|)) := by
      apply integral_mono_ae hp.integrable.integrableOn
        ((sa_integrableOn_rateEnvelope_Ioi hc hR hY).const_mul A)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact hb x (le_of_lt hx)
    _ = A * ∫ x : ℝ in Ioi Y, Real.exp (-c * min (x ^ 2) (R * |x|)) :=
      integral_const_mul A _
    _ ≤ _ := by
      simpa only [mul_div_assoc] using
        mul_le_mul_of_nonneg_left (sa_integral_rateEnvelope_tail hc hR hY) hA

/-- The left CDF tail uses the same density, with no symmetry assumption. -/
theorem SADensity.cdf_le_rateEnvelope {p : ℝ → ℝ} (hp : SADensity p)
    {A c R Y : ℝ} (hA : 0 ≤ A) (hc : 0 < c) (hR : 0 < R) (hY : 0 < Y)
    (hb : ∀ x, x ≤ -Y → p x ≤ A * Real.exp (-c * min (x ^ 2) (R * |x|))) :
    cdf (hp.law : Measure ℝ) (-Y) ≤
      A * Real.exp (-c * min (Y ^ 2) (R * Y)) / (c * min Y R) := by
  rw [← hp.reflect_tail]
  apply hp.reflect.tail_le_rateEnvelope hA hc hR hY
  intro x hx
  have h := hb (-x) (neg_le_neg hx)
  simpa only [neg_sq, abs_neg] using h

/-- A two-sided density envelope controls both CDF tails at the same threshold. -/
theorem SADensity.tails_le_rateEnvelope {p : ℝ → ℝ} (hp : SADensity p)
    {A c R Y : ℝ} (hA : 0 ≤ A) (hc : 0 < c) (hR : 0 < R) (hY : 0 < Y)
    (hb : ∀ x, Y ≤ |x| → p x ≤ A * Real.exp (-c * min (x ^ 2) (R * |x|))) :
    (1 - cdf (hp.law : Measure ℝ) Y ≤
      A * Real.exp (-c * min (Y ^ 2) (R * Y)) / (c * min Y R)) ∧
    (cdf (hp.law : Measure ℝ) (-Y) ≤
      A * Real.exp (-c * min (Y ^ 2) (R * Y)) / (c * min Y R)) := by
  constructor
  · apply hp.tail_le_rateEnvelope hA hc hR hY
    intro x hx
    exact hb x (hx.trans (le_abs_self x))
  · apply hp.cdf_le_rateEnvelope hA hc hR hY
    intro x hx
    exact hb x (le_abs_self (-x) |>.trans_eq (abs_neg x) |>.trans' (by linarith))

end

end PGM
