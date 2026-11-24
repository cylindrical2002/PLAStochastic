import PLAStochastic.ForMathlib.Analysis.SpecialFunctions.CenteredCoth.RemainderKernel
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Exact integrals of the actual positive cotangent remainders -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- A real arctangent primitive controls both integrability and the exact rational-kernel integral. -/
theorem hasDerivAt_scaled_arctan {a : ℝ} (ha : 0 < a) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.arctan (y/a)/a) (1/(x^2+a^2)) x := by
  convert! ((Real.hasDerivAt_arctan (x/a)).comp x ((hasDerivAt_id x).div_const a)).div_const a using 1
  field_simp
  ring

theorem tendsto_scaled_arctan {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => Real.arctan (x/a)/a) atTop (𝓝 (Real.pi/2/a)) := by
  exact ((tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp
    (tendsto_id.atTop_div_const ha)).div_const a

theorem integrableOn_reciprocal_sq_add_sq {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => 1/(x^2+a^2)) (Ioi 0) volume := by
  apply integrableOn_Ioi_deriv_of_nonneg (g := fun x : ℝ => Real.arctan (x/a)/a)
    (show ContinuousWithinAt (fun x : ℝ => Real.arctan (x/a)/a) (Ici 0) 0 by fun_prop)
    (fun x _ => hasDerivAt_scaled_arctan ha x) (fun x _ => by positivity)
    (tendsto_scaled_arctan ha)

theorem integral_reciprocal_sq_add_sq {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ in Ioi 0, 1/(x^2+a^2)) = Real.pi/(2*a) := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg (g := fun x : ℝ => Real.arctan (x/a)/a)
    (show ContinuousWithinAt (fun x : ℝ => Real.arctan (x/a)/a) (Ici 0) 0 by fun_prop)
    (fun x _ => hasDerivAt_scaled_arctan ha x) (fun x _ => by positivity)
    (tendsto_scaled_arctan ha)
  simpa only [zero_div, Real.arctan_zero, sub_zero, div_div] using h

theorem integrableOn_cothRemainderTerm (p n : ℕ) :
    IntegrableOn (cothRemainderTerm p n) (Ioi 0) volume := by
  have he : cothRemainderTerm p n = fun x : ℝ =>
      (2/cothPole n^(2*p))*(1/(x^2+cothPole n^2)) := by
    funext x
    unfold cothRemainderTerm
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he]
  exact (integrableOn_reciprocal_sq_add_sq (cothPole_pos n)).const_mul
    (2/cothPole n^(2*p))

theorem integral_cothRemainderTerm (p n : ℕ) :
    (∫ x : ℝ in Ioi 0, cothRemainderTerm p n x) = Real.pi/cothPole n^(2*p+1) := by
  have he : cothRemainderTerm p n = fun x : ℝ =>
      (2/cothPole n^(2*p))*(1/(x^2+cothPole n^2)) := by
    funext x
    unfold cothRemainderTerm
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he, integral_const_mul, integral_reciprocal_sq_add_sq (cothPole_pos n)]
  have ha := (cothPole_pos n).ne'
  rw [pow_succ]
  field_simp

/-- Absolute Fubini identifies every positive-index remainder integral with its pole series. -/
theorem integral_cothRemainder {p : ℕ} (hp : 0 < p) :
    (∫ x : ℝ in Ioi 0, cothRemainder p x) = ∑' n, Real.pi/cothPole n^(2*p+1) := by
  have hs : Summable (fun n => ∫ x : ℝ in Ioi 0, ‖cothRemainderTerm p n x‖) := by
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (cothRemainderTerm_nonneg p _ _), integral_cothRemainderTerm]
    convert! (summable_cothPole_inv_pow (by omega : 1 < 2*p+1)).mul_left Real.pi using 1
    funext n
    ring
  exact (integral_tsum_of_summable_integral_norm (integrableOn_cothRemainderTerm p) hs).symm.trans
    (tsum_congr (integral_cothRemainderTerm p))

/-- The remainder is genuinely integrable; a positive evaluated integral excludes the
nonintegrable convention for the Bochner integral. -/
theorem integrableOn_cothRemainder {p : ℕ} (hp : 0 < p) :
    IntegrableOn (cothRemainder p) (Ioi 0) volume := by
  have hs : Summable (fun n => Real.pi/cothPole n^(2*p+1)) := by
    simpa only [mul_one_div] using
      (summable_cothPole_inv_pow (by omega : 1 < 2*p+1)).mul_left Real.pi
  have hpos := hs.tsum_pos (fun n => by have := cothPole_pos n; positivity) 0
    (by have := cothPole_pos 0; positivity)
  rw [← integral_cothRemainder hp] at hpos
  by_contra hi
  rw [integral_undef hi] at hpos
  exact (lt_irrefl 0) hpos

theorem tsum_cothPole_inv_pow {k : ℕ} (hk : 1 < k) :
    (∑' n : ℕ, 1/cothPole n^k) = (riemannZeta (k : ℂ)).re/Real.pi^k := by
  have hs := Real.summable_one_div_nat_pow.mpr hk
  have hshift := hs.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_pow (by omega : k ≠ 0),
    div_zero, zero_add] at hshift
  calc
    _ = (1/Real.pi^k)*(∑' n : ℕ, 1/((n : ℝ)+1)^k) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      simp only [cothPole, mul_pow, div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by
      simp only [Nat.cast_add, Nat.cast_one] at hshift
      rw [hshift, tsum_reciprocal_pow_eq_zeta hk]
      ring

/-- The exact odd-zeta value of every positive-index cotangent remainder integral. -/
theorem integral_cothRemainder_eq_zeta {p : ℕ} (hp : 0 < p) :
    (∫ x : ℝ in Ioi 0, cothRemainder p x) =
      (riemannZeta ((2*p+1 : ℕ) : ℂ)).re/Real.pi^(2*p) := by
  rw [integral_cothRemainder hp]
  simp_rw [div_eq_mul_one_div Real.pi]
  rw [tsum_mul_left, tsum_cothPole_inv_pow (by omega : 1 < 2*p+1), pow_succ]
  field_simp

end BrownianAffine
