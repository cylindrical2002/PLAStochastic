import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic

/-! # Exponential moments on the actual unit interval -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- The regular exponential quotient and all of its derivatives are actual integrals. -/
def exponentialUnitMoment (n : ℕ) (y : ℝ) : ℝ :=
  ∫ t : ℝ in Icc 0 1, t^n*Real.exp (y*t)

theorem continuous_exponentialUnitMoment_integrand (n : ℕ) (y : ℝ) :
    Continuous (fun t : ℝ => t^n*Real.exp (y*t)) := by fun_prop

theorem integrable_exponentialUnitMoment (n : ℕ) (y : ℝ) :
    IntegrableOn (fun t : ℝ => t^n*Real.exp (y*t)) (Icc 0 1) volume :=
  (continuous_exponentialUnitMoment_integrand n y).continuousOn.integrableOn_Icc

theorem hasDerivAt_exponentialUnitMoment (n : ℕ) (y : ℝ) :
    HasDerivAt (exponentialUnitMoment n) (exponentialUnitMoment (n+1) y) y := by
  let F : ℝ → ℝ → ℝ := fun a t => t^n*Real.exp (a*t)
  let F' : ℝ → ℝ → ℝ := fun a t => t^(n+1)*Real.exp (a*t)
  have hm (a : ℝ) : Measurable (F a) := by dsimp only [F]; fun_prop
  have hm' (a : ℝ) : Measurable (F' a) := by dsimp only [F']; fun_prop
  have hbound : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1), ∀ a ∈ Ioo (y-1) (y+1),
      ‖F' a t‖ ≤ Real.exp (|y|+1) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht a ha
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have hy : a ≤ |y|+1 := by linarith [ha.2,le_abs_self y]
    have hyt : a*t ≤ |y|+1 := calc
      a*t ≤ (|y|+1)*t := mul_le_mul_of_nonneg_right hy ht0
      _ ≤ (|y|+1)*1 := mul_le_mul_of_nonneg_left ht1 (by positivity)
      _ = _ := mul_one _
    dsimp only [F']
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ t^(n+1)*Real.exp (a*t))]
    calc
      _ ≤ 1*Real.exp (|y|+1) := mul_le_mul
        (pow_le_one₀ ht0 ht1) (Real.exp_le_exp.mpr hyt) (Real.exp_nonneg _) (by positivity)
      _ = _ := one_mul _
  have hd : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1), ∀ a ∈ Ioo (y-1) (y+1),
      HasDerivAt (F · t) (F' a t) a := by
    filter_upwards [] with t a ha
    convert! (((hasDerivAt_id a).mul_const t).exp).const_mul (t^n) using 1
    dsimp only [F',id]
    rw [pow_succ]
    ring
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds (by linarith : y-1<y) (by linarith : y<y+1))
    (Eventually.of_forall fun a => (hm a).aestronglyMeasurable)
    (integrable_exponentialUnitMoment n y) (hm' y).aestronglyMeasurable hbound
    (integrableOn_const (s := Icc (0 : ℝ) 1) (C := Real.exp (|y|+1)) (hs := isCompact_Icc.measure_lt_top.ne)) hd
  exact h.2

theorem continuous_exponentialUnitMoment (n : ℕ) : Continuous (exponentialUnitMoment n) :=
  continuous_iff_continuousAt.mpr fun y => (hasDerivAt_exponentialUnitMoment n y).continuousAt

theorem exponentialUnitMoment_eq_intervalIntegral (n : ℕ) (y : ℝ) :
    exponentialUnitMoment n y = ∫ t : ℝ in (0)..1, t^n*Real.exp (y*t) := by
  rw [exponentialUnitMoment,intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),integral_Icc_eq_integral_Ioc]

theorem exponentialUnitMoment_zero (n : ℕ) : exponentialUnitMoment n 0=1/(n+1) := by
  rw [exponentialUnitMoment_eq_intervalIntegral]
  simp only [zero_mul,Real.exp_zero,mul_one]
  rw [integral_pow]
  simp

theorem exponentialUnitMoment_zero_index {y : ℝ} (hy : y ≠ 0) :
    exponentialUnitMoment 0 y = (Real.exp y-1)/y := by
  rw [exponentialUnitMoment_eq_intervalIntegral]
  simp only [pow_zero,one_mul]
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => Real.exp (y*t)/y) (Real.exp (y*t)) t := by
    convert! ((((hasDerivAt_id t).const_mul y).exp).div_const y) using 1
    dsimp only [id]
    field_simp
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (show IntervalIntegrable (fun t : ℝ => Real.exp (y*t)) volume 0 1 from
      (by fun_prop : Continuous (fun t : ℝ => Real.exp (y*t))).intervalIntegrable _ _)
  simpa only [mul_one,mul_zero,Real.exp_zero,sub_div] using h

theorem exponentialUnitMoment_recurrence (n : ℕ) {y : ℝ} (hy : y ≠ 0) :
    exponentialUnitMoment (n+1) y =
      (Real.exp y-(n+1)*exponentialUnitMoment n y)/y := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => t^(n+1)*Real.exp (y*t))
      ((n+1)*(t^n*Real.exp (y*t))+y*(t^(n+1)*Real.exp (y*t))) t := by
    convert! (((hasDerivAt_id t).pow (n+1)).mul (((hasDerivAt_id t).const_mul y).exp)) using 1
    simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,Pi.pow_apply,id_eq]
    ring
  have hi (m : ℕ) : IntervalIntegrable (fun t : ℝ => t^m*Real.exp (y*t)) volume 0 1 :=
    (continuous_exponentialUnitMoment_integrand m y).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (((hi n).const_mul (n+1)).add ((hi (n+1)).const_mul y))
  simp only [intervalIntegral.integral_add ((hi n).const_mul (n+1)) ((hi (n+1)).const_mul y),
    intervalIntegral.integral_const_mul,←exponentialUnitMoment_eq_intervalIntegral,
    one_pow,one_mul,mul_one,zero_pow (by omega : n+1 ≠ 0),zero_mul,sub_zero] at h
  apply (eq_div_iff hy).mpr
  linear_combination h

end BrownianAffine
