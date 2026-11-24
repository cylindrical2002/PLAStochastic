import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic

/-! # Exponential-integral kernels for absolute third moments

The standard exponential integral is extended by zero outside its positive domain.
All kernel formulas below concern positive arguments.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

def exponentialIntegralE1 (x : ℝ) : ℝ :=
  if 0 < x then ∫ v : ℝ in Ioi x, Real.exp (-v) / v else 0

theorem integrableOn_exponentialIntegralE1_integrand {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun v : ℝ => Real.exp (-v) / v) (Ioi x) := by
  have he : IntegrableOn (fun v : ℝ => Real.exp (-v) / x) (Ioi x) := by
    simpa only [neg_one_mul] using! (integrableOn_exp_mul_Ioi (a := -1) (by norm_num) x).div_const x
  have hm : Measurable (fun v : ℝ => Real.exp (-v) / v) := by fun_prop
  refine he.mono' hm.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  rw [Real.norm_eq_abs, abs_of_pos (div_pos (Real.exp_pos _) (hx.trans hv))]
  exact div_le_div_of_nonneg_left (Real.exp_nonneg _) hx hv.le

theorem exponentialIntegralE1_nonneg (x : ℝ) : 0 ≤ exponentialIntegralE1 x := by
  unfold exponentialIntegralE1
  split_ifs with hx
  · apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact (div_pos (Real.exp_pos _) (hx.trans hv)).le
  · rfl

theorem exponentialIntegralE1_le {x : ℝ} (hx : 0 < x) :
    exponentialIntegralE1 x ≤ Real.exp (-x) / x := by
  have he : IntegrableOn (fun v : ℝ => Real.exp (-v) / x) (Ioi x) := by
    simpa only [neg_one_mul] using! (integrableOn_exp_mul_Ioi (a := -1) (by norm_num) x).div_const x
  have h := integral_mono_ae (integrableOn_exponentialIntegralE1_integrand hx) he (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact div_le_div_of_nonneg_left (Real.exp_nonneg _) hx hv.le)
  change (∫ v : ℝ in Ioi x, Real.exp (-v) / v) ≤ _ at h
  unfold exponentialIntegralE1
  rw [if_pos hx]
  convert! h using 1
  rw [integral_div]
  have hExp : (∫ v : ℝ in Ioi x, Real.exp (-v)) = Real.exp (-x) := by
    simpa using integral_exp_mul_Ioi (a := -1) (by norm_num) x
  rw [hExp]

theorem exponentialIntegralE1_sub {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    exponentialIntegralE1 x - exponentialIntegralE1 y =
      ∫ v in x..y, Real.exp (-v) / v := by
  simp only [exponentialIntegralE1, if_pos hx, if_pos hy]
  exact intervalIntegral.integral_Ioi_sub_Ioi'
    (integrableOn_exponentialIntegralE1_integrand hx) (integrableOn_exponentialIntegralE1_integrand hy)

theorem hasDerivAt_exponentialIntegralE1 {x : ℝ} (hx : 0 < x) :
    HasDerivAt exponentialIntegralE1 (-Real.exp (-x) / x) x := by
  have hc : ContinuousOn (fun v : ℝ => Real.exp (-v) / v) (uIcc 1 x) := by
    intro v hv
    have hv0 : 0 < v := (lt_min zero_lt_one hx).trans_le hv.1
    exact ((by fun_prop : ContinuousAt (fun v : ℝ => Real.exp (-v)) v).div
      continuousAt_id hv0.ne').continuousWithinAt
  have hm : StronglyMeasurable (fun v : ℝ => Real.exp (-v) / v) := by fun_prop
  have hd := (intervalIntegral.integral_hasDerivAt_right hc.intervalIntegrable
    hm.stronglyMeasurableAtFilter
    ((by fun_prop : ContinuousAt (fun v : ℝ => Real.exp (-v)) x).div continuousAt_id hx.ne')).const_sub
      (exponentialIntegralE1 1)
  have he : exponentialIntegralE1 =ᶠ[𝓝 x]
      (fun y => exponentialIntegralE1 1 - ∫ v in (1 : ℝ)..y, Real.exp (-v) / v) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    have h := exponentialIntegralE1_sub zero_lt_one hy
    linarith
  simpa only [neg_div] using hd.congr_of_eventuallyEq he

theorem continuousOn_exponentialIntegralE1 : ContinuousOn exponentialIntegralE1 (Ioi 0) :=
  fun _ hx => (hasDerivAt_exponentialIntegralE1 hx).continuousAt.continuousWithinAt

theorem measurable_exponentialIntegralE1 : Measurable exponentialIntegralE1 := by
  have h := continuousOn_exponentialIntegralE1.measurable_piecewise
    (g := fun _ : ℝ => (0 : ℝ)) continuousOn_const measurableSet_Ioi
  convert! h using 1
  funext x
  by_cases hx : 0 < x <;> simp [Set.piecewise, exponentialIntegralE1, hx]

private theorem image_div_Ioo {x : ℝ} (hx : 0 < x) :
    (fun u : ℝ => x / u) '' Ioo 0 1 = Ioi x := by
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact (lt_div_iff₀ hu.1).mpr (mul_lt_of_lt_one_right hx hu.2)
  · intro hv
    have hv0 : 0 < v := hx.trans hv
    refine ⟨x / v, ⟨div_pos hx hv0, (div_lt_one hv0).mpr hv⟩, ?_⟩
    field_simp

private theorem div_injOn_Ioo {x : ℝ} (hx : 0 < x) :
    InjOn (fun u : ℝ => x / u) (Ioo 0 1) := by
  intro u hu v hv he
  have h := (div_eq_div_iff hu.1.ne' hv.1.ne').mp he
  nlinarith

private theorem hasDerivWithinAt_div_Ioo (x : ℝ) :
    ∀ u ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt (fun u => x / u) (-x / u ^ 2) (Ioo 0 1) u := by
  intro u hu
  simpa only [Pi.div_apply, id_eq, zero_mul, mul_one, zero_sub] using!
    ((hasDerivAt_const u x).div (hasDerivAt_id u) hu.1.ne').hasDerivWithinAt

private theorem inverse_exp_jacobian {x u : ℝ} (hx : 0 < x) (hu : 0 < u) :
    |(-x / u ^ 2)| * (Real.exp (-(x / u)) / (x / u)) = Real.exp (-x / u) / u := by
  rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx.le) (sq_nonneg _))]
  rw [neg_div, neg_neg, neg_div]
  field_simp

theorem exponentialIntegralE1_eq_integral {x : ℝ} (hx : 0 < x) :
    exponentialIntegralE1 x = ∫ u in (0 : ℝ)..1, Real.exp (-x / u) / u := by
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (hasDerivWithinAt_div_Ioo x) (div_injOn_Ioo hx) (fun v : ℝ => Real.exp (-v) / v)
  rw [image_div_Ioo hx] at h
  unfold exponentialIntegralE1
  rw [if_pos hx, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo, h]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u hu
  exact inverse_exp_jacobian hx hu.1

theorem intervalIntegrable_exponentialIntegralE1_inverse {x : ℝ} (hx : 0 < x) :
    IntervalIntegrable (fun u : ℝ => Real.exp (-x / u) / u) volume 0 1 := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
    (hasDerivWithinAt_div_Ioo x) (div_injOn_Ioo hx) (fun v : ℝ => Real.exp (-v) / v)
  rw [image_div_Ioo hx] at h
  have hi := h.mp (integrableOn_exponentialIntegralE1_integrand hx)
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
  exact hi.congr_fun (fun u hu => inverse_exp_jacobian hx hu.1) measurableSet_Ioo

theorem hasDerivAt_exponentialIntegralE1_inverse {x u : ℝ} (hx : 0 < x) (hu : 0 < u) :
    HasDerivAt (fun u => exponentialIntegralE1 (x / u)) (Real.exp (-x / u) / u) u := by
  have hd := (hasDerivAt_exponentialIntegralE1 (div_pos hx hu)).comp u
    ((hasDerivAt_const u x).div (hasDerivAt_id u) hu.ne')
  convert! hd using 1
  simp only [zero_mul, mul_one, zero_sub, neg_div]
  field_simp

theorem expNegInvGlue_div {x u : ℝ} (hx : 0 < x) (hu : 0 < u) :
    expNegInvGlue (u / x) = Real.exp (-x / u) := by
  simp only [expNegInvGlue, not_le.mpr (div_pos hu hx), if_false, inv_div, neg_div]

theorem continuous_inverseExp (x : ℝ) :
    Continuous (fun u : ℝ => expNegInvGlue (u / x)) :=
  (expNegInvGlue.contDiff (n := 0)).continuous.comp (continuous_id.div_const x)

theorem hasDerivAt_inverseExp {x u : ℝ} (hx : 0 < x) (hu : 0 < u) :
    HasDerivAt (fun u : ℝ => expNegInvGlue (u / x))
      (x / u ^ 2 * Real.exp (-x / u)) u := by
  have hd := (((hasDerivAt_const u (-x)).div (hasDerivAt_id u) hu.ne').exp)
  have he : (fun u : ℝ => expNegInvGlue (u / x)) =ᶠ[𝓝 u]
      (fun u : ℝ => Real.exp (-x / u)) := by
    filter_upwards [Ioi_mem_nhds hu] with v hv
    exact expNegInvGlue_div hx hv
  convert! hd.congr_of_eventuallyEq he using 1
  simp
  ring

/-- Auxiliary reciprocal-exponential moments, with the natural zero value at the origin. -/
def reciprocalExpMoment (n : ℕ) (x : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..1, u ^ n * expNegInvGlue (u / x)

theorem intervalIntegrable_reciprocalExpMoment (n : ℕ) (x : ℝ) :
    IntervalIntegrable (fun u : ℝ => u ^ n * expNegInvGlue (u / x)) volume 0 1 :=
  ((continuous_id.pow n).mul (continuous_inverseExp x)).intervalIntegrable _ _

theorem reciprocalExpMoment_zero {x : ℝ} (hx : 0 < x) :
    reciprocalExpMoment 0 x = Real.exp (-x) - x * exponentialIntegralE1 x := by
  have hi : IntervalIntegrable (fun u : ℝ => expNegInvGlue (u / x) +
      x * (Real.exp (-x / u) / u)) volume 0 1 :=
    ((continuous_inverseExp x).intervalIntegrable _ _).add
      ((intervalIntegrable_exponentialIntegralE1_inverse hx).const_mul x)
  have hd : ∀ u ∈ Ioo (0 : ℝ) 1, HasDerivAt
      (fun u : ℝ => u * expNegInvGlue (u / x))
      (expNegInvGlue (u / x) + x * (Real.exp (-x / u) / u)) u := by
    intro u hu
    convert! (hasDerivAt_id u).mul (hasDerivAt_inverseExp hx hu.1) using 1
    dsimp only [id_eq]
    field_simp [hu.1.ne']
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (0 : ℝ) ≤ 1)
    (continuous_id.mul (continuous_inverseExp x)).continuousOn hd hi
  rw [intervalIntegral.integral_add (continuous_inverseExp x |>.intervalIntegrable _ _)
    ((intervalIntegrable_exponentialIntegralE1_inverse hx).const_mul x),
    intervalIntegral.integral_const_mul, ← exponentialIntegralE1_eq_integral hx] at h
  dsimp only [Pi.mul_apply, id_eq] at h
  simp only [expNegInvGlue_div hx zero_lt_one, div_one, one_mul, zero_mul, sub_zero] at h
  simp only [reciprocalExpMoment, pow_zero, one_mul]
  linarith

theorem reciprocalExpMoment_succ {x : ℝ} (hx : 0 < x) (n : ℕ) :
    reciprocalExpMoment (n + 1) x =
      (Real.exp (-x) - x * reciprocalExpMoment n x) / (n + 2) := by
  have hi := ((intervalIntegrable_reciprocalExpMoment (n + 1) x).const_mul (n + 2 : ℝ)).add
    ((intervalIntegrable_reciprocalExpMoment n x).const_mul x)
  have hd : ∀ u ∈ Ioo (0 : ℝ) 1, HasDerivAt
      (fun u : ℝ => u ^ (n + 2) * expNegInvGlue (u / x))
      ((n + 2 : ℝ) * (u ^ (n + 1) * expNegInvGlue (u / x)) +
        x * (u ^ n * expNegInvGlue (u / x))) u := by
    intro u hu
    convert! ((hasDerivAt_id u).pow (n + 2)).mul (hasDerivAt_inverseExp hx hu.1) using 1
    dsimp only [Pi.pow_apply, id_eq]
    simp only [Nat.cast_add, Nat.cast_ofNat, show n + 2 - 1 = n + 1 by omega,
      expNegInvGlue_div hx hu.1]
    field_simp [hu.1.ne']
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (0 : ℝ) ≤ 1)
    (((continuous_id.pow (n + 2)).mul (continuous_inverseExp x)).continuousOn) hd hi
  rw [intervalIntegral.integral_add
    ((intervalIntegrable_reciprocalExpMoment (n + 1) x).const_mul (n + 2 : ℝ))
    ((intervalIntegrable_reciprocalExpMoment n x).const_mul x),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
  dsimp only [Pi.mul_apply, Pi.pow_apply, id_eq] at h
  simp only [expNegInvGlue_div hx zero_lt_one, div_one, one_pow, one_mul,
    zero_pow (by omega : n + 2 ≠ 0), zero_mul, sub_zero] at h
  change (n + 2 : ℝ) * reciprocalExpMoment (n + 1) x + x * reciprocalExpMoment n x = _ at h
  apply (eq_div_iff (by positivity : (n + 2 : ℝ) ≠ 0)).mpr
  linarith

/-- The elementary kernel appearing in the anchored absolute third moment. -/
def kernelR0 (x : ℝ) : ℝ :=
  ((x ^ 2 + 5 * x + 2) * Real.exp (-x) -
    x * (x ^ 2 + 6 * x + 6) * exponentialIntegralE1 x) / 6

def kernelR1 (x : ℝ) : ℝ :=
  ((2 - 6 * x - 7 * x ^ 2 - x ^ 3) * Real.exp (-x) +
    x ^ 2 * (x + 2) * (x + 6) * exponentialIntegralE1 x) / 24

def kernelRE (x : ℝ) : ℝ :=
  ((x ^ 3 + 9 * x ^ 2 + 18 * x + 6) * exponentialIntegralE1 x -
    (x ^ 2 + 8 * x + 11) * Real.exp (-x)) / 18

private theorem kernelR0_eq_glue {x : ℝ} (hx : 0 < x) :
    kernelR0 x = ∫ u in (0 : ℝ)..1, (1 - u) ^ 2 * expNegInvGlue (u / x) := by
  have hi0 := intervalIntegrable_reciprocalExpMoment 0 x
  have hi1 := intervalIntegrable_reciprocalExpMoment 1 x
  have hi2 := intervalIntegrable_reciprocalExpMoment 2 x
  have he : (fun u : ℝ => (1 - u) ^ 2 * expNegInvGlue (u / x)) =
      (fun u : ℝ => u ^ 0 * expNegInvGlue (u / x) -
        2 * (u ^ 1 * expNegInvGlue (u / x)) + u ^ 2 * expNegInvGlue (u / x)) := by
    funext u
    ring
  rw [he, intervalIntegral.integral_add (hi0.sub (hi1.const_mul 2)) hi2,
    intervalIntegral.integral_sub hi0 (hi1.const_mul 2), intervalIntegral.integral_const_mul]
  change kernelR0 x = reciprocalExpMoment 0 x - 2 * reciprocalExpMoment 1 x + reciprocalExpMoment 2 x
  rw [reciprocalExpMoment_succ hx 1, reciprocalExpMoment_succ hx 0, reciprocalExpMoment_zero hx]
  unfold kernelR0
  norm_num
  ring

theorem kernelR0_eq_integral {x : ℝ} (hx : 0 < x) :
    kernelR0 x = ∫ u in (0 : ℝ)..1, (1 - u) ^ 2 * Real.exp (-x / u) := by
  rw [kernelR0_eq_glue hx, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro u hu
  dsimp only
  rw [expNegInvGlue_div hx hu.1]

theorem kernelR0_pos {x : ℝ} (hx : 0 < x) : 0 < kernelR0 x := by
  rw [kernelR0_eq_glue hx]
  apply intervalIntegral.integral_pos zero_lt_one
    (((continuous_const.sub continuous_id).pow 2).mul (continuous_inverseExp x)).continuousOn
  · intro u _
    exact mul_nonneg (sq_nonneg _) (expNegInvGlue.nonneg _)
  · refine ⟨1 / 2, by norm_num, ?_⟩
    exact mul_pos (by norm_num) (expNegInvGlue.pos_of_pos (div_pos (by norm_num) hx))

private theorem integral_square_one_sub : (∫ u in (0 : ℝ)..1, (1 - u) ^ 2) = 1 / 3 := by
  have hd : ∀ u ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun u : ℝ => -(1 - u) ^ 3 / 3) ((1 - u) ^ 2) u := by
    intro u _
    convert! ((((hasDerivAt_const u 1).sub (hasDerivAt_id u)).pow 3).neg.div_const 3) using 1
    simp
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (0 : ℝ) ≤ 1) (by fun_prop) hd
      ((by fun_prop : Continuous (fun u : ℝ => (1 - u) ^ 2)).intervalIntegrable _ _)
  norm_num at h
  exact h

theorem kernelR0_le_exp {x : ℝ} (hx : 0 < x) : kernelR0 x ≤ Real.exp (-x) / 3 := by
  rw [kernelR0_eq_glue hx]
  calc
    _ ≤ ∫ u in (0 : ℝ)..1, (1 - u) ^ 2 * Real.exp (-x) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        ((((continuous_const.sub continuous_id).pow 2).mul (continuous_inverseExp x)).intervalIntegrable _ _)
        ((by fun_prop : Continuous (fun u : ℝ => (1 - u) ^ 2 * Real.exp (-x))).intervalIntegrable _ _)
      intro u hu
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      rw [← show expNegInvGlue (1 / x) = Real.exp (-x) by simpa using expNegInvGlue_div hx zero_lt_one]
      exact expNegInvGlue.monotone (div_le_div_of_nonneg_right hu.2 hx.le)
    _ = Real.exp (-x) / 3 := by
      rw [intervalIntegral.integral_mul_const, integral_square_one_sub]
      ring

theorem intervalIntegrable_kernelR0 {x : ℝ} (hx : 0 < x) :
    IntervalIntegrable (fun u : ℝ => (1 - u) ^ 2 * Real.exp (-x / u)) volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
  have hi : IntervalIntegrable (fun u : ℝ => (1 - u) ^ 2 * expNegInvGlue (u / x)) volume 0 1 :=
    (((continuous_const.sub continuous_id).pow 2).mul
      (continuous_inverseExp x)).intervalIntegrable 0 1
  have h := (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp hi
  apply h.congr_fun _ measurableSet_Ioo
  intro u hu
  dsimp only
  rw [expNegInvGlue_div hx hu.1]

theorem continuousOn_kernelR0 : ContinuousOn kernelR0 (Ioi 0) := by
  intro x hx
  have he := (hasDerivAt_exponentialIntegralE1 hx).continuousAt
  have hc : ContinuousAt kernelR0 x := by
    unfold kernelR0
    fun_prop
  exact hc.continuousWithinAt

end BrownianAffine
