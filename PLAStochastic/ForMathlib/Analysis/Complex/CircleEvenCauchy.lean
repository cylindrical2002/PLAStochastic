import PLAStochastic.ForMathlib.Analysis.Complex.CircleResolvent
import PLAStochastic.ForMathlib.Analysis.Complex.EvenSqrt
import Mathlib.Analysis.Complex.CauchyIntegral

/-! # Actual Cauchy identification of an even square-coordinate circle descent -/

noncomputable section
open Complex Set Metric
namespace PGM

def circleTraceEvenCauchy (X : C(Circle, ℂ)) (q : ℂ) : ℂ :=
  (2 * Real.pi * I : ℂ)⁻¹ *
    circleTraceIntegralCLM (X * circleTraceInvCoord * circleTraceResolvent q)

theorem circleTraceEvenCauchy_analyticAt (X : C(Circle, ℂ)) :
    AnalyticAt ℂ (fun u : C(Circle, ℂ) × ℂ => circleTraceEvenCauchy u.1 u.2) (X, 0) := by
  have hR : AnalyticAt ℂ (fun u : C(Circle, ℂ) × ℂ => circleTraceResolvent u.2) (X, 0) := by
    simpa only [Function.comp_apply] using!
      circleTraceResolvent_analyticAt.comp (x := (X, 0))
        (f := (Prod.snd : C(Circle, ℂ) × ℂ → ℂ)) analyticAt_snd
  have hK : AnalyticAt ℂ (fun u : C(Circle, ℂ) × ℂ =>
      u.1 * circleTraceInvCoord * circleTraceResolvent u.2) (X, 0) :=
    (analyticAt_fst.mul analyticAt_const).mul hR
  have hT : AnalyticAt ℂ (fun u : C(Circle, ℂ) × ℂ =>
      circleTraceIntegralCLM (u.1 * circleTraceInvCoord * circleTraceResolvent u.2)) (X, 0) :=
    ((circleTraceIntegralCLM).analyticAt _).comp hK
  exact analyticAt_const.mul hT

private theorem reciprocal_quadratic_circle_identity (z a : ℂ)
    (hz : z ≠ 0) (hminus : z - a ≠ 0) (hplus : z + a ≠ 0) :
    z⁻¹ * (1 - a ^ 2 * (z⁻¹) ^ 2)⁻¹ = ((z - a)⁻¹ + (z + a)⁻¹) / 2 := by
  have hza : z ^ 2 - a ^ 2 ≠ 0 := by
    rw [show z ^ 2 - a ^ 2 = (z - a) * (z + a) by ring]
    exact mul_ne_zero hminus hplus
  field_simp [hz, hminus, hplus, hza]
  ring

theorem circleTraceResolvent_kernel_of_square {q a : ℂ} (hq : ‖q‖ < 1)
    (ha : ‖a‖ < 1) (hsq : a ^ 2 = q) (z : Circle) :
    (z : ℂ)⁻¹ * circleTraceResolvent q z =
      (((z : ℂ) - a)⁻¹ + ((z : ℂ) + a)⁻¹) / 2 := by
  have hminus : (z : ℂ) - a ≠ 0 := by
    intro h
    have hn : ‖(z : ℂ)‖ = ‖a‖ := congrArg norm (sub_eq_zero.mp h)
    rw [Circle.norm_coe] at hn
    linarith
  have hplus : (z : ℂ) + a ≠ 0 := by
    intro h
    have hn : ‖(z : ℂ)‖ = ‖a‖ := by
      simpa only [norm_neg] using congrArg norm (eq_neg_of_add_eq_zero_left h)
    rw [Circle.norm_coe] at hn
    linarith
  rw [circleTraceResolvent_apply hq z]
  simpa only [hsq] using
    reciprocal_quadratic_circle_identity (z : ℂ) a
      (Circle.coe_ne_zero z) hminus hplus

theorem circleTraceResolvent_kernel {q : ℂ} (hq : ‖q‖ < 1) (z : Circle) :
    (z : ℂ)⁻¹ * circleTraceResolvent q z =
      (((z : ℂ) - Complex.sqrt q)⁻¹ + ((z : ℂ) + Complex.sqrt q)⁻¹) / 2 :=
  circleTraceResolvent_kernel_of_square hq
    (norm_sqrt_lt (by norm_num) (by simpa using hq)) (sqrt_sq_eq q) z

/-- The resolvent integral is the average of the two actual Cauchy values.
Local evenness at those two points identifies it with the square-root descent. -/
theorem circleTraceEvenCauchy_eq_of_square {f : ℂ → ℂ} {X : C(Circle, ℂ)} {q a : ℂ}
    (hf : DifferentiableOn ℂ f (closedBall 0 1)) (hq : ‖q‖ < 1)
    (ha : ‖a‖ < 1) (hsq : a ^ 2 = q)
    (hX : ∀ z : Circle, X z = f z) (heven : f (-a) = f a) :
    circleTraceEvenCauchy X q = f a := by
  have hap : a ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr ha
  have ham : -a ∈ ball (0 : ℂ) 1 := by simpa only [mem_ball_zero_iff, norm_neg] using ha
  have hne : ∀ z ∈ sphere (0 : ℂ) 1, z - a ≠ 0 := by
    intro z hz h
    have hn := mem_sphere_zero_iff_norm.mp hz
    rw [sub_eq_zero.mp h] at hn
    linarith
  have hne' : ∀ z ∈ sphere (0 : ℂ) 1, z + a ≠ 0 := by
    intro z hz h
    have hn := mem_sphere_zero_iff_norm.mp hz
    rw [eq_neg_of_add_eq_zero_left h, norm_neg] at hn
    linarith
  have hfc : ContinuousOn f (sphere (0 : ℂ) 1) := hf.continuousOn.mono sphere_subset_closedBall
  have hp : CircleIntegrable (fun z => (z - a)⁻¹ * f z) 0 1 :=
    (((continuousOn_id.sub continuousOn_const).inv₀ hne).mul hfc).circleIntegrable (by norm_num)
  have hm : CircleIntegrable (fun z => (z + a)⁻¹ * f z) 0 1 :=
    (((continuousOn_id.add continuousOn_const).inv₀ hne').mul hfc).circleIntegrable (by norm_num)
  have hCp : (∮ z in C(0, 1), (z - a)⁻¹ * f z) = (2 * Real.pi * I : ℂ) * f a := by
    simpa only [smul_eq_mul] using! hf.circleIntegral_sub_inv_smul hap
  have hCm : (∮ z in C(0, 1), (z + a)⁻¹ * f z) = (2 * Real.pi * I : ℂ) * f (-a) := by
    simpa only [smul_eq_mul, sub_neg_eq_add] using! hf.circleIntegral_sub_inv_smul ham
  have he : circleTraceIntegralCLM (X * circleTraceInvCoord * circleTraceResolvent q) =
      ∮ z in C(0, 1), (1 / 2 : ℂ) * ((z - a)⁻¹ * f z + (z + a)⁻¹ * f z) := by
    apply circleTraceIntegralCLM_eq_integral
    intro z
    change X z * (z : ℂ)⁻¹ * circleTraceResolvent q z = _
    rw [hX z, mul_assoc, circleTraceResolvent_kernel_of_square hq ha hsq z]
    ring
  have hT : (2 * Real.pi * I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero
  rw [circleTraceEvenCauchy, he, circleIntegral.integral_const_mul,
    circleIntegral.integral_add hp hm, hCp, hCm, heven]
  field_simp
  ring

theorem circleTraceEvenCauchy_eq {f : ℂ → ℂ} {X : C(Circle, ℂ)} {q : ℂ}
    (hf : DifferentiableOn ℂ f (closedBall 0 1)) (hq : ‖q‖ < 1)
    (hX : ∀ z : Circle, X z = f z) (heven : f (-Complex.sqrt q) = f (Complex.sqrt q)) :
    circleTraceEvenCauchy X q = f (Complex.sqrt q) :=
  circleTraceEvenCauchy_eq_of_square hf hq
    (norm_sqrt_lt (by norm_num) (by simpa using hq)) (sqrt_sq_eq q) hX heven

end PGM
