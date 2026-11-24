import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue

/-! # The entire unit removing a quadratic exponential scale factor -/

noncomputable section
open Complex Set Metric Filter Topology
namespace PGM

def quadraticExpUnit (b T : ℂ) : ℂ := T * dslope Complex.exp 0 (b ^ 2 * T)

theorem complex_exp_sub_one_eq_mul_dslope (x : ℂ) :
    Complex.exp x - 1 = x * dslope Complex.exp 0 x := by
  simpa only [sub_zero, smul_eq_mul, exp_zero] using (sub_smul_dslope Complex.exp 0 x).symm

theorem exp_sub_one_eq_quadraticExpUnit (b T : ℂ) :
    Complex.exp (b ^ 2 * T) - 1 = b ^ 2 * quadraticExpUnit b T := by
  rw [complex_exp_sub_one_eq_mul_dslope]
  unfold quadraticExpUnit
  ring

theorem quadraticExpUnit_zero (T : ℂ) : quadraticExpUnit 0 T = T := by
  simp [quadraticExpUnit, dslope_same]

theorem complex_exp_dslope_differentiable : Differentiable ℂ (dslope Complex.exp 0) := by
  intro x
  have hd := (differentiableOn_dslope (f := Complex.exp) (s := univ)
    (c := 0) univ_mem).mpr Complex.differentiable_exp.differentiableOn
  exact (hd x (mem_univ x)).differentiableAt univ_mem

theorem quadraticExpUnit_joint_analyticAt (x : ℂ × ℂ) :
    AnalyticAt ℂ (fun x : ℂ × ℂ => quadraticExpUnit x.1 x.2) x := by
  have harg : AnalyticAt ℂ (fun x : ℂ × ℂ => x.1 ^ 2 * x.2) x :=
    (analyticAt_fst.pow 2).mul analyticAt_snd
  exact analyticAt_snd.mul ((complex_exp_dslope_differentiable.analyticAt _).comp harg)

theorem quadraticExpUnit_hasDerivAt (b T : ℂ) :
    HasDerivAt (quadraticExpUnit b) (Complex.exp (b ^ 2 * T)) T := by
  by_cases hb : b = 0
  · subst b
    have he : quadraticExpUnit 0 = id := funext quadraticExpUnit_zero
    rw [he]
    simpa only [zero_pow (by omega : 2 ≠ 0), zero_mul, exp_zero] using hasDerivAt_id T
  · have hb2 : b ^ 2 ≠ 0 := pow_ne_zero _ hb
    have he : quadraticExpUnit b = fun T => (Complex.exp (b ^ 2 * T) - 1) / b ^ 2 := by
      funext T
      rw [exp_sub_one_eq_quadraticExpUnit]
      field_simp
    rw [he]
    have hd := (((hasDerivAt_id T).const_mul (b ^ 2)).cexp.sub_const 1).div_const (b ^ 2)
    simpa only [mul_one, id_eq, mul_div_cancel_right₀ _ hb2] using! hd

theorem quadraticExpUnit_lipschitz {b T T' : ℂ} {A : ℝ}
    (hb : ‖b‖ ≤ 1) (hT : ‖T‖ ≤ A) (hT' : ‖T'‖ ≤ A) :
    ‖quadraticExpUnit b T - quadraticExpUnit b T'‖ ≤ Real.exp A * ‖T - T'‖ := by
  have hA : 0 ≤ A := (norm_nonneg T).trans hT
  apply (convex_closedBall (0 : ℂ) A).norm_image_sub_le_of_norm_deriv_le
    (fun w _ => (quadraticExpUnit_hasDerivAt b w).differentiableAt) ?_
    (by simpa only [mem_closedBall_zero_iff] using hT')
    (by simpa only [mem_closedBall_zero_iff] using hT)
  intro w hw
  rw [(quadraticExpUnit_hasDerivAt b w).deriv, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  calc
    (b ^ 2 * w).re ≤ ‖b ^ 2 * w‖ := re_le_norm _
    _ = ‖b‖ ^ 2 * ‖w‖ := by rw [norm_mul, norm_pow]
    _ ≤ 1 * A := mul_le_mul (pow_le_one₀ (norm_nonneg _) hb)
      (mem_closedBall_zero_iff.mp hw) (norm_nonneg _) (by norm_num)
    _ = A := one_mul _

end PGM
