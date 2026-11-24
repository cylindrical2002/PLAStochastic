import PLAStochastic.ForMathlib.Analysis.Complex.CircleTraceIntegral
import PLAStochastic.ForMathlib.Analysis.Complex.CompactIntegralAnalytic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Normed.Ring.Units

/-! # Analytic functional circle resolvents with actual pointwise inverses -/

noncomputable section
open Complex
open scoped Ring
namespace PGM

def circleTraceResolvent (q : ℂ) : C(Circle, ℂ) :=
  (1 - ContinuousMap.const Circle q * circleTraceInvCoord ^ 2)⁻¹ʳ

theorem circleTraceResolvent_analyticAt : AnalyticAt ℂ circleTraceResolvent 0 := by
  have hm : AnalyticAt ℂ (fun q : ℂ => ContinuousMap.const Circle q * circleTraceInvCoord ^ 2) 0 :=
    analyticAt_id.continuousMap_const.mul analyticAt_const
  have hInv : AnalyticAt ℂ (fun X : C(Circle, ℂ) => (1 - X)⁻¹ʳ)
      (ContinuousMap.const Circle (0 : ℂ) * circleTraceInvCoord ^ 2) := by
    simpa only [ContinuousMap.const_zero, zero_mul] using
      analyticAt_inverse_one_sub ℂ C(Circle, ℂ)
  exact hInv.comp (x := (0 : ℂ))
    (f := fun q : ℂ => ContinuousMap.const Circle q * circleTraceInvCoord ^ 2) hm

theorem circleTraceResolvent_unit {q : ℂ} (hq : ‖q‖ < 1) :
    IsUnit (1 - ContinuousMap.const Circle q * circleTraceInvCoord ^ 2) := by
  have hn : ‖ContinuousMap.const Circle q * circleTraceInvCoord ^ 2‖ ≤ ‖q‖ := by
    apply (ContinuousMap.norm_le _ (norm_nonneg q)).mpr
    intro z
    change ‖q * ((z : ℂ)⁻¹) ^ 2‖ ≤ ‖q‖
    simp only [norm_mul, norm_pow, norm_inv, Circle.norm_coe, inv_one, one_pow, mul_one]
    exact le_rfl
  exact (Units.oneSub (ContinuousMap.const Circle q * circleTraceInvCoord ^ 2)
    (hn.trans_lt hq)).isUnit

theorem circleTraceResolvent_mul {q : ℂ} (hq : ‖q‖ < 1) (z : Circle) :
    (1 - q * ((z : ℂ)⁻¹) ^ 2) * circleTraceResolvent q z = 1 := by
  have h := congrArg (fun X : C(Circle, ℂ) => X z)
    (Ring.mul_inverse_cancel _ (circleTraceResolvent_unit hq))
  exact h

theorem circleTraceResolvent_den_ne {q : ℂ} (hq : ‖q‖ < 1) (z : Circle) :
    1 - q * ((z : ℂ)⁻¹) ^ 2 ≠ 0 := by
  intro h
  have he := circleTraceResolvent_mul hq z
  rw [h, zero_mul] at he
  exact zero_ne_one he

theorem circleTraceResolvent_apply {q : ℂ} (hq : ‖q‖ < 1) (z : Circle) :
    circleTraceResolvent q z = (1 - q * ((z : ℂ)⁻¹) ^ 2)⁻¹ := by
  have h := circleTraceResolvent_mul hq z
  have he : circleTraceResolvent q z = 1 / (1 - q * ((z : ℂ)⁻¹) ^ 2) :=
    (eq_div_iff (circleTraceResolvent_den_ne hq z)).mpr (by simpa only [mul_comm] using h)
  exact he.trans (one_div _)

end PGM
