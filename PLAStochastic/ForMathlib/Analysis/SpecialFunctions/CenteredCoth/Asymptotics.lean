import PLAStochastic.ForMathlib.Analysis.SpecialFunctions.CenteredCoth.RemainderValues

/-! # The actual centered cotangent: differential equation and controlled expansions -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- The Riccati identity is derived from the actual hyperbolic quotient. -/
theorem hasDerivAt_centeredCoth {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt centeredCoth (1-centeredCoth x^2-2*centeredCoth x/x) x := by
  have hs := Real.sinh_ne_zero.mpr hx
  convert! ((Real.hasDerivAt_cosh x).div (Real.hasDerivAt_sinh x) hs).sub
    ((hasDerivAt_const x (1 : ℝ)).div (hasDerivAt_id x) hx) using 1
  dsimp only [centeredCoth,id]
  field_simp
  have hh := congrArg (fun y : ℝ => y*x^2) (Real.cosh_sq_sub_sinh_sq x)
  nlinarith [hh]

theorem centeredCoth_eq_first_remainder {x : ℝ} (hx : 0 < x) :
    centeredCoth x = x/3-x^3*cothRemainder 1 x := by
  rw [centeredCoth_eq_mul_remainder hx,cothRemainder_recurrence 0 x,cothRemainder_zero_zero]
  norm_num only
  ring

theorem centeredCoth_eq_fourth_remainder {x : ℝ} (hx : 0 < x) :
    centeredCoth x = x/3-x^3/45+2*x^5/945-x^7/4725+x^9*cothRemainder 4 x := by
  rw [centeredCoth_eq_mul_remainder hx,cothRemainder_recurrence 0 x,cothRemainder_zero_zero]
  norm_num only
  rw [cothRemainder_recurrence 1 x,cothRemainder_one_zero]
  norm_num only
  rw [cothRemainder_recurrence 2 x,cothRemainder_two_zero]
  norm_num only
  rw [cothRemainder_recurrence 3 x,cothRemainder_three_zero]
  norm_num only
  ring

theorem centeredCoth_eq_exp {x : ℝ} (hx : 0 < x) :
    centeredCoth x = (1+Real.exp (-2*x))/(1-Real.exp (-2*x))-1/x := by
  unfold centeredCoth
  congr 1
  rw [Real.cosh_eq,Real.sinh_eq,Real.exp_neg,
    show -2*x = -(x+x) by ring,Real.exp_neg,Real.exp_add]
  have he := Real.exp_pos x
  have h1 := Real.one_lt_exp_iff.mpr hx
  field_simp

theorem tendsto_centeredCoth_atTop : Tendsto centeredCoth atTop (𝓝 (1 : ℝ)) := by
  have he : Tendsto (fun x : ℝ => Real.exp (-2*x)) atTop (𝓝 0) := by
    convert! Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)) using 1
    simp [Function.comp_def]
  have hzero : Tendsto (fun x : ℝ => (1+Real.exp (-2*x))/(1-Real.exp (-2*x))-1/x)
      atTop (𝓝 1) := by
    simpa only [one_div,add_zero,sub_zero,div_one,Pi.div_apply] using! ((tendsto_const_nhds.add he).div (tendsto_const_nhds.sub he)
      (by norm_num : (1 : ℝ)-0 ≠ 0)).sub tendsto_inv_atTop_zero
  apply hzero.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (centeredCoth_eq_exp hx).symm

end BrownianAffine
