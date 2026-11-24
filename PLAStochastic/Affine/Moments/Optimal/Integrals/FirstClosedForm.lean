import PLAStochastic.Affine.Moments.Optimal.Integrals.FirstIntegrand

/-! # Exact real evaluation of the first optimal integrand -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- A primitive after removing its actual Laurent singularity at zero. -/
def optimalPrimitiveOne (x : ℝ) : ℝ :=
  -2*regularCenteredCoth x^3/3+x*cothRemainder 0 x^2+5*x*cothRemainder 1 x

theorem continuous_optimalPrimitiveOne : Continuous optimalPrimitiveOne := by
  unfold optimalPrimitiveOne
  exact (((continuous_regularCenteredCoth.pow 3).const_mul (-2)).div_const 3).add
    (continuous_id.mul ((continuous_cothRemainder 0).pow 2)) |>.add
      ((continuous_id.const_mul 5).mul (continuous_cothRemainder 1))

theorem optimalPrimitiveOne_zero : optimalPrimitiveOne 0 = 0 := by
  simp [optimalPrimitiveOne,regularCenteredCoth]

theorem optimalPrimitiveOne_eq {x : ℝ} (hx : 0 < x) :
    optimalPrimitiveOne x = -2*centeredCoth x^3/3+centeredCoth x^2/x-
      5*centeredCoth x/x^2+5/(3*x) := by
  unfold optimalPrimitiveOne
  rw [regularCenteredCoth_eq hx]
  rw [centeredCoth_eq_mul_remainder hx,cothRemainder_recurrence 0 x,cothRemainder_zero_zero]
  norm_num only
  field_simp
  ring

theorem hasDerivAt_optimalPrimitiveOne {x : ℝ} (hx : 0 < x) :
    HasDerivAt optimalPrimitiveOne
      (optimalRawIntegrandOne x-20*cothRemainder 1 x) x := by
  have hx0 := hx.ne'
  have hf := hasDerivAt_centeredCoth hx0
  have hd := ((((hf.pow 3).const_mul (-2)).div_const 3).add
    ((hf.pow 2).div (hasDerivAt_id x) hx0)).sub
      ((hf.const_mul 5).div ((hasDerivAt_id x).pow 2) (pow_ne_zero 2 hx0)) |>.add
        ((hasDerivAt_const x (5 : ℝ)).div ((hasDerivAt_id x).const_mul 3) (by positivity))
  have he : (fun y : ℝ => -2*centeredCoth y^3/3+centeredCoth y^2/y-
      5*centeredCoth y/y^2+5/(3*y)) =ᶠ[𝓝 x] optimalPrimitiveOne := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact (optimalPrimitiveOne_eq hy).symm
  have he' : HasDerivAt optimalPrimitiveOne _ x := hd.congr_of_eventuallyEq he.symm
  convert! he' using 1
  rw [optimalRawIntegrandOne_eq hx]
  simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat]
  rw [centeredCoth_eq_first_remainder hx]
  field_simp
  ring

theorem tendsto_optimalPrimitiveOne : Tendsto optimalPrimitiveOne atTop (𝓝 (-2/3)) := by
  have hf := tendsto_centeredCoth_atTop
  have hi : Tendsto (fun x : ℝ => 1/x) atTop (𝓝 0) := by simpa using tendsto_inv_atTop_zero
  have ht := (((((hf.pow 3).const_mul (-2)).div_const 3).add
    ((hf.pow 2).mul hi)).sub ((hf.const_mul 5).mul (hi.pow 2))).add
      (hi.const_mul (5/3))
  have hlim : Tendsto (fun x : ℝ => -2*centeredCoth x^3/3+centeredCoth x^2*(1/x)-
      5*centeredCoth x*(1/x)^2+(5/3)*(1/x)) atTop (𝓝 (-2/3)) := by
    convert! ht using 1
    norm_num
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [optimalPrimitiveOne_eq hx]
  ring

theorem integral_optimalRawIntegrandOne :
    (∫ x : ℝ in Ioi 0, optimalRawIntegrandOne x) =
      -2/3+20*(riemannZeta (3 : ℂ)).re/Real.pi^2 := by
  have hi := (integrableOn_cothRemainder (by decide : 0 < 1)).const_mul (20 : ℝ)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    continuous_optimalPrimitiveOne.continuousWithinAt
    (fun x hx => hasDerivAt_optimalPrimitiveOne hx)
    (integrableOn_optimalRawIntegrandOne.sub hi) tendsto_optimalPrimitiveOne
  rw [integral_sub integrableOn_optimalRawIntegrandOne hi, integral_const_mul,
    integral_cothRemainder_eq_zeta (by decide : 0 < 1),optimalPrimitiveOne_zero] at h
  norm_num only at h
  linear_combination h

end BrownianAffine
