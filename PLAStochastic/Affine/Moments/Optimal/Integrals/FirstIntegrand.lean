import PLAStochastic.ForMathlib.Analysis.SpecialFunctions.CenteredCoth.Tail

/-! # Absolute integrability of the first actual optimal-moment integrand -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- The continuous extension used to keep the cancellation at zero explicit. -/
def regularCenteredCoth (x : ℝ) : ℝ := x*cothRemainder 0 x

theorem continuous_regularCenteredCoth : Continuous regularCenteredCoth :=
  continuous_id.mul (continuous_cothRemainder 0)

theorem regularCenteredCoth_eq {x : ℝ} (hx : 0 < x) : regularCenteredCoth x = centeredCoth x :=
  (centeredCoth_eq_mul_remainder hx).symm

/-- The first displayed optimal integrand, including its true removable value at zero. -/
def optimalRawIntegrandOne (x : ℝ) : ℝ :=
  2*regularCenteredCoth x^4-2*regularCenteredCoth x^2+
    2*(regularCenteredCoth x^2+1)*cothRemainder 0 x

theorem continuous_optimalRawIntegrandOne : Continuous optimalRawIntegrandOne := by
  unfold optimalRawIntegrandOne
  exact ((continuous_regularCenteredCoth.pow 4).const_mul 2).sub
    ((continuous_regularCenteredCoth.pow 2).const_mul 2) |>.add
      ((((continuous_regularCenteredCoth.pow 2).add_const 1).const_mul 2).mul (continuous_cothRemainder 0))

theorem optimalRawIntegrandOne_zero : optimalRawIntegrandOne 0 = 2/3 := by
  norm_num [optimalRawIntegrandOne,regularCenteredCoth,cothRemainder_zero_zero]

theorem optimalRawIntegrandOne_eq {x : ℝ} (hx : 0 < x) :
    optimalRawIntegrandOne x =
      2*centeredCoth x^4-2*centeredCoth x^2+(2*centeredCoth x^3+2*centeredCoth x)/x := by
  unfold optimalRawIntegrandOne
  rw [regularCenteredCoth_eq hx]
  have hf := centeredCoth_eq_mul_remainder hx
  field_simp
  nlinarith [hf]

private def rawOneTailPolynomial (t u : ℝ) : ℝ :=
  2*t^6*u^4-2*t+u^3*(-6*t^5+8*t^4)+u^2*(6*t^4-18*t^3+10*t^2)+
    u*(-2*t^3+12*t^2-12*t+4)+2

private theorem rawOneTailPolynomial_identity {x : ℝ} (hx : 0 < x) :
    x^2*optimalRawIntegrandOne x =
      rawOneTailPolynomial (1/x) (x^2*(centeredCoth x-1+1/x)) := by
  rw [optimalRawIntegrandOne_eq hx]
  unfold rawOneTailPolynomial
  field_simp
  ring

theorem tendsto_quadratic_optimalRawIntegrandOne :
    Tendsto (fun x : ℝ => x^2*optimalRawIntegrandOne x) atTop (𝓝 2) := by
  have hc : Continuous (fun p : ℝ × ℝ => rawOneTailPolynomial p.1 p.2) := by
    unfold rawOneTailPolynomial
    fun_prop
  have hpair : Tendsto (fun x : ℝ => (1/x,x^2*(centeredCoth x-1+1/x))) atTop (𝓝 (0,0)) := by
    simpa only [one_div] using tendsto_inv_atTop_zero.prodMk_nhds tendsto_centeredCoth_quadratic_error
  have hlim := (hc.tendsto (0,0)).comp hpair
  have ht : Tendsto (fun x : ℝ => rawOneTailPolynomial (1/x) (x^2*(centeredCoth x-1+1/x)))
      atTop (𝓝 2) := by simpa [Function.comp_def,rawOneTailPolynomial] using! hlim
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (rawOneTailPolynomial_identity hx).symm

theorem tendsto_optimalRawIntegrandOne_atTop : Tendsto optimalRawIntegrandOne atTop (𝓝 0) := by
  have h := tendsto_quadratic_optimalRawIntegrandOne.mul
    ((tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).pow 2)
  have ht : Tendsto (fun x : ℝ => (x^2*optimalRawIntegrandOne x)*(x⁻¹)^2) atTop (𝓝 0) := by simpa using! h
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  field_simp

theorem integrableOn_optimalRawIntegrandOne : IntegrableOn optimalRawIntegrandOne (Ioi 0) volume := by
  apply integrableOn_Ioi_of_quadratic_tail continuous_optimalRawIntegrandOne (L := 2)
  have h := tendsto_optimalRawIntegrandOne_atTop.add tendsto_quadratic_optimalRawIntegrandOne
  convert! h using 1
  · funext x
    ring
  · norm_num

end BrownianAffine
