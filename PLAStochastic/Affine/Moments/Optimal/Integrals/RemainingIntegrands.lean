import PLAStochastic.Affine.Moments.Optimal.Integrals.FirstIntegrand

/-! # The remaining actual optimal integrands and their absolute integrability -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
set_option maxHeartbeats 800000

def optimalRawIntegrandTwo (x : ℝ) : ℝ :=
  ((-10*((cothRemainder 0 x)^2)) + (-6*(cothRemainder 1 x)) + (4*(cothRemainder 0 x)) + (12*((cothRemainder 0 x)^3)) + (-12*((cothRemainder 0 x)^3)*(x^2)) + (8*((cothRemainder 0 x)^5)*(x^4)) + (20*((cothRemainder 0 x)^4)*(x^2)))

theorem continuous_optimalRawIntegrandTwo : Continuous optimalRawIntegrandTwo := by
  unfold optimalRawIntegrandTwo
  have h0 := continuous_cothRemainder 0
  have h1 := continuous_cothRemainder 1
  have h2 := continuous_cothRemainder 2
  have h3 := continuous_cothRemainder 3
  fun_prop

theorem optimalRawIntegrandTwo_zero : optimalRawIntegrandTwo 0 = (8/15) := by
  norm_num [optimalRawIntegrandTwo,cothRemainder_zero_zero,cothRemainder_one_zero,
    cothRemainder_two_zero,cothRemainder_three_zero]

theorem optimalRawIntegrandTwo_eq {x : ℝ} (hx : 0 < x) :
    optimalRawIntegrandTwo x = (((1/x^1)*((-12*(centeredCoth x^3)) + (4*centeredCoth x) + (8*(centeredCoth x^5)))) + ((1/x^3)*((6*centeredCoth x) + (12*(centeredCoth x^3)))) + ((1/x^2)*(-2 + (-10*(centeredCoth x^2)) + (20*(centeredCoth x^4))))) := by
  unfold optimalRawIntegrandTwo
  rw [centeredCoth_eq_mul_remainder hx]
  rw [cothRemainder_recurrence 0 x,cothRemainder_zero_zero]
  norm_num only
  field_simp
  ring

private def rawTwoTailPolynomial (t u : ℝ) : ℝ :=
  ((-4*(t^3)) + (2*t) + (-94*(t^4)*(u^2)) + (-80*(t^6)*(u^3)) + (-28*u*(t^2)) + (-20*(t^8)*(u^4)) + (-4*u*(t^5)) + (4*(t^6)*(u^2)) + (8*t*u) + (8*u*(t^4)) + (8*(t^9)*(u^5)) + (12*(t^7)*(u^3)) + (26*u*(t^3)) + (36*(t^5)*(u^2)) + (40*(t^7)*(u^4)) + (44*(t^3)*(u^2)) + (68*(t^5)*(u^3)))

private theorem rawTwoTailPolynomial_identity {x : ℝ} (hx : 0 < x) :
    x^2*optimalRawIntegrandTwo x =
      rawTwoTailPolynomial (1/x) (x^2*(centeredCoth x-1+1/x)) := by
  rw [optimalRawIntegrandTwo_eq hx]
  unfold rawTwoTailPolynomial
  field_simp
  ring

theorem tendsto_quadratic_optimalRawIntegrandTwo :
    Tendsto (fun x : ℝ => x^2*optimalRawIntegrandTwo x) atTop (𝓝 0) := by
  have hc : Continuous (fun p : ℝ × ℝ => rawTwoTailPolynomial p.1 p.2) := by
    unfold rawTwoTailPolynomial
    fun_prop
  have hpair : Tendsto (fun x : ℝ => (1/x,x^2*(centeredCoth x-1+1/x))) atTop (𝓝 (0,0)) := by
    simpa only [one_div] using tendsto_inv_atTop_zero.prodMk_nhds tendsto_centeredCoth_quadratic_error
  have hlim := (hc.tendsto (0,0)).comp hpair
  have ht : Tendsto (fun x : ℝ => rawTwoTailPolynomial (1/x) (x^2*(centeredCoth x-1+1/x)))
      atTop (𝓝 0) := by simpa [Function.comp_def,rawTwoTailPolynomial] using! hlim
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (rawTwoTailPolynomial_identity hx).symm

theorem tendsto_optimalRawIntegrandTwo_atTop : Tendsto optimalRawIntegrandTwo atTop (𝓝 0) := by
  have h := tendsto_quadratic_optimalRawIntegrandTwo.mul
    ((tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).pow 2)
  have ht : Tendsto (fun x : ℝ => (x^2*optimalRawIntegrandTwo x)*(x⁻¹)^2) atTop (𝓝 0) := by simpa using! h
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  field_simp

theorem integrableOn_optimalRawIntegrandTwo : IntegrableOn optimalRawIntegrandTwo (Ioi 0) volume := by
  apply integrableOn_Ioi_of_quadratic_tail continuous_optimalRawIntegrandTwo (L := 0)
  have h := tendsto_optimalRawIntegrandTwo_atTop.add tendsto_quadratic_optimalRawIntegrandTwo
  convert! h using 1
  · funext x
    ring
  · norm_num

def optimalRawIntegrandThree (x : ℝ) : ℝ :=
  ((30*(cothRemainder 2 x)) + (215*((cothRemainder 0 x)^4)) + ((-517/3)*((cothRemainder 0 x)^3)) + ((-86/9)*(cothRemainder 1 x)) + ((119/3)*((cothRemainder 0 x)^2)) + (-95*((cothRemainder 1 x)^3)*(x^4)) + (40*((cothRemainder 0 x)^6)*(x^4)) + (160*((cothRemainder 0 x)^5)*(x^2)) + ((-227/3)*((cothRemainder 0 x)^4)*(x^2)) + ((55/3)*((cothRemainder 1 x)^2)*(x^2)))

theorem continuous_optimalRawIntegrandThree : Continuous optimalRawIntegrandThree := by
  unfold optimalRawIntegrandThree
  have h0 := continuous_cothRemainder 0
  have h1 := continuous_cothRemainder 1
  have h2 := continuous_cothRemainder 2
  have h3 := continuous_cothRemainder 3
  fun_prop

theorem optimalRawIntegrandThree_zero : optimalRawIntegrandThree 0 = (167/315) := by
  norm_num [optimalRawIntegrandThree,cothRemainder_zero_zero,cothRemainder_one_zero,
    cothRemainder_two_zero,cothRemainder_three_zero]

theorem optimalRawIntegrandThree_eq {x : ℝ} (hx : 0 < x) :
    optimalRawIntegrandThree x = (((1/x^5)*((30*centeredCoth x) + (95*(centeredCoth x^3)))) + ((1/x^4)*(-10 + (215*(centeredCoth x^4)) + ((-230/3)*(centeredCoth x^2)))) + ((1/x^3)*((29*centeredCoth x) + (160*(centeredCoth x^5)) + ((-517/3)*(centeredCoth x^3)))) + ((1/x^2)*(-4 + (40*(centeredCoth x^6)) + ((-227/3)*(centeredCoth x^4)) + ((119/3)*(centeredCoth x^2))))) := by
  unfold optimalRawIntegrandThree
  rw [centeredCoth_eq_mul_remainder hx]
  rw [cothRemainder_recurrence 0 x,cothRemainder_zero_zero]
  norm_num only
  rw [cothRemainder_recurrence 1 x,cothRemainder_one_zero]
  norm_num only
  field_simp
  ring

private def rawThreeTailPolynomial (t u : ℝ) : ℝ :=
  ((-15*(t^5)) + (-5*(t^4)) + (2*(t^2)) + (4*(t^3)) + (-409*(t^5)*(u^2)) + (-400*(t^9)*(u^4)) + (-80*(t^11)*(u^5)) + (-15*u*(t^7)) + (5*(t^8)*(u^2)) + (10*u*(t^6)) + (15*(t^10)*(u^4)) + (35*(t^9)*(u^3)) + (40*(t^12)*(u^6)) + (60*(t^8)*(u^3)) + (74*u*(t^5)) + (105*(t^7)*(u^2)) + (240*(t^10)*(u^5)) + ((-2009/3)*(t^7)*(u^3)) + ((-178/3)*u*(t^3)) + ((50/3)*u*(t^2)) + ((98/3)*u*(t^4)) + ((229/3)*(t^6)*(u^2)) + ((557/3)*(t^4)*(u^2)) + ((1492/3)*(t^6)*(u^3)) + ((1573/3)*(t^8)*(u^4)))

private theorem rawThreeTailPolynomial_identity {x : ℝ} (hx : 0 < x) :
    x^2*optimalRawIntegrandThree x =
      rawThreeTailPolynomial (1/x) (x^2*(centeredCoth x-1+1/x)) := by
  rw [optimalRawIntegrandThree_eq hx]
  unfold rawThreeTailPolynomial
  field_simp
  ring

theorem tendsto_quadratic_optimalRawIntegrandThree :
    Tendsto (fun x : ℝ => x^2*optimalRawIntegrandThree x) atTop (𝓝 0) := by
  have hc : Continuous (fun p : ℝ × ℝ => rawThreeTailPolynomial p.1 p.2) := by
    unfold rawThreeTailPolynomial
    fun_prop
  have hpair : Tendsto (fun x : ℝ => (1/x,x^2*(centeredCoth x-1+1/x))) atTop (𝓝 (0,0)) := by
    simpa only [one_div] using tendsto_inv_atTop_zero.prodMk_nhds tendsto_centeredCoth_quadratic_error
  have hlim := (hc.tendsto (0,0)).comp hpair
  have ht : Tendsto (fun x : ℝ => rawThreeTailPolynomial (1/x) (x^2*(centeredCoth x-1+1/x)))
      atTop (𝓝 0) := by simpa [Function.comp_def,rawThreeTailPolynomial] using! hlim
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (rawThreeTailPolynomial_identity hx).symm

theorem tendsto_optimalRawIntegrandThree_atTop : Tendsto optimalRawIntegrandThree atTop (𝓝 0) := by
  have h := tendsto_quadratic_optimalRawIntegrandThree.mul
    ((tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).pow 2)
  have ht : Tendsto (fun x : ℝ => (x^2*optimalRawIntegrandThree x)*(x⁻¹)^2) atTop (𝓝 0) := by simpa using! h
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  field_simp

theorem integrableOn_optimalRawIntegrandThree : IntegrableOn optimalRawIntegrandThree (Ioi 0) volume := by
  apply integrableOn_Ioi_of_quadratic_tail continuous_optimalRawIntegrandThree (L := 0)
  have h := tendsto_optimalRawIntegrandThree_atTop.add tendsto_quadratic_optimalRawIntegrandThree
  convert! h using 1
  · funext x
    ring
  · norm_num

def optimalRawIntegrandFour (x : ℝ) : ℝ :=
  ((-1995*((cothRemainder 0 x)^4)) + (-210*(cothRemainder 3 x)) + (75*(cothRemainder 2 x)) + (180*((cothRemainder 1 x)^2)) + (378*((cothRemainder 0 x)^3)) + (2772*((cothRemainder 0 x)^5)) + ((-47/3)*(cothRemainder 1 x)) + (-1125*((cothRemainder 1 x)^3)*(x^4)) + (-936*((cothRemainder 1 x)^3)*(x^2)) + (-540*((cothRemainder 0 x)^5)*(x^2)) + (119*((cothRemainder 1 x)^2)*(x^2)) + (240*((cothRemainder 0 x)^7)*(x^4)) + (1320*((cothRemainder 0 x)^6)*(x^2)) + (2628*((cothRemainder 1 x)^4)*(x^6)))

theorem continuous_optimalRawIntegrandFour : Continuous optimalRawIntegrandFour := by
  unfold optimalRawIntegrandFour
  have h0 := continuous_cothRemainder 0
  have h1 := continuous_cothRemainder 1
  have h2 := continuous_cothRemainder 2
  have h3 := continuous_cothRemainder 3
  fun_prop

theorem optimalRawIntegrandFour_zero : optimalRawIntegrandFour 0 = (598/945) := by
  norm_num [optimalRawIntegrandFour,cothRemainder_zero_zero,cothRemainder_one_zero,
    cothRemainder_two_zero,cothRemainder_three_zero]

theorem optimalRawIntegrandFour_eq {x : ℝ} (hx : 0 < x) :
    optimalRawIntegrandFour x = (((1/x^7)*((210*centeredCoth x) + (936*(centeredCoth x^3)))) + ((1/x^6)*(-70 + (-756*(centeredCoth x^2)) + (2628*(centeredCoth x^4)))) + ((1/x^5)*((-2379*(centeredCoth x^3)) + (267*centeredCoth x) + (2772*(centeredCoth x^5)))) + ((1/x^4)*(-35 + (-1995*(centeredCoth x^4)) + (746*(centeredCoth x^2)) + (1320*(centeredCoth x^6)))) + ((1/x^3)*((-540*(centeredCoth x^5)) + (-78*centeredCoth x) + (240*(centeredCoth x^7)) + (378*(centeredCoth x^3))))) := by
  unfold optimalRawIntegrandFour
  rw [centeredCoth_eq_mul_remainder hx]
  rw [cothRemainder_recurrence 0 x,cothRemainder_zero_zero]
  norm_num only
  rw [cothRemainder_recurrence 1 x,cothRemainder_one_zero]
  norm_num only
  rw [cothRemainder_recurrence 2 x,cothRemainder_two_zero]
  norm_num only
  field_simp
  ring

private def rawFourTailPolynomial (t u : ℝ) : ℝ :=
  ((-84*(t^7)) + (-42*(t^6)) + (2*(t^3)) + (9*(t^5)) + (10*(t^4)) + (-4695*(t^10)*(u^4)) + (-4380*(t^8)*(u^3)) + (-2160*(t^12)*(u^5)) + (-1558*(t^6)*(u^2)) + (-879*(t^9)*(u^3)) + (-540*(t^11)*(u^4)) + (-477*(t^7)*(u^2)) + (-360*(t^14)*(u^6)) + (-116*u*(t^4)) + (-108*(t^13)*(u^5)) + (-84*u*(t^9)) + (-28*u*(t^5)) + (36*u*(t^3)) + (144*(t^11)*(u^3)) + (168*(t^12)*(u^4)) + (240*(t^15)*(u^7)) + (294*u*(t^6)) + (297*u*(t^7)) + (432*(t^9)*(u^2)) + (672*(t^10)*(u^3)) + (774*(t^5)*(u^2)) + (819*(t^8)*(u^2)) + (1680*(t^13)*(u^6)) + (3378*(t^7)*(u^3)) + (4500*(t^11)*(u^5)) + (5700*(t^9)*(u^4)))

private theorem rawFourTailPolynomial_identity {x : ℝ} (hx : 0 < x) :
    x^2*optimalRawIntegrandFour x =
      rawFourTailPolynomial (1/x) (x^2*(centeredCoth x-1+1/x)) := by
  rw [optimalRawIntegrandFour_eq hx]
  unfold rawFourTailPolynomial
  field_simp
  ring

theorem tendsto_quadratic_optimalRawIntegrandFour :
    Tendsto (fun x : ℝ => x^2*optimalRawIntegrandFour x) atTop (𝓝 0) := by
  have hc : Continuous (fun p : ℝ × ℝ => rawFourTailPolynomial p.1 p.2) := by
    unfold rawFourTailPolynomial
    fun_prop
  have hpair : Tendsto (fun x : ℝ => (1/x,x^2*(centeredCoth x-1+1/x))) atTop (𝓝 (0,0)) := by
    simpa only [one_div] using tendsto_inv_atTop_zero.prodMk_nhds tendsto_centeredCoth_quadratic_error
  have hlim := (hc.tendsto (0,0)).comp hpair
  have ht : Tendsto (fun x : ℝ => rawFourTailPolynomial (1/x) (x^2*(centeredCoth x-1+1/x)))
      atTop (𝓝 0) := by simpa [Function.comp_def,rawFourTailPolynomial] using! hlim
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (rawFourTailPolynomial_identity hx).symm

theorem tendsto_optimalRawIntegrandFour_atTop : Tendsto optimalRawIntegrandFour atTop (𝓝 0) := by
  have h := tendsto_quadratic_optimalRawIntegrandFour.mul
    ((tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).pow 2)
  have ht : Tendsto (fun x : ℝ => (x^2*optimalRawIntegrandFour x)*(x⁻¹)^2) atTop (𝓝 0) := by simpa using! h
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  field_simp

theorem integrableOn_optimalRawIntegrandFour : IntegrableOn optimalRawIntegrandFour (Ioi 0) volume := by
  apply integrableOn_Ioi_of_quadratic_tail continuous_optimalRawIntegrandFour (L := 0)
  have h := tendsto_optimalRawIntegrandFour_atTop.add tendsto_quadratic_optimalRawIntegrandFour
  convert! h using 1
  · funext x
    ring
  · norm_num

end BrownianAffine
