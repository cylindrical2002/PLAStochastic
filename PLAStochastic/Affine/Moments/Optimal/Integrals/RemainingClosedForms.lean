import PLAStochastic.Affine.Moments.Optimal.Integrals.RemainingIntegrands
import PLAStochastic.Affine.Moments.Optimal.Integrals.FirstClosedForm

/-! # Exact real evaluations of the remaining optimal integrands -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8000
set_option maxHeartbeats 1600000

def optimalPrimitiveTwo (x : ℝ) : ℝ :=
  ((-2*((cothRemainder 0 x)^4)*(x^3)) + (2*x*((cothRemainder 0 x)^2)) + ((-10/3)*((cothRemainder 1 x)^2)*(x^3)) + ((-2/3)*x*((cothRemainder 0 x)^3)) + ((38/9)*(cothRemainder 1 x)*x) + ((70/3)*(cothRemainder 2 x)*x))

theorem continuous_optimalPrimitiveTwo : Continuous optimalPrimitiveTwo := by
  unfold optimalPrimitiveTwo
  have h0 := continuous_cothRemainder 0
  have h1 := continuous_cothRemainder 1
  have h2 := continuous_cothRemainder 2
  fun_prop

theorem optimalPrimitiveTwo_zero : optimalPrimitiveTwo 0 = 0 := by
  simp [optimalPrimitiveTwo]

theorem optimalPrimitiveTwo_eq {x : ℝ} (hx : 0 < x) :
    optimalPrimitiveTwo x = (((-70/9)*(1/x^3)) + ((14/9)*(1/x^1)) + (-2*centeredCoth x*(1/x^2)) + (-2*(centeredCoth x^4)*(1/x^1)) + (2*(centeredCoth x^2)*(1/x^1)) + ((-10/3)*(centeredCoth x^2)*(1/x^3)) + ((-2/3)*(centeredCoth x^3)*(1/x^2)) + ((70/3)*centeredCoth x*(1/x^4))) := by
  unfold optimalPrimitiveTwo
  rw [centeredCoth_eq_mul_remainder hx]
  rw [cothRemainder_recurrence 0 x,cothRemainder_zero_zero]
  norm_num only
  rw [cothRemainder_recurrence 1 x,cothRemainder_one_zero]
  norm_num only
  field_simp
  ring

theorem hasDerivAt_optimalPrimitiveTwo {x : ℝ} (hx : 0 < x) :
    HasDerivAt optimalPrimitiveTwo
      (optimalRawIntegrandTwo x-((140*(cothRemainder 2 x)) + ((-14/3)*(cothRemainder 1 x)))) x := by
  have hx0 := hx.ne'
  have hf := hasDerivAt_centeredCoth hx0
  have hd := (((((((((hasDerivAt_const x ((-70/9) : ℝ)).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 3) (pow_ne_zero 3 hx0))).add ((hasDerivAt_const x ((14/9) : ℝ)).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 1) (pow_ne_zero 1 hx0)))).add (((hasDerivAt_const x (-2 : ℝ)).mul hf).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 2) (pow_ne_zero 2 hx0)))).add (((hasDerivAt_const x (-2 : ℝ)).mul (hf.pow 4)).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 1) (pow_ne_zero 1 hx0)))).add (((hasDerivAt_const x (2 : ℝ)).mul (hf.pow 2)).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 1) (pow_ne_zero 1 hx0)))).add (((hasDerivAt_const x ((-10/3) : ℝ)).mul (hf.pow 2)).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 3) (pow_ne_zero 3 hx0)))).add (((hasDerivAt_const x ((-2/3) : ℝ)).mul (hf.pow 3)).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 2) (pow_ne_zero 2 hx0)))).add (((hasDerivAt_const x ((70/3) : ℝ)).mul hf).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 4) (pow_ne_zero 4 hx0))))
  have he : (fun x : ℝ => (((-70/9)*(1/x^3)) + ((14/9)*(1/x^1)) + (-2*centeredCoth x*(1/x^2)) + (-2*(centeredCoth x^4)*(1/x^1)) + (2*(centeredCoth x^2)*(1/x^1)) + ((-10/3)*(centeredCoth x^2)*(1/x^3)) + ((-2/3)*(centeredCoth x^3)*(1/x^2)) + ((70/3)*centeredCoth x*(1/x^4)))) =ᶠ[𝓝 x] optimalPrimitiveTwo := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact (optimalPrimitiveTwo_eq hy).symm
  have he' : HasDerivAt optimalPrimitiveTwo _ x := hd.congr_of_eventuallyEq he.symm
  convert! he' using 1
  rw [optimalRawIntegrandTwo_eq hx]
  simp only [Pi.pow_apply,Pi.div_apply,Pi.mul_apply,id_eq,Nat.cast_ofNat]
  rw [centeredCoth_eq_mul_remainder hx]
  rw [cothRemainder_recurrence 0 x,cothRemainder_zero_zero]
  norm_num only
  rw [cothRemainder_recurrence 1 x,cothRemainder_one_zero]
  norm_num only
  field_simp
  ring

theorem tendsto_optimalPrimitiveTwo : Tendsto optimalPrimitiveTwo atTop (𝓝 0) := by
  have hf := tendsto_centeredCoth_atTop
  have hi : Tendsto (fun x : ℝ => 1/x) atTop (𝓝 0) := by simpa using tendsto_inv_atTop_zero
  have ht := (((((((((tendsto_const_nhds (x := ((-70/9) : ℝ))).mul (hi.pow 3)).add ((tendsto_const_nhds (x := ((14/9) : ℝ))).mul (hi.pow 1))).add (((tendsto_const_nhds (x := (-2 : ℝ))).mul hf).mul (hi.pow 2))).add (((tendsto_const_nhds (x := (-2 : ℝ))).mul (hf.pow 4)).mul (hi.pow 1))).add (((tendsto_const_nhds (x := (2 : ℝ))).mul (hf.pow 2)).mul (hi.pow 1))).add (((tendsto_const_nhds (x := ((-10/3) : ℝ))).mul (hf.pow 2)).mul (hi.pow 3))).add (((tendsto_const_nhds (x := ((-2/3) : ℝ))).mul (hf.pow 3)).mul (hi.pow 2))).add (((tendsto_const_nhds (x := ((70/3) : ℝ))).mul hf).mul (hi.pow 4)))
  have hlim : Tendsto (fun x : ℝ => (((-70/9)*(1/x^3)) + ((14/9)*(1/x^1)) + (-2*centeredCoth x*(1/x^2)) + (-2*(centeredCoth x^4)*(1/x^1)) + (2*(centeredCoth x^2)*(1/x^1)) + ((-10/3)*(centeredCoth x^2)*(1/x^3)) + ((-2/3)*(centeredCoth x^3)*(1/x^2)) + ((70/3)*centeredCoth x*(1/x^4)))) atTop (𝓝 0) := by
    simpa [div_pow] using! ht
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (optimalPrimitiveTwo_eq hx).symm

theorem integral_optimalRawIntegrandTwo :
    (∫ x : ℝ in Ioi 0, optimalRawIntegrandTwo x) =
      (-14/3)*(riemannZeta (3 : ℂ)).re/Real.pi^2 + 140*(riemannZeta (5 : ℂ)).re/Real.pi^4 := by
  have hi1 := (integrableOn_cothRemainder (by decide : 0 < 1)).const_mul ((-14/3) : ℝ)
  have hi2 := (integrableOn_cothRemainder (by decide : 0 < 2)).const_mul (140 : ℝ)
  have hi : IntegrableOn (fun x : ℝ => ((140*(cothRemainder 2 x)) + ((-14/3)*(cothRemainder 1 x)))) (Ioi 0) volume := (hi2.add hi1)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    continuous_optimalPrimitiveTwo.continuousWithinAt
    (fun x hx => hasDerivAt_optimalPrimitiveTwo hx)
    (integrableOn_optimalRawIntegrandTwo.sub hi) tendsto_optimalPrimitiveTwo
  rw [integral_sub integrableOn_optimalRawIntegrandTwo hi,optimalPrimitiveTwo_zero] at h
  have hadd2 := integral_add hi2 hi1
  rw [hadd2] at h
  simp only [integral_const_mul] at h
  rw [integral_cothRemainder_eq_zeta (by decide : 0 < 1)] at h
  rw [integral_cothRemainder_eq_zeta (by decide : 0 < 2)] at h
  norm_num only at h
  linear_combination h

def optimalPrimitiveThree (x : ℝ) : ℝ :=
  ((-16*x*((cothRemainder 0 x)^4)) + (-8*((cothRemainder 0 x)^5)*(x^3)) + (13*((cothRemainder 1 x)^3)*(x^5)) + ((-115/18)*((cothRemainder 1 x)^2)*(x^3)) + ((35/2)*x*((cothRemainder 1 x)^2)) + ((55/18)*(cothRemainder 2 x)*x) + ((106/27)*(cothRemainder 1 x)*x) + ((107/9)*x*((cothRemainder 0 x)^3)) + ((315/2)*(cothRemainder 3 x)*x))

theorem continuous_optimalPrimitiveThree : Continuous optimalPrimitiveThree := by
  unfold optimalPrimitiveThree
  have h0 := continuous_cothRemainder 0
  have h1 := continuous_cothRemainder 1
  have h2 := continuous_cothRemainder 2
  have h3 := continuous_cothRemainder 3
  fun_prop

theorem optimalPrimitiveThree_zero : optimalPrimitiveThree 0 = 0 := by
  simp [optimalPrimitiveThree]

theorem optimalPrimitiveThree_eq {x : ℝ} (hx : 0 < x) :
    optimalPrimitiveThree x = (((-139/54)*(1/x^3)) + ((40/27)*(1/x^1)) + ((105/2)*(1/x^5)) + (-16*(centeredCoth x^4)*(1/x^3)) + (-13*(centeredCoth x^3)*(1/x^4)) + (-8*(centeredCoth x^5)*(1/x^2)) + (-4*centeredCoth x*(1/x^2)) + ((-315/2)*centeredCoth x*(1/x^6)) + ((-155/18)*centeredCoth x*(1/x^4)) + ((35/2)*(centeredCoth x^2)*(1/x^5)) + ((107/9)*(centeredCoth x^3)*(1/x^2)) + ((119/18)*(centeredCoth x^2)*(1/x^3))) := by
  unfold optimalPrimitiveThree
  rw [centeredCoth_eq_mul_remainder hx]
  rw [cothRemainder_recurrence 0 x,cothRemainder_zero_zero]
  norm_num only
  rw [cothRemainder_recurrence 1 x,cothRemainder_one_zero]
  norm_num only
  rw [cothRemainder_recurrence 2 x,cothRemainder_two_zero]
  norm_num only
  field_simp
  ring

theorem hasDerivAt_optimalPrimitiveThree {x : ℝ} (hx : 0 < x) :
    HasDerivAt optimalPrimitiveThree
      (optimalRawIntegrandThree x-((1260*(cothRemainder 3 x)) + ((-170/3)*(cothRemainder 2 x)) + ((2/9)*(cothRemainder 1 x)))) x := by
  have hx0 := hx.ne'
  have hf := hasDerivAt_centeredCoth hx0
  have hd := (((((((((((((hasDerivAt_const x ((-139/54) : ℝ)).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 3) (pow_ne_zero 3 hx0))).add ((hasDerivAt_const x ((40/27) : ℝ)).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 1) (pow_ne_zero 1 hx0)))).add ((hasDerivAt_const x ((105/2) : ℝ)).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 5) (pow_ne_zero 5 hx0)))).add (((hasDerivAt_const x (-16 : ℝ)).mul (hf.pow 4)).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 3) (pow_ne_zero 3 hx0)))).add (((hasDerivAt_const x (-13 : ℝ)).mul (hf.pow 3)).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 4) (pow_ne_zero 4 hx0)))).add (((hasDerivAt_const x (-8 : ℝ)).mul (hf.pow 5)).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 2) (pow_ne_zero 2 hx0)))).add (((hasDerivAt_const x (-4 : ℝ)).mul hf).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 2) (pow_ne_zero 2 hx0)))).add (((hasDerivAt_const x ((-315/2) : ℝ)).mul hf).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 6) (pow_ne_zero 6 hx0)))).add (((hasDerivAt_const x ((-155/18) : ℝ)).mul hf).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 4) (pow_ne_zero 4 hx0)))).add (((hasDerivAt_const x ((35/2) : ℝ)).mul (hf.pow 2)).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 5) (pow_ne_zero 5 hx0)))).add (((hasDerivAt_const x ((107/9) : ℝ)).mul (hf.pow 3)).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 2) (pow_ne_zero 2 hx0)))).add (((hasDerivAt_const x ((119/18) : ℝ)).mul (hf.pow 2)).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 3) (pow_ne_zero 3 hx0))))
  have he : (fun x : ℝ => (((-139/54)*(1/x^3)) + ((40/27)*(1/x^1)) + ((105/2)*(1/x^5)) + (-16*(centeredCoth x^4)*(1/x^3)) + (-13*(centeredCoth x^3)*(1/x^4)) + (-8*(centeredCoth x^5)*(1/x^2)) + (-4*centeredCoth x*(1/x^2)) + ((-315/2)*centeredCoth x*(1/x^6)) + ((-155/18)*centeredCoth x*(1/x^4)) + ((35/2)*(centeredCoth x^2)*(1/x^5)) + ((107/9)*(centeredCoth x^3)*(1/x^2)) + ((119/18)*(centeredCoth x^2)*(1/x^3)))) =ᶠ[𝓝 x] optimalPrimitiveThree := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact (optimalPrimitiveThree_eq hy).symm
  have he' : HasDerivAt optimalPrimitiveThree _ x := hd.congr_of_eventuallyEq he.symm
  convert! he' using 1
  rw [optimalRawIntegrandThree_eq hx]
  simp only [Pi.pow_apply,Pi.div_apply,Pi.mul_apply,id_eq,Nat.cast_ofNat]
  rw [centeredCoth_eq_mul_remainder hx]
  rw [cothRemainder_recurrence 0 x,cothRemainder_zero_zero]
  norm_num only
  rw [cothRemainder_recurrence 1 x,cothRemainder_one_zero]
  norm_num only
  rw [cothRemainder_recurrence 2 x,cothRemainder_two_zero]
  norm_num only
  field_simp
  ring

theorem tendsto_optimalPrimitiveThree : Tendsto optimalPrimitiveThree atTop (𝓝 0) := by
  have hf := tendsto_centeredCoth_atTop
  have hi : Tendsto (fun x : ℝ => 1/x) atTop (𝓝 0) := by simpa using tendsto_inv_atTop_zero
  have ht := (((((((((((((tendsto_const_nhds (x := ((-139/54) : ℝ))).mul (hi.pow 3)).add ((tendsto_const_nhds (x := ((40/27) : ℝ))).mul (hi.pow 1))).add ((tendsto_const_nhds (x := ((105/2) : ℝ))).mul (hi.pow 5))).add (((tendsto_const_nhds (x := (-16 : ℝ))).mul (hf.pow 4)).mul (hi.pow 3))).add (((tendsto_const_nhds (x := (-13 : ℝ))).mul (hf.pow 3)).mul (hi.pow 4))).add (((tendsto_const_nhds (x := (-8 : ℝ))).mul (hf.pow 5)).mul (hi.pow 2))).add (((tendsto_const_nhds (x := (-4 : ℝ))).mul hf).mul (hi.pow 2))).add (((tendsto_const_nhds (x := ((-315/2) : ℝ))).mul hf).mul (hi.pow 6))).add (((tendsto_const_nhds (x := ((-155/18) : ℝ))).mul hf).mul (hi.pow 4))).add (((tendsto_const_nhds (x := ((35/2) : ℝ))).mul (hf.pow 2)).mul (hi.pow 5))).add (((tendsto_const_nhds (x := ((107/9) : ℝ))).mul (hf.pow 3)).mul (hi.pow 2))).add (((tendsto_const_nhds (x := ((119/18) : ℝ))).mul (hf.pow 2)).mul (hi.pow 3)))
  have hlim : Tendsto (fun x : ℝ => (((-139/54)*(1/x^3)) + ((40/27)*(1/x^1)) + ((105/2)*(1/x^5)) + (-16*(centeredCoth x^4)*(1/x^3)) + (-13*(centeredCoth x^3)*(1/x^4)) + (-8*(centeredCoth x^5)*(1/x^2)) + (-4*centeredCoth x*(1/x^2)) + ((-315/2)*centeredCoth x*(1/x^6)) + ((-155/18)*centeredCoth x*(1/x^4)) + ((35/2)*(centeredCoth x^2)*(1/x^5)) + ((107/9)*(centeredCoth x^3)*(1/x^2)) + ((119/18)*(centeredCoth x^2)*(1/x^3)))) atTop (𝓝 0) := by
    simpa [div_pow] using! ht
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (optimalPrimitiveThree_eq hx).symm

theorem integral_optimalRawIntegrandThree :
    (∫ x : ℝ in Ioi 0, optimalRawIntegrandThree x) =
      (2/9)*(riemannZeta (3 : ℂ)).re/Real.pi^2 + (-170/3)*(riemannZeta (5 : ℂ)).re/Real.pi^4 + 1260*(riemannZeta (7 : ℂ)).re/Real.pi^6 := by
  have hi1 := (integrableOn_cothRemainder (by decide : 0 < 1)).const_mul ((2/9) : ℝ)
  have hi2 := (integrableOn_cothRemainder (by decide : 0 < 2)).const_mul ((-170/3) : ℝ)
  have hi3 := (integrableOn_cothRemainder (by decide : 0 < 3)).const_mul (1260 : ℝ)
  have hi : IntegrableOn (fun x : ℝ => ((1260*(cothRemainder 3 x)) + ((-170/3)*(cothRemainder 2 x)) + ((2/9)*(cothRemainder 1 x)))) (Ioi 0) volume := ((hi3.add hi2).add hi1)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    continuous_optimalPrimitiveThree.continuousWithinAt
    (fun x hx => hasDerivAt_optimalPrimitiveThree hx)
    (integrableOn_optimalRawIntegrandThree.sub hi) tendsto_optimalPrimitiveThree
  rw [integral_sub integrableOn_optimalRawIntegrandThree hi,optimalPrimitiveThree_zero] at h
  have hadd3 := integral_add (hi3.add hi2) hi1
  simp only [Pi.add_apply] at hadd3
  rw [hadd3] at h
  have hadd2 := integral_add hi3 hi2
  rw [hadd2] at h
  simp only [integral_const_mul] at h
  rw [integral_cothRemainder_eq_zeta (by decide : 0 < 1)] at h
  rw [integral_cothRemainder_eq_zeta (by decide : 0 < 2)] at h
  rw [integral_cothRemainder_eq_zeta (by decide : 0 < 3)] at h
  norm_num only at h
  linear_combination h

def optimalPrimitiveFour (x : ℝ) : ℝ :=
  ((-189*((cothRemainder 1 x)^4)*(x^7)) + (-144*x*((cothRemainder 0 x)^5)) + (-126*((cothRemainder 2 x)^2)*(x^3)) + (-40*((cothRemainder 0 x)^6)*(x^3)) + (-15*((cothRemainder 1 x)^2)*(x^3)) + (4*(cothRemainder 1 x)*x) + (57*((cothRemainder 1 x)^3)*(x^3)) + (75*x*((cothRemainder 0 x)^4)) + (102*((cothRemainder 1 x)^3)*(x^5)) + (1386*(cothRemainder 4 x)*x) + ((9/2)*x*((cothRemainder 1 x)^2)) + ((23/5)*(cothRemainder 2 x)*x) + ((105/2)*(cothRemainder 3 x)*x))

theorem continuous_optimalPrimitiveFour : Continuous optimalPrimitiveFour := by
  unfold optimalPrimitiveFour
  have h0 := continuous_cothRemainder 0
  have h1 := continuous_cothRemainder 1
  have h2 := continuous_cothRemainder 2
  have h3 := continuous_cothRemainder 3
  have h4 := continuous_cothRemainder 4
  fun_prop

theorem optimalPrimitiveFour_zero : optimalPrimitiveFour 0 = 0 := by
  simp [optimalPrimitiveFour]

theorem optimalPrimitiveFour_eq {x : ℝ} (hx : 0 < x) :
    optimalPrimitiveFour x = ((-462*(1/x^7)) + ((-52/45)*(1/x^3)) + ((14/9)*(1/x^1)) + ((343/10)*(1/x^5)) + (-189*(centeredCoth x^4)*(1/x^5)) + (-144*(centeredCoth x^5)*(1/x^4)) + (-126*(centeredCoth x^2)*(1/x^7)) + (-57*(centeredCoth x^3)*(1/x^6)) + (-40*(centeredCoth x^6)*(1/x^3)) + (-39*(centeredCoth x^2)*(1/x^3)) + (-23*centeredCoth x*(1/x^4)) + (75*(centeredCoth x^4)*(1/x^3)) + (150*(centeredCoth x^3)*(1/x^4)) + (1386*centeredCoth x*(1/x^8)) + ((63/2)*centeredCoth x*(1/x^6)) + ((123/2)*(centeredCoth x^2)*(1/x^5))) := by
  unfold optimalPrimitiveFour
  rw [centeredCoth_eq_mul_remainder hx]
  rw [cothRemainder_recurrence 0 x,cothRemainder_zero_zero]
  norm_num only
  rw [cothRemainder_recurrence 1 x,cothRemainder_one_zero]
  norm_num only
  rw [cothRemainder_recurrence 2 x,cothRemainder_two_zero]
  norm_num only
  rw [cothRemainder_recurrence 3 x,cothRemainder_three_zero]
  norm_num only
  field_simp
  ring

theorem hasDerivAt_optimalPrimitiveFour {x : ℝ} (hx : 0 < x) :
    HasDerivAt optimalPrimitiveFour
      (optimalRawIntegrandFour x-((-714*(cothRemainder 3 x)) + (6*(cothRemainder 2 x)) + (13860*(cothRemainder 4 x)))) x := by
  have hx0 := hx.ne'
  have hf := hasDerivAt_centeredCoth hx0
  have hd := (((((((((((((((((hasDerivAt_const x (-462 : ℝ)).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 7) (pow_ne_zero 7 hx0))).add ((hasDerivAt_const x ((-52/45) : ℝ)).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 3) (pow_ne_zero 3 hx0)))).add ((hasDerivAt_const x ((14/9) : ℝ)).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 1) (pow_ne_zero 1 hx0)))).add ((hasDerivAt_const x ((343/10) : ℝ)).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 5) (pow_ne_zero 5 hx0)))).add (((hasDerivAt_const x (-189 : ℝ)).mul (hf.pow 4)).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 5) (pow_ne_zero 5 hx0)))).add (((hasDerivAt_const x (-144 : ℝ)).mul (hf.pow 5)).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 4) (pow_ne_zero 4 hx0)))).add (((hasDerivAt_const x (-126 : ℝ)).mul (hf.pow 2)).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 7) (pow_ne_zero 7 hx0)))).add (((hasDerivAt_const x (-57 : ℝ)).mul (hf.pow 3)).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 6) (pow_ne_zero 6 hx0)))).add (((hasDerivAt_const x (-40 : ℝ)).mul (hf.pow 6)).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 3) (pow_ne_zero 3 hx0)))).add (((hasDerivAt_const x (-39 : ℝ)).mul (hf.pow 2)).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 3) (pow_ne_zero 3 hx0)))).add (((hasDerivAt_const x (-23 : ℝ)).mul hf).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 4) (pow_ne_zero 4 hx0)))).add (((hasDerivAt_const x (75 : ℝ)).mul (hf.pow 4)).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 3) (pow_ne_zero 3 hx0)))).add (((hasDerivAt_const x (150 : ℝ)).mul (hf.pow 3)).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 4) (pow_ne_zero 4 hx0)))).add (((hasDerivAt_const x (1386 : ℝ)).mul hf).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 8) (pow_ne_zero 8 hx0)))).add (((hasDerivAt_const x ((63/2) : ℝ)).mul hf).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 6) (pow_ne_zero 6 hx0)))).add (((hasDerivAt_const x ((123/2) : ℝ)).mul (hf.pow 2)).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 5) (pow_ne_zero 5 hx0))))
  have he : (fun x : ℝ => ((-462*(1/x^7)) + ((-52/45)*(1/x^3)) + ((14/9)*(1/x^1)) + ((343/10)*(1/x^5)) + (-189*(centeredCoth x^4)*(1/x^5)) + (-144*(centeredCoth x^5)*(1/x^4)) + (-126*(centeredCoth x^2)*(1/x^7)) + (-57*(centeredCoth x^3)*(1/x^6)) + (-40*(centeredCoth x^6)*(1/x^3)) + (-39*(centeredCoth x^2)*(1/x^3)) + (-23*centeredCoth x*(1/x^4)) + (75*(centeredCoth x^4)*(1/x^3)) + (150*(centeredCoth x^3)*(1/x^4)) + (1386*centeredCoth x*(1/x^8)) + ((63/2)*centeredCoth x*(1/x^6)) + ((123/2)*(centeredCoth x^2)*(1/x^5)))) =ᶠ[𝓝 x] optimalPrimitiveFour := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact (optimalPrimitiveFour_eq hy).symm
  have he' : HasDerivAt optimalPrimitiveFour _ x := hd.congr_of_eventuallyEq he.symm
  convert! he' using 1
  rw [optimalRawIntegrandFour_eq hx]
  simp only [Pi.pow_apply,Pi.div_apply,Pi.mul_apply,id_eq,Nat.cast_ofNat]
  rw [centeredCoth_eq_mul_remainder hx]
  rw [cothRemainder_recurrence 0 x,cothRemainder_zero_zero]
  norm_num only
  rw [cothRemainder_recurrence 1 x,cothRemainder_one_zero]
  norm_num only
  rw [cothRemainder_recurrence 2 x,cothRemainder_two_zero]
  norm_num only
  rw [cothRemainder_recurrence 3 x,cothRemainder_three_zero]
  norm_num only
  field_simp
  ring

theorem tendsto_optimalPrimitiveFour : Tendsto optimalPrimitiveFour atTop (𝓝 0) := by
  have hf := tendsto_centeredCoth_atTop
  have hi : Tendsto (fun x : ℝ => 1/x) atTop (𝓝 0) := by simpa using tendsto_inv_atTop_zero
  have ht := (((((((((((((((((tendsto_const_nhds (x := (-462 : ℝ))).mul (hi.pow 7)).add ((tendsto_const_nhds (x := ((-52/45) : ℝ))).mul (hi.pow 3))).add ((tendsto_const_nhds (x := ((14/9) : ℝ))).mul (hi.pow 1))).add ((tendsto_const_nhds (x := ((343/10) : ℝ))).mul (hi.pow 5))).add (((tendsto_const_nhds (x := (-189 : ℝ))).mul (hf.pow 4)).mul (hi.pow 5))).add (((tendsto_const_nhds (x := (-144 : ℝ))).mul (hf.pow 5)).mul (hi.pow 4))).add (((tendsto_const_nhds (x := (-126 : ℝ))).mul (hf.pow 2)).mul (hi.pow 7))).add (((tendsto_const_nhds (x := (-57 : ℝ))).mul (hf.pow 3)).mul (hi.pow 6))).add (((tendsto_const_nhds (x := (-40 : ℝ))).mul (hf.pow 6)).mul (hi.pow 3))).add (((tendsto_const_nhds (x := (-39 : ℝ))).mul (hf.pow 2)).mul (hi.pow 3))).add (((tendsto_const_nhds (x := (-23 : ℝ))).mul hf).mul (hi.pow 4))).add (((tendsto_const_nhds (x := (75 : ℝ))).mul (hf.pow 4)).mul (hi.pow 3))).add (((tendsto_const_nhds (x := (150 : ℝ))).mul (hf.pow 3)).mul (hi.pow 4))).add (((tendsto_const_nhds (x := (1386 : ℝ))).mul hf).mul (hi.pow 8))).add (((tendsto_const_nhds (x := ((63/2) : ℝ))).mul hf).mul (hi.pow 6))).add (((tendsto_const_nhds (x := ((123/2) : ℝ))).mul (hf.pow 2)).mul (hi.pow 5)))
  have hlim : Tendsto (fun x : ℝ => ((-462*(1/x^7)) + ((-52/45)*(1/x^3)) + ((14/9)*(1/x^1)) + ((343/10)*(1/x^5)) + (-189*(centeredCoth x^4)*(1/x^5)) + (-144*(centeredCoth x^5)*(1/x^4)) + (-126*(centeredCoth x^2)*(1/x^7)) + (-57*(centeredCoth x^3)*(1/x^6)) + (-40*(centeredCoth x^6)*(1/x^3)) + (-39*(centeredCoth x^2)*(1/x^3)) + (-23*centeredCoth x*(1/x^4)) + (75*(centeredCoth x^4)*(1/x^3)) + (150*(centeredCoth x^3)*(1/x^4)) + (1386*centeredCoth x*(1/x^8)) + ((63/2)*centeredCoth x*(1/x^6)) + ((123/2)*(centeredCoth x^2)*(1/x^5)))) atTop (𝓝 0) := by
    simpa [div_pow] using! ht
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (optimalPrimitiveFour_eq hx).symm

theorem integral_optimalRawIntegrandFour :
    (∫ x : ℝ in Ioi 0, optimalRawIntegrandFour x) =
      6*(riemannZeta (5 : ℂ)).re/Real.pi^4 + -714*(riemannZeta (7 : ℂ)).re/Real.pi^6 + 13860*(riemannZeta (9 : ℂ)).re/Real.pi^8 := by
  have hi2 := (integrableOn_cothRemainder (by decide : 0 < 2)).const_mul (6 : ℝ)
  have hi3 := (integrableOn_cothRemainder (by decide : 0 < 3)).const_mul (-714 : ℝ)
  have hi4 := (integrableOn_cothRemainder (by decide : 0 < 4)).const_mul (13860 : ℝ)
  have hi : IntegrableOn (fun x : ℝ => ((-714*(cothRemainder 3 x)) + (6*(cothRemainder 2 x)) + (13860*(cothRemainder 4 x)))) (Ioi 0) volume := ((hi3.add hi2).add hi4)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    continuous_optimalPrimitiveFour.continuousWithinAt
    (fun x hx => hasDerivAt_optimalPrimitiveFour hx)
    (integrableOn_optimalRawIntegrandFour.sub hi) tendsto_optimalPrimitiveFour
  rw [integral_sub integrableOn_optimalRawIntegrandFour hi,optimalPrimitiveFour_zero] at h
  have hadd3 := integral_add (hi3.add hi2) hi4
  simp only [Pi.add_apply] at hadd3
  rw [hadd3] at h
  have hadd2 := integral_add hi3 hi2
  rw [hadd2] at h
  simp only [integral_const_mul] at h
  rw [integral_cothRemainder_eq_zeta (by decide : 0 < 2)] at h
  rw [integral_cothRemainder_eq_zeta (by decide : 0 < 3)] at h
  rw [integral_cothRemainder_eq_zeta (by decide : 0 < 4)] at h
  norm_num only at h
  linear_combination h

end BrownianAffine
