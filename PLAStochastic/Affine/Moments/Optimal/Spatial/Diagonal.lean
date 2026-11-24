import PLAStochastic.Affine.Moments.Optimal.Spatial.Recursion
import PLAStochastic.Affine.Moments.Optimal.Integrals.RemainingIntegrands

/-! # The actual spatial recursion gives the four displayed optimal integrands -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000

theorem sinh_eq_exp_square (x : ℝ) :
    Real.sinh x=(Real.exp x^2-1)/(2*Real.exp x) := by
  rw [Real.sinh_eq,Real.exp_neg]
  field_simp

theorem centeredCoth_eq_exp_square {x : ℝ} (hx : 0 < x) :
    centeredCoth x=(Real.exp x^2+1)/(Real.exp x^2-1)-1/x := by
  have he := (Real.exp_pos x).ne'
  have hs : Real.exp x^2-1 ≠ 0 := by have h := Real.one_lt_exp_iff.mpr hx; nlinarith
  rw [centeredCoth,sinh_eq_exp_square,Real.cosh_eq,Real.exp_neg]
  field_simp

theorem optimalSpatialFormula0_diagonal {x : ℝ} (hx : 0 < x) :
    optimalSpatialFormula0 x x=optimalRawIntegrandOne x := by
  have hx0 := hx.ne'
  have hplus : 2*x ≠ 0 := by positivity
  have hminus : -(2*x) ≠ 0 := neg_ne_zero.mpr hplus
  have hs := Real.sinh_ne_zero.mpr hx0
  have he := (Real.exp_pos x).ne'
  have hd : Real.exp x-(Real.exp x)⁻¹ ≠ 0 := by
    intro hz
    apply hs
    simp only [Real.sinh_eq,Real.exp_neg,hz,zero_div]
  rw [optimalRawIntegrandOne_eq hx]
  unfold optimalSpatialFormula0
  unfold optimalSpatialDerivative0
  unfold spatialCothFactor0 optimalSpatialWeight0
  simp only [spatialDifferenceMoment,show x+x=2*x by ring,
    show x+(-x)=0 by ring,show -x-x=-(2*x) by ring,sub_self,exponentialUnitMoment_zero]
  norm_num only
  simp only [exponentialUnitMoment_zero_index hplus,exponentialUnitMoment_zero_index hminus]
  rw [centeredCoth_eq_exp_square hx,sinh_eq_exp_square]
  simp only [Real.exp_neg,show 2*x=x+x by ring,Real.exp_add]
  have hsq : Real.exp x^2-1 ≠ 0 := by have h := Real.one_lt_exp_iff.mpr hx; nlinarith
  field_simp [hsq]
  ring

theorem optimalSpatialFormula1_diagonal {x : ℝ} (hx : 0 < x) :
    optimalSpatialFormula1 x x=optimalRawIntegrandTwo x := by
  have hx0 := hx.ne'
  have hplus : 2*x ≠ 0 := by positivity
  have hminus : -(2*x) ≠ 0 := neg_ne_zero.mpr hplus
  have hs := Real.sinh_ne_zero.mpr hx0
  have he := (Real.exp_pos x).ne'
  have hd : Real.exp x-(Real.exp x)⁻¹ ≠ 0 := by
    intro hz
    apply hs
    simp only [Real.sinh_eq,Real.exp_neg,hz,zero_div]
  rw [optimalRawIntegrandTwo_eq hx]
  unfold optimalSpatialFormula1
  unfold optimalSpatialDerivative1
  unfold spatialCothFactor0 optimalSpatialWeight0
  unfold spatialCothFactor1 optimalSpatialWeight1
  simp only [spatialDifferenceMoment,show x+x=2*x by ring,
    show x+(-x)=0 by ring,show -x-x=-(2*x) by ring,sub_self,exponentialUnitMoment_zero]
  norm_num only
  simp only [exponentialUnitMoment_recurrence 0 hplus,exponentialUnitMoment_recurrence 0 hminus]
  simp only [exponentialUnitMoment_zero_index hplus,exponentialUnitMoment_zero_index hminus]
  rw [centeredCoth_eq_exp_square hx,sinh_eq_exp_square]
  simp only [Real.exp_neg,show 2*x=x+x by ring,Real.exp_add]
  have hsq : Real.exp x^2-1 ≠ 0 := by have h := Real.one_lt_exp_iff.mpr hx; nlinarith
  field_simp [hsq]
  ring

theorem optimalSpatialFormula2_diagonal {x : ℝ} (hx : 0 < x) :
    optimalSpatialFormula2 x x=optimalRawIntegrandThree x := by
  have hx0 := hx.ne'
  have hplus : 2*x ≠ 0 := by positivity
  have hminus : -(2*x) ≠ 0 := neg_ne_zero.mpr hplus
  have hs := Real.sinh_ne_zero.mpr hx0
  have he := (Real.exp_pos x).ne'
  have hd : Real.exp x-(Real.exp x)⁻¹ ≠ 0 := by
    intro hz
    apply hs
    simp only [Real.sinh_eq,Real.exp_neg,hz,zero_div]
  rw [optimalRawIntegrandThree_eq hx]
  unfold optimalSpatialFormula2
  unfold optimalSpatialDerivative1
  unfold optimalSpatialDerivative2
  unfold spatialCothFactor0 optimalSpatialWeight0
  unfold spatialCothFactor1 optimalSpatialWeight1
  unfold spatialCothFactor2 optimalSpatialWeight2
  simp only [spatialDifferenceMoment,show x+x=2*x by ring,
    show x+(-x)=0 by ring,show -x-x=-(2*x) by ring,sub_self,exponentialUnitMoment_zero]
  norm_num only
  simp only [exponentialUnitMoment_recurrence 1 hplus,exponentialUnitMoment_recurrence 1 hminus]
  simp only [exponentialUnitMoment_recurrence 0 hplus,exponentialUnitMoment_recurrence 0 hminus]
  simp only [exponentialUnitMoment_zero_index hplus,exponentialUnitMoment_zero_index hminus]
  rw [centeredCoth_eq_exp_square hx,sinh_eq_exp_square]
  simp only [Real.exp_neg,show 2*x=x+x by ring,Real.exp_add]
  have hsq : Real.exp x^2-1 ≠ 0 := by have h := Real.one_lt_exp_iff.mpr hx; nlinarith
  field_simp [hsq]
  ring

theorem optimalSpatialFormula3_diagonal {x : ℝ} (hx : 0 < x) :
    optimalSpatialFormula3 x x=optimalRawIntegrandFour x := by
  have hx0 := hx.ne'
  have hplus : 2*x ≠ 0 := by positivity
  have hminus : -(2*x) ≠ 0 := neg_ne_zero.mpr hplus
  have hs := Real.sinh_ne_zero.mpr hx0
  have he := (Real.exp_pos x).ne'
  have hd : Real.exp x-(Real.exp x)⁻¹ ≠ 0 := by
    intro hz
    apply hs
    simp only [Real.sinh_eq,Real.exp_neg,hz,zero_div]
  rw [optimalRawIntegrandFour_eq hx]
  unfold optimalSpatialFormula3
  unfold optimalSpatialDerivative1
  unfold optimalSpatialDerivative2
  unfold optimalSpatialDerivative3
  unfold spatialCothFactor0 optimalSpatialWeight0
  unfold spatialCothFactor1 optimalSpatialWeight1
  unfold spatialCothFactor2 optimalSpatialWeight2
  unfold spatialCothFactor3 optimalSpatialWeight3
  simp only [spatialDifferenceMoment,show x+x=2*x by ring,
    show x+(-x)=0 by ring,show -x-x=-(2*x) by ring,sub_self,exponentialUnitMoment_zero]
  norm_num only
  simp only [exponentialUnitMoment_recurrence 2 hplus,exponentialUnitMoment_recurrence 2 hminus]
  simp only [exponentialUnitMoment_recurrence 1 hplus,exponentialUnitMoment_recurrence 1 hminus]
  simp only [exponentialUnitMoment_recurrence 0 hplus,exponentialUnitMoment_recurrence 0 hminus]
  simp only [exponentialUnitMoment_zero_index hplus,exponentialUnitMoment_zero_index hminus]
  rw [centeredCoth_eq_exp_square hx,sinh_eq_exp_square]
  simp only [Real.exp_neg,show 2*x=x+x by ring,Real.exp_add]
  have hsq : Real.exp x^2-1 ≠ 0 := by have h := Real.one_lt_exp_iff.mpr hx; nlinarith
  field_simp [hsq]
  ring

theorem optimalSpatialB_zero_diagonal {k : ℝ} (hk : 0 < k) :
    optimalSpatialB 0 k k=optimalRawIntegrandOne k := by
  rw [optimalSpatialB_zero,optimalSpatialFormula0_diagonal hk]

theorem optimalSpatialB_one_diagonal {k : ℝ} (hk : 0 < k) :
    optimalSpatialB 1 k k=optimalRawIntegrandTwo k := by
  rw [optimalSpatialB_one hk.ne',optimalSpatialFormula1_diagonal hk]

theorem optimalSpatialB_two_diagonal {k : ℝ} (hk : 0 < k) :
    optimalSpatialB 2 k k=optimalRawIntegrandThree k := by
  rw [optimalSpatialB_two hk.ne',optimalSpatialFormula2_diagonal hk]

theorem optimalSpatialB_three_diagonal {k : ℝ} (hk : 0 < k) :
    optimalSpatialB 3 k k=optimalRawIntegrandFour k := by
  rw [optimalSpatialB_three hk.ne',optimalSpatialFormula3_diagonal hk]

end BrownianAffine
