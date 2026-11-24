import PLAStochastic.Affine.Moments.Optimal.Width.SurvivalScaling
import PLAStochastic.Affine.Moments.Optimal.Width.InverseWidth
import PLAStochastic.Affine.Moments.Optimal.Laplace.LaplaceReal

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- The endpoint-weighted unit-width spatial integral of the actual convolution. -/
def optimalMomentSpatialConvolutionENN (T : ℝ) : ℝ≥0∞ :=
  ∫⁻ a in Ioo (0:ℝ) 1, ∫⁻ b in Ioo (0:ℝ) 1,
    ENNReal.ofReal (Real.exp ((b-a)^2/(2*T)))*optimalMomentConvolutionENN a b T

private def inverseRangeMomentTest (q : ℝ) : ℝ→ℝ≥0∞ :=
  (Ioi 0).indicator (fun r => ENNReal.ofReal (r^(-(2*q+1))))

private theorem measurable_inverseRangeMomentTest (q : ℝ) : Measurable (inverseRangeMomentTest q) :=
  (by fun_prop : Measurable (fun r : ℝ => ENNReal.ofReal (r^(-(2*q+1))))).indicator measurableSet_Ioi

private theorem slopeCoareaTest_inverseRangeMoment {q : ℝ} (hq : 0<q) (g : Path 1) :
    slopeCoareaTest (inverseRangeMomentTest q) g=slopeWeightENNReal q g := by
  by_cases hr : 0<slopeRange g 0
  · unfold slopeCoareaTest inverseRangeMomentTest slopeWeightENNReal slopeWeight
    rw [indicator_of_mem (show slopeRange g 0∈Ioi (0:ℝ) from hr),
      ←ENNReal.ofReal_mul (abs_nonneg _),Real.rpow_neg hr.le,div_eq_mul_inv]
  · have hz : slopeRange g 0=0 := le_antisymm (le_of_not_gt hr) (slopeRange_nonnegative g 0)
    unfold slopeCoareaTest inverseRangeMomentTest slopeWeightENNReal slopeWeight
    simp only [hz,indicator_of_notMem (show (0:ℝ)∉Ioi (0:ℝ) by simp),mul_zero,
      Real.zero_rpow (show 2*q+1≠0 by linarith),div_zero,ENNReal.ofReal_zero]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- All positive real optimal moments are derived from the actual width kernel. -/
theorem optimalUnitLifetime_moment_width_lintegral (hB : IsBrownianReal B μ)
    {q : ℝ} (hq : 0<q) :
    (∫⁻ ω, ENNReal.ofReal (optimalUnitLifetime B ω^q) ∂μ)=
      ENNReal.ofReal ((2:ℝ)^(2*q)*q)*2*
        ∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (r^(-(2*q+1)))*optimalSurvivalWidthKernelENN r := by
  have he := (identDistrib_optimalUnitLifetime_rpow_error hB q).comp
    (show Measurable ENNReal.ofReal from ENNReal.measurable_ofReal)
  have hel : (∫⁻ ω, ENNReal.ofReal (optimalUnitLifetime B ω^q) ∂μ)=
      ∫⁻ ω, ENNReal.ofReal (optimalProcessError B 1 ω^(-2*q)) ∂μ := by
    simpa only [Function.comp_apply] using he.lintegral_eq
  rw [hel,optimal_inverse_error_lintegral_slopeWeight hB hq]
  have hc := brownian_coarea_test_lintegral hB (measurable_inverseRangeMomentTest q)
  simp only [slopeCoareaTest_inverseRangeMoment hq] at hc
  rw [←hc,optimal_range_cdf_test_width hB (measurable_inverseRangeMomentTest q)]
  have hpoint (r : ℝ) : inverseRangeMomentTest q r*optimalSurvivalWidthKernelENN r=
      (Ioi 0).indicator (fun r => ENNReal.ofReal (r^(-(2*q+1)))*optimalSurvivalWidthKernelENN r) r := by
    by_cases hr : r∈Ioi (0:ℝ) <;> simp [inverseRangeMomentTest,hr]
  simp only [hpoint,lintegral_indicator measurableSet_Ioi,mul_assoc]

/-- Unit-width conversion of the true width-kernel moment, including its exact constant. -/
theorem lintegral_optimalSurvivalWidthKernel_moment (q : ℝ) :
    (∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (r^(-(2*q+1)))*optimalSurvivalWidthKernelENN r)=
      ENNReal.ofReal (Real.sqrt (2*Real.pi)/8)*
        ∫⁻ T in Ioi (0:ℝ), ENNReal.ofReal (T^(q-3/2))*optimalMomentSpatialConvolutionENN T := by
  have he : (∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (r^(-(2*q+1)))*optimalSurvivalWidthKernelENN r)=
      ENNReal.ofReal (Real.sqrt (2*Real.pi)/4)*
        ∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (r^(-2*q))*optimalMomentSpatialConvolutionENN (1/r^2) := by
    rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp only
    rw [optimalSurvivalWidthKernelENN_eq_convolution hr,←mul_assoc,
      ←ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _)]
    have hp : r^(-(2*q+1))*r=r^(-2*q) := by
      rw [←Real.rpow_add_one hr.ne',show -(2*q+1)+1=-2*q by ring]
    have hc : r^(-(2*q+1))*(Real.sqrt (2*Real.pi)*r/4)=
        (Real.sqrt (2*Real.pi)/4)*r^(-2*q) := by
      calc
        _ = (Real.sqrt (2*Real.pi)/4)*(r^(-(2*q+1))*r) := by ring
        _ = _ := by rw [hp]
    rw [hc,ENNReal.ofReal_mul (by positivity),mul_assoc]
    rfl
  rw [he,lintegral_inverseSquare_moment_weight]
  have hc : ENNReal.ofReal (Real.sqrt (2*Real.pi)/4)*(1/2:ℝ≥0∞)=
      ENNReal.ofReal (Real.sqrt (2*Real.pi)/8) := by
    have hh : ENNReal.ofReal (1/2:ℝ)=(1/2:ℝ≥0∞) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2)]
      norm_num
    rw [←hh,←ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  rw [←mul_assoc,hc]

/-- The complete positive-real-order unit-width formula is tied to the actual
optimal Brownian lifetime, with the convolution obtained from the true extrema law. -/
theorem optimalUnitLifetime_moment_unitWidth_lintegral (hB : IsBrownianReal B μ)
    {q : ℝ} (hq : 0<q) :
    (∫⁻ ω, ENNReal.ofReal (optimalUnitLifetime B ω^q) ∂μ)=
      ENNReal.ofReal ((2:ℝ)^(2*q-2)*q*Real.sqrt (2*Real.pi))*
        ∫⁻ T in Ioi (0:ℝ), ENNReal.ofReal (T^(q-3/2))*optimalMomentSpatialConvolutionENN T := by
  rw [optimalUnitLifetime_moment_width_lintegral hB hq,lintegral_optimalSurvivalWidthKernel_moment]
  rw [←mul_assoc,←ENNReal.ofReal_ofNat (2:ℕ),←ENNReal.ofReal_mul (by positivity),
    ←ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [Real.rpow_sub (by norm_num : (0:ℝ)<2),Real.rpow_two]
  ring

end BrownianAffine
