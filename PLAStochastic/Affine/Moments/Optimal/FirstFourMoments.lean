import PLAStochastic.Affine.Moments.Optimal.RawMoments
import PLAStochastic.Affine.Lifetime.Variance
import PLAStochastic.ForMathlib.Probability.Moments.FourthCentral

/-! # Exact dispersion and fourth central moment constants for the actual lifetimes -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

def optimalMeanConstant : ℝ := 40*(riemannZeta (3:ℂ)).re/Real.pi^2-4/3
def optimalSecondMomentConstant : ℝ :=
  2240*(riemannZeta (5:ℂ)).re/Real.pi^4-224*(riemannZeta (3:ℂ)).re/(3*Real.pi^2)
def optimalThirdMomentConstant : ℝ :=
  120960*(riemannZeta (7:ℂ)).re/Real.pi^6-5440*(riemannZeta (5:ℂ)).re/Real.pi^4+
    64*(riemannZeta (3:ℂ)).re/(3*Real.pi^2)
def optimalFourthMomentConstant : ℝ :=
  7096320*(riemannZeta (9:ℂ)).re/Real.pi^8-365568*(riemannZeta (7:ℂ)).re/Real.pi^6+
    3072*(riemannZeta (5:ℂ)).re/Real.pi^4
def optimalVarianceConstant : ℝ := optimalSecondMomentConstant-optimalMeanConstant^2
def optimalDispersionConstant : ℝ := optimalVarianceConstant/optimalMeanConstant^2
def optimalFourthCentralConstant : ℝ :=
  optimalFourthMomentConstant-4*optimalMeanConstant*optimalThirdMomentConstant+
    6*optimalMeanConstant^2*optimalSecondMomentConstant-3*optimalMeanConstant^4

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem optimalUnitLifetime_mean_eq_constant (hB : IsBrownianReal B μ) :
    (∫ ω,optimalUnitLifetime B ω ∂μ)=optimalMeanConstant := by
  rw [optimalUnitLifetime_first_moment hB]
  unfold optimalMeanConstant
  ring

theorem optimalUnitLifetime_second_eq_constant (hB : IsBrownianReal B μ) :
    (∫ ω,optimalUnitLifetime B ω^2 ∂μ)=optimalSecondMomentConstant :=
  optimalUnitLifetime_second_moment hB

theorem optimalUnitLifetime_third_eq_constant (hB : IsBrownianReal B μ) :
    (∫ ω,optimalUnitLifetime B ω^3 ∂μ)=optimalThirdMomentConstant :=
  optimalUnitLifetime_third_moment hB

theorem optimalUnitLifetime_fourth_eq_constant (hB : IsBrownianReal B μ) :
    (∫ ω,optimalUnitLifetime B ω^4 ∂μ)=optimalFourthMomentConstant :=
  optimalUnitLifetime_fourth_moment hB

theorem optimalUnitLifetime_variance_eq_constant (hB : IsBrownianReal B μ) :
    variance (optimalUnitLifetime B) μ=optimalVarianceConstant := by
  rw [optimalUnitLifetime_variance_eq_raw hB,optimalUnitLifetime_second_eq_constant hB,
    optimalUnitLifetime_mean_eq_constant hB]
  rfl

theorem optimalMeanConstant_pos : 0<optimalMeanConstant := by
  have hn := optimalUnitLifetime_mean_nonnegative (μ := canonicalPreBrownianMeasure) canonicalBrownian
  rw [optimalUnitLifetime_mean_eq_constant isBrownianReal_canonicalBrownian] at hn
  apply lt_of_le_of_ne hn
  intro hz
  have he : (∫ ω,optimalUnitLifetime canonicalBrownian ω ∂canonicalPreBrownianMeasure)=0 := by
    rw [optimalUnitLifetime_mean_eq_constant isBrownianReal_canonicalBrownian,hz.symm]
  have hae := (integral_eq_zero_iff_of_nonneg (optimalUnitLifetime_nonnegative canonicalBrownian)
    (optimalUnitLifetime_integrable isBrownianReal_canonicalBrownian)).mp he
  exact optimalUnitLifetime_not_ae_constant isBrownianReal_canonicalBrownian 0 hae

theorem optimalVarianceConstant_pos : 0<optimalVarianceConstant := by
  rw [←optimalUnitLifetime_variance_eq_constant isBrownianReal_canonicalBrownian]
  exact optimalUnitLifetime_variance_positive isBrownianReal_canonicalBrownian

theorem optimalDispersionConstant_pos : 0<optimalDispersionConstant :=
  div_pos optimalVarianceConstant_pos (sq_pos_of_pos optimalMeanConstant_pos)

theorem optimalMean_div_dispersion :
    optimalMeanConstant/optimalDispersionConstant=optimalMeanConstant^3/optimalVarianceConstant := by
  unfold optimalDispersionConstant
  field_simp

theorem optimalUnitLifetime_fourth_central (hB : IsBrownianReal B μ) :
    (∫ ω,(optimalUnitLifetime B ω-(∫ z,optimalUnitLifetime B z ∂μ))^4 ∂μ)=
      (∫ ω,optimalUnitLifetime B ω^4 ∂μ)-
        4*(∫ ω,optimalUnitLifetime B ω ∂μ)*(∫ ω,optimalUnitLifetime B ω^3 ∂μ)+
        6*(∫ ω,optimalUnitLifetime B ω ∂μ)^2*(∫ ω,optimalUnitLifetime B ω^2 ∂μ)-
        3*(∫ ω,optimalUnitLifetime B ω ∂μ)^4 := by
  let : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  exact integral_centered_fourth (optimalUnitLifetime_memLp hB 4 (by norm_num))

theorem anchoredUnitLifetime_fourth_central (hB : IsBrownianReal B μ) :
    (∫ ω,(anchoredUnitLifetime B ω-(∫ z,anchoredUnitLifetime B z ∂μ))^4 ∂μ)=
      (∫ ω,anchoredUnitLifetime B ω^4 ∂μ)-
        4*(∫ ω,anchoredUnitLifetime B ω ∂μ)*(∫ ω,anchoredUnitLifetime B ω^3 ∂μ)+
        6*(∫ ω,anchoredUnitLifetime B ω ∂μ)^2*(∫ ω,anchoredUnitLifetime B ω^2 ∂μ)-
        3*(∫ ω,anchoredUnitLifetime B ω ∂μ)^4 := by
  let : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  exact integral_centered_fourth (anchoredUnitLifetime_memLp hB 4 (by norm_num))

theorem optimalUnitLifetime_fourth_central_eq_constant (hB : IsBrownianReal B μ) :
    (∫ ω,(optimalUnitLifetime B ω-optimalMeanConstant)^4 ∂μ)=optimalFourthCentralConstant := by
  have h := optimalUnitLifetime_fourth_central hB
  rwa [optimalUnitLifetime_mean_eq_constant hB,optimalUnitLifetime_second_eq_constant hB,
    optimalUnitLifetime_third_eq_constant hB,optimalUnitLifetime_fourth_eq_constant hB] at h

theorem optimalUnitLifetime_absolute_third_survival_constants (hB : IsBrownianReal B μ) :
    (∫ ω,|optimalUnitLifetime B ω-optimalMeanConstant| ^ 3 ∂μ)/optimalVarianceConstant^(3/2:ℝ)=
      (optimalThirdMomentConstant-3*optimalMeanConstant*optimalSecondMomentConstant+4*optimalMeanConstant^3-
        6*(∫ t in 0..optimalMeanConstant,(optimalMeanConstant-t)^2*μ.real {ω | t<optimalUnitLifetime B ω}))/
          optimalVarianceConstant^(3/2:ℝ) := by
  have h := optimalUnitLifetime_standardized_absolute_third_survival hB
  dsimp only at h
  rwa [optimalUnitLifetime_mean_eq_constant hB,optimalUnitLifetime_variance_eq_constant hB,
    optimalUnitLifetime_second_eq_constant hB,optimalUnitLifetime_third_eq_constant hB] at h

end BrownianAffine
