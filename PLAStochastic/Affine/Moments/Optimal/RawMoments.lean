import PLAStochastic.Affine.Moments.Optimal.Laplace.SpatialIntegralFormula
import PLAStochastic.Affine.Moments.Optimal.Spatial.LIntegral
import PLAStochastic.Affine.Moments.Optimal.Integrals.FirstClosedForm
import PLAStochastic.Affine.Moments.Optimal.Integrals.RemainingClosedForms

/-! # The first four actual optimal Brownian lifetime moments -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem optimalUnitLifetime_moment_1_integral (hB : IsBrownianReal B μ) :
    (∫ ω, optimalUnitLifetime B ω^1 ∂μ)=
      2*∫ k : ℝ in Ioi 0,optimalRawIntegrandOne k := by
  have h := optimalUnitLifetime_moment_eq_spatial_integral hB 0
    integrableOn_optimalRawIntegrandOne (fun _ hk => optimalRawIntegrandOne_nonneg hk) (by
      intro k hk
      rw [←lintegral_spatialLaplaceFormula0_diagonal hk]
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro b hb
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro a ha
      dsimp only [optimalMomentGaussianKernel]
      rw [optimalMomentTimeTransform_eq_spatial0 ha hb hk,
        ENNReal.ofReal_mul (Real.cosh_pos _).le,mul_comm (b-a) k])
  norm_num at h ⊢
  exact h

theorem optimalUnitLifetime_moment_2_integral (hB : IsBrownianReal B μ) :
    (∫ ω, optimalUnitLifetime B ω^2 ∂μ)=
      16*∫ k : ℝ in Ioi 0,optimalRawIntegrandTwo k := by
  have h := optimalUnitLifetime_moment_eq_spatial_integral hB 1
    integrableOn_optimalRawIntegrandTwo (fun _ hk => optimalRawIntegrandTwo_nonneg hk) (by
      intro k hk
      rw [←lintegral_spatialLaplaceFormula1_diagonal hk]
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro b hb
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro a ha
      dsimp only [optimalMomentGaussianKernel]
      rw [optimalMomentTimeTransform_eq_spatial1 ha hb hk,
        ENNReal.ofReal_mul (Real.cosh_pos _).le,mul_comm (b-a) k])
  norm_num at h ⊢
  exact h

theorem optimalUnitLifetime_moment_3_integral (hB : IsBrownianReal B μ) :
    (∫ ω, optimalUnitLifetime B ω^3 ∂μ)=
      96*∫ k : ℝ in Ioi 0,optimalRawIntegrandThree k := by
  have h := optimalUnitLifetime_moment_eq_spatial_integral hB 2
    integrableOn_optimalRawIntegrandThree (fun _ hk => optimalRawIntegrandThree_nonneg hk) (by
      intro k hk
      rw [←lintegral_spatialLaplaceFormula2_diagonal hk]
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro b hb
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro a ha
      dsimp only [optimalMomentGaussianKernel]
      rw [optimalMomentTimeTransform_eq_spatial2 ha hb hk,
        ENNReal.ofReal_mul (Real.cosh_pos _).le,mul_comm (b-a) k])
  norm_num at h ⊢
  exact h

theorem optimalUnitLifetime_moment_4_integral (hB : IsBrownianReal B μ) :
    (∫ ω, optimalUnitLifetime B ω^4 ∂μ)=
      512*∫ k : ℝ in Ioi 0,optimalRawIntegrandFour k := by
  have h := optimalUnitLifetime_moment_eq_spatial_integral hB 3
    integrableOn_optimalRawIntegrandFour (fun _ hk => optimalRawIntegrandFour_nonneg hk) (by
      intro k hk
      rw [←lintegral_spatialLaplaceFormula3_diagonal hk]
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro b hb
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro a ha
      dsimp only [optimalMomentGaussianKernel]
      rw [optimalMomentTimeTransform_eq_spatial3 ha hb hk,
        ENNReal.ofReal_mul (Real.cosh_pos _).le,mul_comm (b-a) k])
  norm_num at h ⊢
  exact h

theorem optimalUnitLifetime_first_moment (hB : IsBrownianReal B μ) :
    (∫ ω, optimalUnitLifetime B ω ∂μ)=
      -4/3+40*(riemannZeta (3:ℂ)).re/Real.pi^2 := by
  have h := optimalUnitLifetime_moment_1_integral hB
  simp only [pow_one] at h
  rw [h,integral_optimalRawIntegrandOne]
  ring

theorem optimalUnitLifetime_second_moment (hB : IsBrownianReal B μ) :
    (∫ ω, optimalUnitLifetime B ω^2 ∂μ)=
      2240*(riemannZeta (5:ℂ)).re/Real.pi^4-
        224*(riemannZeta (3:ℂ)).re/(3*Real.pi^2) := by
  rw [optimalUnitLifetime_moment_2_integral hB,integral_optimalRawIntegrandTwo]
  ring

theorem optimalUnitLifetime_third_moment (hB : IsBrownianReal B μ) :
    (∫ ω, optimalUnitLifetime B ω^3 ∂μ)=
      120960*(riemannZeta (7:ℂ)).re/Real.pi^6-
        5440*(riemannZeta (5:ℂ)).re/Real.pi^4+
          64*(riemannZeta (3:ℂ)).re/(3*Real.pi^2) := by
  rw [optimalUnitLifetime_moment_3_integral hB,integral_optimalRawIntegrandThree]
  ring

theorem optimalUnitLifetime_fourth_moment (hB : IsBrownianReal B μ) :
    (∫ ω, optimalUnitLifetime B ω^4 ∂μ)=
      7096320*(riemannZeta (9:ℂ)).re/Real.pi^8-
        365568*(riemannZeta (7:ℂ)).re/Real.pi^6+
          3072*(riemannZeta (5:ℂ)).re/Real.pi^4 := by
  rw [optimalUnitLifetime_moment_4_integral hB,integral_optimalRawIntegrandFour]
  ring

end BrownianAffine
