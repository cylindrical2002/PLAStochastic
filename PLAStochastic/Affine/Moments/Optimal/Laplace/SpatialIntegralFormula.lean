import PLAStochastic.Affine.Moments.Optimal.Laplace.GaussianMixing

noncomputable section
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

theorem optimalMomentGaussianCoefficient (n : ℕ) :
    (2:ℝ)^(2*((n:ℝ)+1)-2)*((n:ℝ)+1)*Real.sqrt (2*Real.pi)*Real.sqrt (2/Real.pi)=
      (2:ℝ)^(2*n+1)*((n:ℝ)+1) := by
  have hs : Real.sqrt (2*Real.pi)*Real.sqrt (2/Real.pi)=2 := by
    rw [←Real.sqrt_mul (by positivity),show (2*Real.pi)*(2/Real.pi)=(4:ℝ) by
      field_simp; ring]
    norm_num
  have he : 2*((n:ℝ)+1)-2=((2*n:ℕ):ℝ) := by push_cast; ring
  rw [he,Real.rpow_natCast,pow_succ]
  calc
    _ = (2:ℝ)^(2*n)*((n:ℝ)+1)*(Real.sqrt (2*Real.pi)*Real.sqrt (2/Real.pi)) := by ring
    _ = _ := by rw [hs]; ring

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0→Ω→ℝ}

/-- A finite explicit spatial integral evaluates an actual integer Brownian moment.
The required spatial identity will be discharged by the proved four kernels. -/
theorem optimalUnitLifetime_moment_eq_spatial_integral (hB : IsBrownianReal B μ)
    (n : ℕ) {L : ℝ→ℝ} (hLi : IntegrableOn L (Ioi 0))
    (hLn : ∀k∈Ioi (0:ℝ),0≤L k)
    (hL : ∀k∈Ioi (0:ℝ),
      (∫⁻ b : ℝ in Ioo 0 1, ∫⁻ a : ℝ in Ioo 0 1, optimalMomentGaussianKernel n (a,b,k))=
        ENNReal.ofReal (L k)) :
    (∫ ω, optimalUnitLifetime B ω^(n+1) ∂μ)=
      (2:ℝ)^(2*n+1)*((n:ℝ)+1)*∫ k : ℝ in Ioi 0,L k := by
  have he := optimalUnitLifetime_moment_gaussian_lintegral hB n
  rw [optimalMomentGaussianCoefficient] at he
  have hEn : 0≤ᵐ[volume.restrict (Ioi (0:ℝ))] L := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with k hk
    exact hLn k hk
  have hI : (∫⁻ k : ℝ in Ioi 0, ∫⁻ b : ℝ in Ioo 0 1, ∫⁻ a : ℝ in Ioo 0 1,
      optimalMomentGaussianKernel n (a,b,k))=ENNReal.ofReal (∫ k : ℝ in Ioi 0,L k) := by
    rw [ofReal_integral_eq_lintegral_ofReal hLi hEn]
    exact setLIntegral_congr_fun measurableSet_Ioi hL
  rw [hI] at he
  have hl := optimalUnitLifetime_integrable_rpow hB (by positivity : 0≤(n:ℝ)+1)
  have hn : 0≤ᵐ[μ] (fun ω => optimalUnitLifetime B ω^((n:ℝ)+1)) :=
    Eventually.of_forall fun ω => Real.rpow_nonneg (optimalUnitLifetime_nonnegative B ω) _
  have hLpos : 0≤∫ k : ℝ in Ioi 0,L k := integral_nonneg_of_ae hEn
  have ht := congrArg ENNReal.toReal he
  rw [←integral_eq_lintegral_of_nonneg_ae hn hl.aestronglyMeasurable,
    ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity),ENNReal.toReal_ofReal hLpos] at ht
  simpa only [←Nat.cast_add_one,Real.rpow_natCast] using ht

end BrownianAffine
