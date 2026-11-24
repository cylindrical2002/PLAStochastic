import PLAStochastic.Affine.Moments.Optimal.Survival.Kernel.SpatialContinuity
import PLAStochastic.Affine.Moments.Optimal.Survival.Kernel.AEEq

/-! # The exact survival kernel of the unrestricted Brownian lifetime

Proposition A.2 is derived from the actual extrema law and holds at every
positive time. No survival identity or continuity assumption is supplied.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem optimal_range_cdf_eq_width (hB : IsBrownianReal B μ) {r : ℝ} (hr : 0 < r) :
    μ {ω | 2*optimalProcessError B 1 ω < r}=optimalSurvivalWidthKernelENN r := by
  apply monotone_eq_continuousAt_of_ae_eq
    (f := fun r => μ {ω | 2*optimalProcessError B 1 ω < r})
  · intro r s hrs
    exact measure_mono (fun _ hω => hω.trans_le hrs)
  · exact optimal_range_cdf_eq_width_ae hB
  · exact (continuousOn_optimalSurvivalWidthKernelENN r hr).continuousAt (Ioi_mem_nhds hr)

/-- The nonnegative form of the paper's unrestricted survival kernel, at every T>0. -/
theorem measure_optimalUnitLifetime_survival_kernel (hB : IsBrownianReal B μ)
    {T : ℝ} (hT : 0 < T) :
    μ {ω | 4*T < optimalUnitLifetime B ω}=ENNReal.ofReal
      (Real.sqrt (2*Real.pi)/(4*Real.sqrt T)*optimalSurvivalSpatialIntegral T) := by
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  rw [measure_optimalUnitLifetime_gt_scaled hB hT,
    optimal_range_cdf_eq_width hB (by positivity),optimalSurvivalWidthKernelENN_eq_spatial (by positivity)]
  have he : 1/(1/Real.sqrt T)^2=T := by
    rw [div_pow,one_pow,one_div_one_div,Real.sq_sqrt hT.le]
  rw [he]
  congr 2
  ring

/-- Proposition A.2 with the actual real probability and the literal double integral. -/
theorem measureReal_optimalUnitLifetime_survival_kernel (hB : IsBrownianReal B μ)
    {T : ℝ} (hT : 0 < T) :
    μ.real {ω | 4*T < optimalUnitLifetime B ω}=
      Real.sqrt (2*Real.pi)/(4*Real.sqrt T)*
        ∫ a in Ioo (0 : ℝ) 1, ∫ b in Ioo (0 : ℝ) 1,
          Real.exp ((b-a)^2/(2*T))*optimalMomentConvolution a b T := by
  have he := congrArg ENNReal.toReal (measure_optimalUnitLifetime_survival_kernel hB hT)
  rw [ENNReal.toReal_ofReal (mul_nonneg (by positivity) (optimalSurvivalSpatialIntegral_nonneg T)),
    optimalSurvivalSpatialIntegral_eq_iterated hT] at he
  exact he

theorem continuousAt_optimalUnitLifetime_survival (hB : IsBrownianReal B μ)
    {t : ℝ} (ht : 0 < t) :
    ContinuousAt (fun s : ℝ => μ {ω | s < optimalUnitLifetime B ω}) t := by
  have hs : 0 < Real.sqrt (t/4) := Real.sqrt_pos.mpr (by positivity)
  have hsne : Real.sqrt (t/4) ≠ 0 := hs.ne'
  have hfour : (4 : ℝ) ≠ 0 := by norm_num
  have hmap : ContinuousAt (fun s : ℝ => 1/Real.sqrt (s/4)) t := by fun_prop
  have hpos : 0 < 1/Real.sqrt (t/4) := by positivity
  have hw : ContinuousAt optimalSurvivalWidthKernelENN (1/Real.sqrt (t/4)) :=
    (continuousOn_optimalSurvivalWidthKernelENN _ hpos).continuousAt (Ioi_mem_nhds hpos)
  have hc : ContinuousAt (fun s : ℝ => optimalSurvivalWidthKernelENN (1/Real.sqrt (s/4))) t :=
    ContinuousAt.comp (f := fun s : ℝ => 1/Real.sqrt (s/4)) hw hmap
  apply hc.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  change 0 < s at hs
  have hh := measure_optimalUnitLifetime_gt_scaled hB (show 0 < s/4 by exact div_pos hs (by norm_num))
  rw [optimal_range_cdf_eq_width hB (by positivity)] at hh
  simpa only [mul_div_cancel₀ _ (by norm_num : (4 : ℝ) ≠ 0)] using hh

theorem continuousOn_optimalUnitLifetime_survival (hB : IsBrownianReal B μ) :
    ContinuousOn (fun t : ℝ => μ {ω | t < optimalUnitLifetime B ω}) (Ioi (0 : ℝ)) :=
  fun _ ht => (continuousAt_optimalUnitLifetime_survival hB ht).continuousWithinAt

theorem continuousOn_optimalUnitLifetime_survival_real (hB : IsBrownianReal B μ) :
    ContinuousOn (fun t : ℝ => μ.real {ω | t < optimalUnitLifetime B ω}) (Ioi (0 : ℝ)) := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  intro t ht
  exact (ContinuousAt.comp (f := fun s : ℝ => μ {ω | s < optimalUnitLifetime B ω})
    (ENNReal.continuousAt_toReal (measure_ne_top μ {ω | t < optimalUnitLifetime B ω}))
    (continuousAt_optimalUnitLifetime_survival hB ht)).continuousWithinAt

end BrownianAffine
