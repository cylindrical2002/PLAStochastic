import PLAStochastic.Affine.Moments.Optimal.Width.SurvivalWidth
import PLAStochastic.Affine.Moments.Optimal.Width.SurvivalTonelli

/-! # The true optimal-range CDF and the unit-width survival kernel -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

def optimalSurvivalPhysicalIntegrand (r : ℝ) (p : UnitWidthCoordinates) : ℝ :=
  Real.sqrt (2 * Real.pi) / 4 * Real.exp ((p.2.2.2-p.1)^2/2) * p.2.2.1 *
    heatBoundaryLeft r p.2.1 p.1 * heatCrossBoundary r p.2.2.1 *
      heatBoundaryRight r (1-p.2.1-p.2.2.1) p.2.2.2

theorem optimalSurvivalPhysicalDensity_of_mem {r : ℝ} {p : UnitWidthCoordinates}
    (hp : (r,p) ∈ optimalMomentDomain) :
    optimalSurvivalPhysicalDensity (r,p) = ENNReal.ofReal (optimalSurvivalPhysicalIntegrand r p) := by
  rw [optimalSurvivalPhysicalDensity, indicator_of_mem hp]
  have hd : 0 < orderedExtremaDensity (optimalMomentCoordinates (r,p)) :=
    orderedExtremaDensity_pos (by rwa [← optimalMomentCoordinates_preimage_ordered] at hp)
  unfold optimalExtremaSurvivalWeight gaussianEndpointWeight
  rw [mul_one, ← ENNReal.ofReal_mul (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_nonneg _)),
    ← ENNReal.ofReal_mul hd.le]
  congr 1
  unfold orderedExtremaDensity orderedContactDensityKernel optimalMomentCoordinates
    optimalSurvivalPhysicalIntegrand
  simp only [sub_neg_eq_add, neg_neg]
  rw [show r-p.1+p.1=r by ring,
    show p.2.1+p.2.2.1-p.2.1=p.2.2.1 by ring,
    show p.2.2.2-p.1+p.1=p.2.2.2 by ring,
    abs_of_pos hp.2.2.2.2.1]
  ring

theorem optimalSurvivalWidthKernelENN_eq_physical {r : ℝ} (hr : 0 < r) :
    optimalSurvivalWidthKernelENN r =
      ∫⁻ p in fixedWidthMomentDomain r, ENNReal.ofReal (optimalSurvivalPhysicalIntegrand r p) := by
  rw [optimalSurvivalWidthKernelENN, ← lintegral_indicator (by
    unfold fixedWidthMomentDomain
    measurability : MeasurableSet (fixedWidthMomentDomain r))]
  apply lintegral_congr
  intro p
  by_cases hp : p ∈ fixedWidthMomentDomain r
  · have hp' : (r,p) ∈ optimalMomentDomain := ⟨hr,hp⟩
    rw [indicator_of_mem hp, optimalSurvivalPhysicalDensity_of_mem hp']
  · have hp' : (r,p) ∉ optimalMomentDomain := fun h => hp h.2
    simp only [indicator_of_notMem hp, optimalSurvivalPhysicalDensity, indicator_of_notMem hp']

theorem optimalSurvivalPhysicalIntegrand_width_scaling {r : ℝ} (hr : 0 < r)
    (p : UnitWidthCoordinates) :
    optimalSurvivalPhysicalIntegrand r (unitWidthScale r p) =
      (Real.sqrt (2 * Real.pi) / (4 * r ^ 5)) *
        (Real.exp ((p.2.2.2-p.1)^2/(2*(1/r^2))) *
          optimalMomentConvolutionIntegrand p.1 p.2.2.2 (1/r^2) p.2.1 p.2.2.1) := by
  have ht : 1-r^2*p.2.1-r^2*p.2.2.1 = r^2*(1/r^2-p.2.1-p.2.2.1) := by
    field_simp
  have he : (r*p.2.2.2-r*p.1)^2/2 = (p.2.2.2-p.1)^2/(2*(1/r^2)) := by
    field_simp
  simp only [optimalSurvivalPhysicalIntegrand, unitWidthScale, ht, he,
    heatBoundaryLeft_width_scaling hr.ne', heatCrossBoundary_width_scaling hr.ne',
    heatBoundaryRight_width_scaling hr.ne', optimalMomentConvolutionIntegrand]
  field_simp

/-- The complete width kernel, including the endpoint cancellation and time-gap
weight, scales to the manuscript's actual unit-width convolution. -/
theorem optimalSurvivalWidthKernelENN_eq_convolution {r : ℝ} (hr : 0 < r) :
    optimalSurvivalWidthKernelENN r = ENNReal.ofReal (Real.sqrt (2*Real.pi) * r / 4) *
      ∫⁻ a in Ioo (0 : ℝ) 1, ∫⁻ b in Ioo (0 : ℝ) 1,
        ENNReal.ofReal (Real.exp ((b-a)^2/(2*(1/r^2)))) *
          optimalMomentConvolutionENN a b (1/r^2) := by
  have hscale := setLIntegral_unitWidthScale hr
    (fun p => ENNReal.ofReal (optimalSurvivalPhysicalIntegrand r p)) (fixedWidthMomentDomain r)
  rw [unitWidthScale_preimage_domain hr] at hscale
  have he := (ENNReal.eq_div_iff (by positivity : ENNReal.ofReal (r^6) ≠ 0)
    ENNReal.ofReal_ne_top).mp hscale
  rw [optimalSurvivalWidthKernelENN_eq_physical hr, ← he]
  simp_rw [optimalSurvivalPhysicalIntegrand_width_scaling hr,
    ENNReal.ofReal_mul (by positivity : 0 ≤ Real.sqrt (2*Real.pi)/(4*r^5)),
    ENNReal.ofReal_mul (Real.exp_nonneg _)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ r^6)]
  have hc : r^6 * (Real.sqrt (2*Real.pi)/(4*r^5)) = Real.sqrt (2*Real.pi)*r/4 := by
    field_simp
  rw [hc]
  congr 1
  exact lintegral_unitWidthMomentDomain_eq_convolution
    (G := fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp ((p.2-p.1)^2/(2*(1/r^2)))))
    (by fun_prop) (1/r^2)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The survival-kernel formula follows from the true path law for almost every
width. The remaining everywhere statement requires continuity of the kernel. -/
theorem optimal_range_cdf_convolution_ae (hB : IsBrownianReal B μ) :
    ∀ᵐ r ∂(volume : Measure ℝ), 0 < r →
      μ {ω | 2 * optimalProcessError B 1 ω < r} =
        ENNReal.ofReal (Real.sqrt (2*Real.pi)*r/4) *
          ∫⁻ a in Ioo (0 : ℝ) 1, ∫⁻ b in Ioo (0 : ℝ) 1,
            ENNReal.ofReal (Real.exp ((b-a)^2/(2*(1/r^2)))) *
              optimalMomentConvolutionENN a b (1/r^2) := by
  filter_upwards [optimal_range_cdf_eq_width_ae hB] with r hr hr0
  rw [hr, optimalSurvivalWidthKernelENN_eq_convolution hr0]

end BrownianAffine
