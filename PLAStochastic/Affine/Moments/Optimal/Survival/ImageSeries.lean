import PLAStochastic.Affine.Moments.Optimal.Survival.QImage.SpatialBridge
import PLAStochastic.Affine.Moments.Optimal.Survival.Spatial.Collection

/-! # The explicit image series is the actual optimal Brownian survival law

This closes Proposition A.3. The two limits are computed independently: one
from the true Brownian extrema law and the actual Q convolution; the other
from exact finite spatial integration and vanishing Gaussian boundaries.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem measureReal_optimalUnitLifetime_survival_of_nonpos (hB : IsBrownianReal B μ)
    {t : ℝ} (ht : t ≤ 0) : μ.real {ω | t < optimalUnitLifetime B ω}=1 := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  have he : μ {ω | t < optimalUnitLifetime B ω}=1 := by
    rw [←measure_univ (μ := μ)]
    apply measure_congr
    filter_upwards [optimalUnitLifetime_positive_ae hB] with ω hω
    apply propext
    change (t < optimalUnitLifetime B ω) ↔ True
    exact iff_true_intro (ht.trans_lt hω)
  change (μ {ω | t < optimalUnitLifetime B ω}).toReal=1
  rw [he,ENNReal.toReal_one]

theorem optimalImageSeries_eq_measureReal_pos (hB : IsBrownianReal B μ)
    {t : ℝ} (ht : 0 < t) :
    optimalImageSeries t=μ.real {ω | t < optimalUnitLifetime B ω} := by
  have hT : 0 < t/4 := by positivity
  have he := tendsto_nhds_unique (tendsto_sum_range_optimalImageSpatialMode hT)
    (hasSum_optimalImageSpatialMode_survival hB hT).tendsto_sum_nat
  simpa only [mul_div_cancel₀ _ (by norm_num : (4 : ℝ) ≠ 0)] using he

/-- The final image expansion equals the genuine survival probability for every real time. -/
theorem optimalImageSeries_eq_measureReal (hB : IsBrownianReal B μ) (t : ℝ) :
    optimalImageSeries t=μ.real {ω | t < optimalUnitLifetime B ω} := by
  by_cases ht : 0 < t
  · exact optimalImageSeries_eq_measureReal_pos hB ht
  · rw [optimalImageSeries_of_nonpos (le_of_not_gt ht),
      measureReal_optimalUnitLifetime_survival_of_nonpos hB (le_of_not_gt ht)]

end BrownianAffine
