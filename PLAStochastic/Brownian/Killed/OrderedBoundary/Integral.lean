import PLAStochastic.Brownian.Killed.OrderedBoundary.Uniform
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Joint measurability and compact test-integral limits for ordered heat layers -/
noncomputable section
open Filter Set MeasureTheory
open scoped Topology BigOperators
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- Joint measurability is valid globally, even outside the positive-time convergence region. -/
theorem measurable_heatSpatialSeries_comp {Ω : Type*} [MeasurableSpace Ω]
    {r t x z : Ω → ℝ} (hr : Measurable r) (ht : Measurable t)
    (hx : Measurable x) (hz : Measurable z) (a b : ℕ) :
    Measurable (fun ω => heatSpatialSeries (r ω) a b (t ω) (x ω) (z ω)) := by
  apply Measurable.tsum
  intro n
  dsimp only [heatSpatialMode, heatFrequency]
  fun_prop

/-- The actual normalized double layer is a globally Borel function of its six base parameters. -/
theorem measurable_orderedContactLayerQuotient (e d : ℝ) :
    Measurable (fun p : OrderedHeatParameters =>
      orderedContactLayerQuotient p.1.1 e d p.1.2 p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2) := by
  have hA := measurable_heatSpatialSeries_comp (by fun_prop : Measurable (fun p : OrderedHeatParameters => p.1.1))
    (by fun_prop : Measurable (fun p : OrderedHeatParameters => p.2.1.1))
    (by fun_prop : Measurable (fun p : OrderedHeatParameters => p.2.2.1)) (measurable_const (a := (0 : ℝ))) 0 1
  have hC := (measurable_heatSpatialSeries_comp (by fun_prop : Measurable (fun p : OrderedHeatParameters => p.1.1+e))
    (by fun_prop : Measurable (fun p : OrderedHeatParameters => p.2.1.2))
    (measurable_const (a := e)) (by fun_prop : Measurable (fun p : OrderedHeatParameters => p.1.1+e)) 0 1).neg
  have hR := measurable_heatSpatialSeries_comp (by fun_prop : Measurable (fun p : OrderedHeatParameters => p.1.1+e+d))
    (by fun_prop : Measurable (fun p : OrderedHeatParameters => p.1.2-p.2.1.1-p.2.1.2))
    (by fun_prop : Measurable (fun p : OrderedHeatParameters => p.1.1+e))
    (by fun_prop : Measurable (fun p : OrderedHeatParameters => p.2.2.2+e)) 0 0
  exact ((hA.mul (hC.div_const e)).mul (hR.div_const d)).div_const 4

/-- All compactly restricted continuous test integrals converge to the ordered heat product. -/
theorem tendsto_integral_orderedContactLayerQuotient
    {μ : Measure OrderedHeatParameters} [IsFiniteMeasureOnCompacts μ]
    {K : Set OrderedHeatParameters} (hK : IsCompact K) (hKi : K ⊆ orderedHeatInterior)
    {φ : OrderedHeatParameters → ℝ} (hφ : ContinuousOn φ K) :
    Tendsto (fun e : ℝ × ℝ => ∫ p in K, φ p *
      orderedContactLayerQuotient p.1.1 e.1 e.2 p.1.2 p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2 ∂μ)
      ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ)))
      (𝓝 (∫ p in K, φ p *
        orderedContactDensityKernel p.1.1 p.1.2 p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2 ∂μ)) := by
  have : IsFiniteMeasure (μ.restrict K) := ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  obtain ⟨C, _, hC⟩ := orderedContactLayerQuotient_eventually_bounded hK hKi
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hφ
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => |M| * C)
  · exact Eventually.of_forall (fun e => (hφ.aestronglyMeasurable hK.measurableSet).mul
      (measurable_orderedContactLayerQuotient e.1 e.2).aestronglyMeasurable)
  · filter_upwards [hC] with e he
    filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
    rw [norm_mul]
    exact mul_le_mul ((hM p hp).trans (le_abs_self M)) (he p hp) (norm_nonneg _) (abs_nonneg M)
  · exact integrable_const _
  · filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
    exact (tendstoUniformlyOn_orderedContactLayerQuotient hK hKi |>.tendsto_at hp).const_mul (φ p)

/-- Bounded Borel tests also admit the nonnegative-integral limit used for actual measures. -/
theorem tendsto_lintegral_orderedContactLayerQuotient
    {μ : Measure OrderedHeatParameters} [IsFiniteMeasureOnCompacts μ]
    {K : Set OrderedHeatParameters} (hK : IsCompact K) (hKi : K ⊆ orderedHeatInterior)
    {φ : OrderedHeatParameters → ℝ} (hφ : Measurable φ)
    {M : ℝ} (hM : ∀ p ∈ K, ‖φ p‖ ≤ M) :
    Tendsto (fun e : ℝ × ℝ => ∫⁻ p in K, ENNReal.ofReal (φ p *
      orderedContactLayerQuotient p.1.1 e.1 e.2 p.1.2 p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2) ∂μ)
      ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ)))
      (𝓝 (∫⁻ p in K, ENNReal.ofReal (φ p *
        orderedContactDensityKernel p.1.1 p.1.2 p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2) ∂μ)) := by
  have : IsFiniteMeasure (μ.restrict K) := ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  obtain ⟨C, _, hC⟩ := orderedContactLayerQuotient_eventually_bounded hK hKi
  apply tendsto_lintegral_filter_of_dominated_convergence (fun _ => ENNReal.ofReal (|M| * C))
  · exact Eventually.of_forall (fun e => (hφ.mul (measurable_orderedContactLayerQuotient e.1 e.2)).ennreal_ofReal)
  · filter_upwards [hC] with e he
    filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
    apply ENNReal.ofReal_le_ofReal
    apply le_trans (le_abs_self _)
    rw [← Real.norm_eq_abs, norm_mul]
    exact mul_le_mul ((hM p hp).trans (le_abs_self M)) (he p hp) (norm_nonneg _) (abs_nonneg M)
  · rw [lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  · filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((tendstoUniformlyOn_orderedContactLayerQuotient hK hKi |>.tendsto_at hp).const_mul (φ p))

end BrownianAffine
