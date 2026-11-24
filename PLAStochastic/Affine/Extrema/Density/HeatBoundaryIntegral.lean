import PLAStochastic.Brownian.Killed.OrderedBoundary.Integral
import PLAStochastic.Affine.Extrema.OrderedVector

/-! # The ordered heat-layer limits in the manuscript's five extrema coordinates -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- The affine map from extrema coordinates (low, high, low-time, high-time, endpoint)
to the six heat parameters, with horizon one and elapsed second-contact time. -/
def extremaContactParameters (p : ExtremaVector) : OrderedHeatParameters :=
  ((p.2.1-p.1, 1), (p.2.2.1, p.2.2.2.1-p.2.2.1), (-p.1, p.2.2.2.2-p.1))

theorem continuous_extremaContactParameters : Continuous extremaContactParameters := by
  unfold extremaContactParameters
  fun_prop

theorem extremaContactParameters_mem {p : ExtremaVector} (hp : p ∈ orderedExtremaDomain) :
    extremaContactParameters p ∈ orderedHeatInterior := by
  rcases hp with ⟨hl,hh,_,_,hs,hsq,hq⟩
  change 0 < p.2.1-p.1 ∧ 0 < p.2.2.1 ∧ 0 < p.2.2.2.1-p.2.2.1 ∧
    p.2.2.1+(p.2.2.2.1-p.2.2.1) < 1
  exact ⟨by linarith, hs, by linarith, by linarith⟩

/-- Pulling back uniform convergence needs only compactness of the original extrema set. -/
theorem tendstoUniformlyOn_extremaContactLayerQuotient
    {K : Set ExtremaVector} (hK : IsCompact K) (hKi : K ⊆ orderedExtremaDomain) :
    TendstoUniformlyOn (fun e p => orderedContactLayerQuotient (p.2.1-p.1) e.1 e.2 1
      p.2.2.1 (p.2.2.2.1-p.2.2.1) (-p.1) (p.2.2.2.2-p.1))
      (fun p => orderedContactDensityKernel (p.2.1-p.1) 1 p.2.2.1
        (p.2.2.2.1-p.2.2.1) (-p.1) (p.2.2.2.2-p.1))
      ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ))) K := by
  have himg : extremaContactParameters '' K ⊆ orderedHeatInterior := by
    rintro _ ⟨p,hp,rfl⟩
    exact extremaContactParameters_mem (hKi hp)
  have hu := (tendstoUniformlyOn_orderedContactLayerQuotient
    (hK.image continuous_extremaContactParameters) himg).comp extremaContactParameters
  have hsub : K ⊆ extremaContactParameters ⁻¹' (extremaContactParameters '' K) :=
    fun p hp => ⟨p,hp,rfl⟩
  simpa only [Function.comp_def, extremaContactParameters] using! hu.mono hsub

/-- Uniform compact domination is likewise inherited directly in five dimensions. -/
theorem extremaContactLayerQuotient_eventually_bounded
    {K : Set ExtremaVector} (hK : IsCompact K) (hKi : K ⊆ orderedExtremaDomain) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ e : ℝ × ℝ in ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ))),
      ∀ p ∈ K, ‖orderedContactLayerQuotient (p.2.1-p.1) e.1 e.2 1
        p.2.2.1 (p.2.2.2.1-p.2.2.1) (-p.1) (p.2.2.2.2-p.1)‖ ≤ C := by
  have himg : extremaContactParameters '' K ⊆ orderedHeatInterior := by
    rintro _ ⟨p,hp,rfl⟩
    exact extremaContactParameters_mem (hKi hp)
  obtain ⟨C,hC,hb⟩ := orderedContactLayerQuotient_eventually_bounded
    (hK.image continuous_extremaContactParameters) himg
  refine ⟨C,hC,?_⟩
  filter_upwards [hb] with e he p hp
  exact he (extremaContactParameters p) ⟨p,hp,rfl⟩

/-- The exact five-coordinate real test-integral limit, retaining the original measure. -/
theorem tendsto_integral_extremaContactLayerQuotient
    {μ : Measure ExtremaVector} [IsFiniteMeasureOnCompacts μ]
    {K : Set ExtremaVector} (hK : IsCompact K) (hKi : K ⊆ orderedExtremaDomain)
    {φ : ExtremaVector → ℝ} (hφ : ContinuousOn φ K) :
    Tendsto (fun e : ℝ × ℝ => ∫ p in K, φ p * orderedContactLayerQuotient
      (p.2.1-p.1) e.1 e.2 1 p.2.2.1 (p.2.2.2.1-p.2.2.1) (-p.1) (p.2.2.2.2-p.1) ∂μ)
      ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ)))
      (𝓝 (∫ p in K, φ p * orderedContactDensityKernel (p.2.1-p.1) 1
        p.2.2.1 (p.2.2.2.1-p.2.2.1) (-p.1) (p.2.2.2.2-p.1) ∂μ)) := by
  have : IsFiniteMeasure (μ.restrict K) := ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  obtain ⟨C,_,hC⟩ := extremaContactLayerQuotient_eventually_bounded hK hKi
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hφ
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => |M| * C)
  · exact Eventually.of_forall (fun e => (hφ.aestronglyMeasurable hK.measurableSet).mul
      ((measurable_orderedContactLayerQuotient e.1 e.2).comp
        continuous_extremaContactParameters.measurable).aestronglyMeasurable)
  · filter_upwards [hC] with e he
    filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
    rw [norm_mul]
    exact mul_le_mul ((hM p hp).trans (le_abs_self M)) (he p hp) (norm_nonneg _) (abs_nonneg M)
  · exact integrable_const _
  · filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
    exact (tendstoUniformlyOn_extremaContactLayerQuotient hK hKi |>.tendsto_at hp).const_mul (φ p)

/-- Bounded Borel tests also converge in the nonnegative-integral formulation. -/
theorem tendsto_lintegral_extremaContactLayerQuotient
    {μ : Measure ExtremaVector} [IsFiniteMeasureOnCompacts μ]
    {K : Set ExtremaVector} (hK : IsCompact K) (hKi : K ⊆ orderedExtremaDomain)
    {φ : ExtremaVector → ℝ} (hφ : Measurable φ) {M : ℝ} (hM : ∀ p ∈ K, ‖φ p‖ ≤ M) :
    Tendsto (fun e : ℝ × ℝ => ∫⁻ p in K, ENNReal.ofReal (φ p * orderedContactLayerQuotient
      (p.2.1-p.1) e.1 e.2 1 p.2.2.1 (p.2.2.2.1-p.2.2.1) (-p.1) (p.2.2.2.2-p.1)) ∂μ)
      ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ)))
      (𝓝 (∫⁻ p in K, ENNReal.ofReal (φ p * orderedContactDensityKernel (p.2.1-p.1) 1
        p.2.2.1 (p.2.2.2.1-p.2.2.1) (-p.1) (p.2.2.2.2-p.1)) ∂μ)) := by
  have : IsFiniteMeasure (μ.restrict K) := ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  obtain ⟨C,_,hC⟩ := extremaContactLayerQuotient_eventually_bounded hK hKi
  apply tendsto_lintegral_filter_of_dominated_convergence (fun _ => ENNReal.ofReal (|M| * C))
  · exact Eventually.of_forall (fun e => (hφ.mul ((measurable_orderedContactLayerQuotient e.1 e.2).comp
      continuous_extremaContactParameters.measurable)).ennreal_ofReal)
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
      ((tendstoUniformlyOn_extremaContactLayerQuotient hK hKi |>.tendsto_at hp).const_mul (φ p))

end BrownianAffine
