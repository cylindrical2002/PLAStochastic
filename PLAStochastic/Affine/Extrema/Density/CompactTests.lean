import PLAStochastic.Affine.Extrema.Density.LayerIntegral

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- Exact identification against every nonnegative continuous test supported on
an interior compact set: the real Brownian ordered-extrema law has the A0-C-Ar/4
integral on this entire determining class of tests. -/
theorem lintegral_brownianOrderedExtrema_compact_test {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    {K : Set ExtremaVector} (hK : IsCompact K) (hKi : K ⊆ orderedExtremaDomain)
    {φ : ExtremaVector → ℝ} (hφ : Continuous φ) (hn : ∀ p, 0 ≤ φ p)
    (hsupp : ∀ p, p ∉ K → φ p=0) :
    (∫⁻ p, ENNReal.ofReal (φ p) ∂brownianOrderedExtremaMeasure B μ) =
      ∫⁻ p in K, ENNReal.ofReal (φ p*orderedExtremaDensity p) := by
  let E : ℕ → ℝ := fun n => 1/((n : ℝ)+1)
  have hE (n : ℕ) : 0 < E n := by dsimp [E]; positivity
  have hElim : Tendsto E atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hEr : Tendsto E atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within E hElim (Eventually.of_forall hE)
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hφ.continuousOn
  have hMa (p : ExtremaVector) : ‖φ p‖ ≤ |M| := by
    by_cases hp : p ∈ K
    · exact (hM p hp).trans (le_abs_self M)
    · rw [hsupp p hp,norm_zero]
      exact abs_nonneg M
  have hsU : ∀ p, p ∉ orderedExtremaDomain → φ p=0 :=
    fun p hp => hsupp p (fun h => hp (hKi h))
  have hp := tendsto_lintegral_levelOrderedContactTest hB hE hE hElim hElim hφ hMa
  have heq (n : ℕ) : (∫⁻ q : ℝ × ℝ, ∫⁻ ω, ENNReal.ofReal
      (orderedContactTest φ B (-q.1) (q.2-q.1) (E n) (E n) ω) ∂μ) /
        (ENNReal.ofReal (E n)*ENNReal.ofReal (E n)) =
      ∫⁻ p in K, ENNReal.ofReal (φ p*orderedExtremaLayerDensity (E n) (E n) p) := by
    rw [lintegral_levelOrderedContactTest_normalized_eq_layerDensity hB (hE n) (hE n) hφ.measurable hn hsU,
      ←lintegral_indicator hK.measurableSet]
    apply lintegral_congr
    intro p
    by_cases hp : p ∈ K
    · rw [indicator_of_mem hp]
    · rw [indicator_of_notMem hp,hsupp p hp,zero_mul,ENNReal.ofReal_zero]
  have hp' := hp.congr' (Eventually.of_forall heq)
  have ha := (tendsto_lintegral_extremaContactLayerQuotient (μ := (volume : Measure ExtremaVector))
    hK hKi hφ.measurable hM).comp (hEr.prodMk hEr)
  have ha' : Tendsto (fun n => ∫⁻ p in K, ENNReal.ofReal
      (φ p*orderedExtremaLayerDensity (E n) (E n) p)) atTop
      (𝓝 (∫⁻ p in K, ENNReal.ofReal (φ p*orderedExtremaDensity p))) := by
    simpa only [Function.comp_def,orderedExtremaLayerDensity,orderedExtremaDensity] using ha
  exact tendsto_nhds_unique hp' ha'

end BrownianAffine
