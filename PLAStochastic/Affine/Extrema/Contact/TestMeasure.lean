import PLAStochastic.Affine.Extrema.Contact.Averaging

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open MeasureTheory.Measure
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The order-only test agrees almost surely with restriction of the actual
five-variable law to its full lower-first interior domain. -/
theorem orderedExtremaTest_eq_indicator_ae (hB : IsBrownianReal B μ) (φ : ExtremaVector → ℝ) :
    (fun ω => orderedExtremaTest φ B ω) =ᵐ[μ]
      (fun ω => orderedExtremaDomain.indicator φ (brownianExtremaVector B ω)) := by
  filter_upwards [brownianExtremaVector_ordered_support_ae hB] with ω hs
  rcases hs with hs | hs
  · have ho : (lowerTime (unitPath (processPath B ω) 1) 0 : ℝ) <
        (upperTime (unitPath (processPath B ω) 1) 0 : ℝ) := hs.2.2.2.2.2.1
    rw [indicator_of_mem hs,orderedExtremaTest,if_pos ho]
  · have ho : ¬ (lowerTime (unitPath (processPath B ω) 1) 0 : ℝ) <
        (upperTime (unitPath (processPath B ω) 1) 0 : ℝ) := not_lt_of_gt hs.2.2.2.2.2.1
    have hn : brownianExtremaVector B ω ∉ orderedExtremaDomain := fun h => ho h.2.2.2.2.2.1
    rw [indicator_of_notMem hn,orderedExtremaTest,if_neg ho]

theorem integral_orderedExtremaTest_eq_measure (hB : IsBrownianReal B μ)
    {φ : ExtremaVector → ℝ} (hφ : Measurable φ) :
    (∫ ω, orderedExtremaTest φ B ω ∂μ) = ∫ p, φ p ∂brownianOrderedExtremaMeasure B μ := by
  symm
  change (∫ p in orderedExtremaDomain,φ p ∂μ.map (brownianExtremaVector B))=_
  rw [←integral_indicator measurableSet_orderedExtremaDomain,
    integral_map (aemeasurable_brownianExtremaVector hB)
      (hφ.indicator measurableSet_orderedExtremaDomain).aestronglyMeasurable]
  exact integral_congr_ae (orderedExtremaTest_eq_indicator_ae hB φ).symm

theorem lintegral_orderedExtremaTest_eq_measure (hB : IsBrownianReal B μ)
    {φ : ExtremaVector → ℝ} (hφ : Measurable φ) :
    (∫⁻ ω, ENNReal.ofReal (orderedExtremaTest φ B ω) ∂μ) =
      ∫⁻ p, ENNReal.ofReal (φ p) ∂brownianOrderedExtremaMeasure B μ := by
  symm
  change (∫⁻ p in orderedExtremaDomain,ENNReal.ofReal (φ p) ∂μ.map (brownianExtremaVector B))=_
  rw [←lintegral_indicator measurableSet_orderedExtremaDomain,
    lintegral_map' (hφ.ennreal_ofReal.indicator measurableSet_orderedExtremaDomain).aemeasurable
      (aemeasurable_brownianExtremaVector hB)]
  apply lintegral_congr_ae
  filter_upwards [orderedExtremaTest_eq_indicator_ae hB φ] with ω he
  rw [he]
  by_cases hs : brownianExtremaVector B ω ∈ orderedExtremaDomain
  · simp only [indicator_of_mem hs]
  · simp only [indicator_of_notMem hs,ENNReal.ofReal_zero]

/-- The nonnegative probabilistic layer average converges directly to the actual
ordered extrema measure against every bounded continuous real test (via ofReal). -/
theorem tendsto_lintegral_rescaledOrderedContactTest (hB : IsBrownianReal B μ)
    {E F : ℕ → ℝ} (hE : ∀ n, 0 < E n) (hF : ∀ n, 0 < F n)
    (hElim : Tendsto E atTop (𝓝 0)) (hFlim : Tendsto F atTop (𝓝 0))
    {φ : ExtremaVector → ℝ} (hφ : Continuous φ)
    {M : ℝ} (hM : ∀ p, ‖φ p‖ ≤ M) :
    Tendsto (fun n => ∫⁻ p : Ω × (ℝ × ℝ),
      ENNReal.ofReal (rescaledOrderedContactTest φ B (E n) (F n) p.2.1 p.2.2 p.1)
        ∂μ.prod contactAveragingSquare) atTop
      (𝓝 (∫⁻ p, ENNReal.ofReal (φ p) ∂brownianOrderedExtremaMeasure B μ)) := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have ht := tendsto_lintegral_of_dominated_convergence' (μ := μ.prod contactAveragingSquare)
    (fun _ => ENNReal.ofReal M)
    (fun n => (aemeasurable_rescaledOrderedContactTest hB contactAveragingSquare
      (E n) (F n) hφ.measurable).ennreal_ofReal)
    (fun n => Eventually.of_forall (fun p => ENNReal.ofReal_le_ofReal
      ((le_abs_self _).trans (norm_orderedContactTest_le B _ _ _ _ p.1 hM))))
    (by simp only [lintegral_const,measure_univ,mul_one]; exact ENNReal.ofReal_ne_top)
    (f := fun p : Ω × (ℝ × ℝ) => ENNReal.ofReal (orderedExtremaTest φ B p.1)) ?_
  · rw [lintegral_prod (fun p : Ω × (ℝ × ℝ) => ENNReal.ofReal (orderedExtremaTest φ B p.1)) (by
      have hm : AEMeasurable (fun ω => orderedExtremaTest φ B ω) μ := by
        apply ((hφ.measurable.indicator measurableSet_orderedExtremaDomain).comp_aemeasurable
          (aemeasurable_brownianExtremaVector hB)).congr
        exact (orderedExtremaTest_eq_indicator_ae hB φ).symm
      exact hm.ennreal_ofReal.comp_fst)] at ht
    simp only [lintegral_const,measure_univ,mul_one] at ht
    rwa [lintegral_orderedExtremaTest_eq_measure hB hφ.measurable] at ht
  · filter_upwards [quasiMeasurePreserving_fst.ae
      (brownian_rescaledOrderedContactTest_tendsto_ae hB hE hF hElim hFlim),
      quasiMeasurePreserving_snd.ae contactAveragingSquare_mem_ae] with p hp hu
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (hp p.2.1 hu.1 p.2.2 hu.2 φ hφ.continuousAt)

end BrownianAffine
