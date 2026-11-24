import PLAStochastic.Index.GEP.Kernel.Influence.Reward.OutputBoundary

/-! # Total-sum rewards only depend on their values on nonnegative sums -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

theorem kernel_IF_total_pathWeight_congr_nonneg (eps : ℝ) (k : ℕ)
    {H₁ H₂ : ℝ → ℝ≥0∞} (hH : ∀ s, 0 ≤ s → H₁ s = H₂ s) :
    kernelIFPathWeight eps k (fun g => H₁ (gapKeys g k)) =
      kernelIFPathWeight eps k (fun g => H₂ (gapKeys g k)) := by
  funext g
  unfold kernelIFPathWeight
  by_cases hg : g ∈ kernelIFPathEvent eps k
  · rw [indicator_of_mem hg, indicator_of_mem hg]
    apply hH
    exact Finset.sum_nonneg (fun j hj => (hg.1 j (Finset.mem_range.mp hj)).le)
  · rw [indicator_of_notMem hg, indicator_of_notMem hg]

theorem kernel_IF_total_activeWeight_congr_nonneg (eps : ℝ) (k i : ℕ)
    (q : FluxFacetIndex k) {H₁ H₂ : ℝ → ℝ≥0∞}
    (hH : ∀ s, 0 ≤ s → H₁ s = H₂ s) :
    kernelIFActiveWeight eps k i q (fun g => H₁ (gapKeys g k)) =
      kernelIFActiveWeight eps k i q (fun g => H₂ (gapKeys g k)) := by
  unfold kernelIFActiveWeight
  rw [kernel_IF_total_pathWeight_congr_nonneg eps k hH]

theorem kernel_IF_total_oriented_congr_nonneg (ν : ProbabilityMeasure ℝ)
    (f : ℝ → ℝ≥0∞) (eps : ℝ) (k i : ℕ)
    (A : FluxFacetIndex k → Prop) [DecidablePred A]
    {H₁ H₂ : ℝ → ℝ≥0∞} (hH : ∀ s, 0 ≤ s → H₁ s = H₂ s) :
    kernelIFOrientedDensity ν f eps k i A (fun g => H₁ (gapKeys g k)) =
      kernelIFOrientedDensity ν f eps k i A (fun g => H₂ (gapKeys g k)) := by
  funext x
  apply tsum_congr
  intro r
  split_ifs
  · rw [kernel_IF_total_activeWeight_congr_nonneg eps k i _ hH]
  · rfl

/-- The reward may be replaced by its nonnegative-domain extension before
coarea, because the actual path event already requires all gaps to be positive. -/
theorem kernel_IF_total_candidate_pins_ae_of_eq_nonneg (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} {D : ℝ} (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u)
    (hfD : ∀ u, f u ≤ D) (hfneg : ∀ u, u ≤ 0 → f u = 0)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun u => ENNReal.ofReal (f u)))
    (hpos : ∀ᵐ u ∂(ν : Measure ℝ), 0 < u)
    {eps : ℝ} (heps : 0 ≤ eps) {k i : ℕ} (hi : i < k) (q : FluxFacetIndex k)
    {H₁ H₂ : ℝ → ℝ≥0∞} (hH₂ : Measurable H₂)
    (hH : ∀ s, 0 ≤ s → H₁ s = H₂ s) :
    kernelFacetCandidateDensity ν (fun u => ENNReal.ofReal (f u)) eps k i q
      (kernelIFActiveWeight eps k i q (fun g => H₁ (gapKeys g k))) =ᵐ[volume.restrict (Ioi 0)]
        kernelIFFacetTotalPinDensity ν f eps q i H₂ := by
  rw [kernel_IF_total_activeWeight_congr_nonneg eps k i q hH]
  exact kernel_IF_total_candidate_facet_pins_ae ν hf hf0 hfD hfneg hν hpos heps hi q hH₂

end
end PGM
