import PLAStochastic.Index.GEP.Kernel.Influence.Reward.NonnegativeCut
import PLAStochastic.Index.GEP.Kernel.Insertion.ExteriorReward

/-! # Original output boundary represented by the pointwise bounded exterior reward -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option maxHeartbeats 1200000

theorem kernel_IF_weighted_prefix_congr_nonneg (ν : ProbabilityMeasure ℝ)
    (f : ℝ → ℝ≥0∞) (eps : ℝ) (k i : ℕ) {H₁ H₂ : ℝ → ℝ}
    (hH : ∀ s, 0 ≤ s → H₁ s = H₂ s) :
    kernelIFWeightedPrefixKernel ν f eps k i (fun g => H₁ (gapKeys g k)) =
      kernelIFWeightedPrefixKernel ν f eps k i (fun g => H₂ (gapKeys g k)) := by
  have hp (A : FluxFacetIndex k → Prop) [DecidablePred A] :=
    kernel_IF_total_oriented_congr_nonneg ν f eps k i A
      (H₁ := fun s => ENNReal.ofReal (H₁ s)) (H₂ := fun s => ENNReal.ofReal (H₂ s))
      (fun s hs => congrArg ENNReal.ofReal (hH s hs))
  have hn (A : FluxFacetIndex k → Prop) [DecidablePred A] :=
    kernel_IF_total_oriented_congr_nonneg ν f eps k i A
      (H₁ := fun s => ENNReal.ofReal (-H₁ s)) (H₂ := fun s => ENNReal.ofReal (-H₂ s))
      (fun s hs => congrArg (fun u => ENNReal.ofReal (-u)) (hH s hs))
  unfold kernelIFWeightedPrefixKernel kernelIFSignedDensity
  rw [hp (fun q => fluxFacetCoef eps q i < 0), hn (fun q => fluxFacetCoef eps q i < 0),
    hp (fun q => 0 < fluxFacetCoef eps q i), hn (fun q => 0 < fluxFacetCoef eps q i)]

theorem output_IF_boundary_eq_cut_pins_ae (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} {D : ℝ} (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u)
    (hfD : ∀ u, f u ≤ D) (hfneg : ∀ u, u ≤ 0 → f u = 0)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun u => ENNReal.ofReal (f u)))
    (hpos : ∀ᵐ u ∂(ν : Measure ℝ), 0 < u)
    {eps : ℝ} (heps : 0 ≤ eps) {η M C : ℝ} {ψ : ℝ → ℝ} (hψ : OutTest η M ψ) :
    outputIFBoundary eps ν (fun u => ENNReal.ofReal (f u)) ψ C =ᵐ[volume]
      kernelIFTotalPinBoundary ν f eps (kernelPositiveBoundaryReward ν C ψ) := by
  have he (k i : ℕ) := kernel_IF_weighted_prefix_congr_nonneg ν
    (fun u => ENNReal.ofReal (f u)) eps k i
    (H₁ := kernelBoundaryReward ν C ψ) (H₂ := kernelPositiveBoundaryReward ν C ψ)
    (fun s hs => (indicator_of_mem hs _).symm)
  have hh : ∀ᵐ x ∂volume, ∀ b : FluxInfluenceIndex,
      kernelIFWeightedPrefixKernel ν (fun u => ENNReal.ofReal (f u)) eps b.1 b.2
          (fun g => kernelPositiveBoundaryReward ν C ψ (gapKeys g b.1)) x =
        kernelIFTotalPinPrefix ν f eps b.1 b.2 (kernelPositiveBoundaryReward ν C ψ) x :=
    ae_all_iff.mpr fun b => kernel_IF_total_prefix_pins_ae ν hf hf0 hfD hfneg hν hpos heps b.2.isLt
      (measurable_kernelPositiveBoundaryReward hψ ν C)
  filter_upwards [hh] with x hx
  unfold outputIFBoundary outputIFTerm kernelIFTotalPinBoundary
  simp_rw [he]
  rw [kernel_IF_real_tsum_triangle (fun k i =>
    kernelIFWeightedPrefixKernel ν (fun u => ENNReal.ofReal (f u)) eps k i
      (fun g => kernelPositiveBoundaryReward ν C ψ (gapKeys g k)) x)]
  exact tsum_congr hx

end
end PGM
