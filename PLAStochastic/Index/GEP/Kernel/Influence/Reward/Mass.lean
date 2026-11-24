import PLAStochastic.Index.GEP.Kernel.Influence.Pins.Mass
import PLAStochastic.Index.GEP.Kernel.Influence.Reward.AllFacets

/-! # Reindexing the original nonnegative facet masses by physical block lengths -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option maxHeartbeats 1200000

def kernelIFTotalPinOrientedDensity (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (eps : ℝ) (k i : ℕ) (A : FluxFacetIndex k → Prop) [DecidablePred A]
    (H : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ∑' r : Fin (Fintype.card (FluxFacetIndex k)),
    if A ((Fintype.equivFin (FluxFacetIndex k)).symm r) then
      kernelIFFacetTotalPinDensity ν f eps ((Fintype.equivFin (FluxFacetIndex k)).symm r) i H x
    else 0

theorem kernel_IF_total_oriented_pins_ae (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} {D : ℝ} (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u)
    (hfD : ∀ u, f u ≤ D) (hfneg : ∀ u, u ≤ 0 → f u = 0)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun u => ENNReal.ofReal (f u)))
    (hpos : ∀ᵐ u ∂(ν : Measure ℝ), 0 < u)
    {eps : ℝ} (heps : 0 ≤ eps) {k i : ℕ} (hi : i < k)
    (A : FluxFacetIndex k → Prop) [DecidablePred A]
    {H : ℝ → ℝ≥0∞} (hH : Measurable H) :
    kernelIFOrientedDensity ν (fun u => ENNReal.ofReal (f u)) eps k i A (fun g => H (gapKeys g k))
      =ᵐ[volume.restrict (Ioi 0)] kernelIFTotalPinOrientedDensity ν f eps k i A H := by
  have hh : ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)), ∀ q : FluxFacetIndex k,
      kernelFacetCandidateDensity ν (fun u => ENNReal.ofReal (f u)) eps k i q
        (kernelIFActiveWeight eps k i q (fun g => H (gapKeys g k))) x =
          kernelIFFacetTotalPinDensity ν f eps q i H x :=
    (ae_all_iff).mpr fun q =>
      kernel_IF_total_candidate_facet_pins_ae ν hf hf0 hfD hfneg hν hpos heps hi q hH
  filter_upwards [hh] with x hx
  apply tsum_congr
  intro r
  split_ifs <;> simp only [hx]

def kernelIFTotalPinSourceMass (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (eps : ℝ)
    (H : ℝ → ℝ≥0∞) (A : KernelIFSourceIndex → Prop) (x : ℝ) : ℝ≥0∞ := by
  classical
  exact ∑' b : KernelIFSourceIndex, if A b then
    kernelIFFacetTotalPinDensity ν f eps b.2.2 b.2.1 H x else 0

def kernelIFTotalPinBlockMass (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (eps : ℝ)
    (H : ℝ → ℝ≥0∞) (A : KernelIFSourceIndex → Prop) (x : ℝ) : ℝ≥0∞ := by
  classical
  exact (∑' p : KernelIFBlockIndex, if A (kernelIFLeftOfBlocks p).1 then
      kernelIFFacetTotalPinDensity ν f eps (kernelIFLeftOfBlocks p).1.2.2
        (kernelIFLeftOfBlocks p).1.2.1 H x else 0) +
    ∑' p : KernelIFBlockIndex, if A (kernelIFRightOfBlocks p).1 then
      kernelIFFacetTotalPinDensity ν f eps (kernelIFRightOfBlocks p).1.2.2
        (kernelIFRightOfBlocks p).1.2.1 H x else 0

theorem kernel_IF_total_pin_mass_reindex (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (eps : ℝ) (H : ℝ → ℝ≥0∞) (A : KernelIFSourceIndex → Prop) (x : ℝ) :
    kernelIFTotalPinSourceMass ν f eps H A x = kernelIFTotalPinBlockMass ν f eps H A x := by
  classical
  apply kernel_IF_source_tsum_blocks
  intro b hl hr
  by_cases hA : A b
  · simp only [if_pos hA]
    unfold kernelIFFacetTotalPinDensity
    by_cases hq : kernelFacetEffective eps b.2.2
    · have hl' : ¬((b.2.2.1 : ℕ) ≤ b.2.1 ∧ (b.2.1 : ℕ) < b.2.2.2.1) :=
        fun hh => hl ⟨hq.1, hh⟩
      have hr' : ¬((b.2.2.2.1 : ℕ) ≤ b.2.1 ∧ (b.2.1 : ℕ) < b.2.2.2.2.1) :=
        fun hh => hr ⟨hq.1, hh⟩
      simp only [if_pos hq, if_neg hl', if_neg hr']
    · simp only [if_neg hq]
  · simp only [if_neg hA]

/-- The finite enumeration used by the original selected-facet density carries
no additional multiplicity. -/
theorem kernel_IF_total_pin_oriented_eq_tsum (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (eps : ℝ) (k i : ℕ) (A : FluxFacetIndex k → Prop) [DecidablePred A] (H : ℝ → ℝ≥0∞) (x : ℝ) :
    kernelIFTotalPinOrientedDensity ν f eps k i A H x =
      ∑' q : FluxFacetIndex k, if A q then kernelIFFacetTotalPinDensity ν f eps q i H x else 0 :=
  (Fintype.equivFin (FluxFacetIndex k)).symm.tsum_eq
    (fun q => if A q then kernelIFFacetTotalPinDensity ν f eps q i H x else 0)

/-- Both orientations, or any chosen collection of original facets, are
reindexed before taking real parts. This equality is valid even when infinite. -/
theorem kernel_IF_total_oriented_mass_eq_blocks (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (eps : ℝ) (H : ℝ → ℝ≥0∞) (A : KernelIFSourceIndex → Prop) [DecidablePred A] (x : ℝ) :
    (∑' b : FluxInfluenceIndex, kernelIFTotalPinOrientedDensity ν f eps b.1 b.2
      (fun q => A ⟨b.1, b.2, q⟩) H x) = kernelIFTotalPinBlockMass ν f eps H A x := by
  rw [← kernel_IF_total_pin_mass_reindex]
  unfold kernelIFTotalPinSourceMass
  rw [ENNReal.tsum_sigma' (f := fun b : FluxInfluenceIndex =>
    kernelIFTotalPinOrientedDensity ν f eps b.1 b.2 (fun q => A ⟨b.1, b.2, q⟩) H x)]
  rw [ENNReal.tsum_sigma']
  apply tsum_congr
  intro k
  simp_rw [kernel_IF_total_pin_oriented_eq_tsum]
  exact ENNReal.tsum_prod.symm

/-- This is the full mass of the original candidate densities, not a grouped
signed derivative. Thus later absolute bounds apply to the same physical sum. -/
theorem kernel_IF_total_actual_oriented_mass_eq_blocks_ae (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} {D : ℝ} (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u)
    (hfD : ∀ u, f u ≤ D) (hfneg : ∀ u, u ≤ 0 → f u = 0)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun u => ENNReal.ofReal (f u)))
    (hpos : ∀ᵐ u ∂(ν : Measure ℝ), 0 < u)
    {eps : ℝ} (heps : 0 ≤ eps)
    {H : ℝ → ℝ≥0∞} (hH : Measurable H) (A : KernelIFSourceIndex → Prop) [DecidablePred A] :
    (fun x => ∑' b : FluxInfluenceIndex,
      kernelIFOrientedDensity ν (fun u => ENNReal.ofReal (f u)) eps b.1 b.2
        (fun q => A ⟨b.1, b.2, q⟩) (fun g => H (gapKeys g b.1)) x)
      =ᵐ[volume.restrict (Ioi 0)] kernelIFTotalPinBlockMass ν f eps H A := by
  have hh : ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)), ∀ b : FluxInfluenceIndex,
      kernelIFOrientedDensity ν (fun u => ENNReal.ofReal (f u)) eps b.1 b.2
          (fun q => A ⟨b.1, b.2, q⟩) (fun g => H (gapKeys g b.1)) x =
        kernelIFTotalPinOrientedDensity ν f eps b.1 b.2 (fun q => A ⟨b.1, b.2, q⟩) H x :=
    ae_all_iff.mpr fun b => kernel_IF_total_oriented_pins_ae ν hf hf0 hfD hfneg hν hpos heps b.2.isLt _ hH
  filter_upwards [hh] with x hx
  rw [← kernel_IF_total_oriented_mass_eq_blocks]
  exact tsum_congr hx

end
end PGM
