import PLAStochastic.Index.GEP.Kernel.Influence.Pins.InfiniteInfluence
import PLAStochastic.Index.GEP.Kernel.Influence.Pins.OuterRows

/-! # Reindexing the original nonnegative facet masses by physical block lengths -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option maxHeartbeats 1200000

abbrev KernelIFSourceIndex := Σ k : ℕ, Fin k × FluxFacetIndex k

def kernelIFPinSourceMass (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (eps : ℝ)
    (A : KernelIFSourceIndex → Prop) (x : ℝ) : ℝ≥0∞ := by
  classical
  exact ∑' b : KernelIFSourceIndex, if A b then
    kernelIFFacetPinDensity ν f eps b.2.2 b.2.1 (fun _ => 1) x else 0

def kernelIFPinBlockMass (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (eps : ℝ)
    (A : KernelIFSourceIndex → Prop) (x : ℝ) : ℝ≥0∞ := by
  classical
  exact (∑' p : KernelIFBlockIndex, if A (kernelIFLeftOfBlocks p).1 then
      kernelIFFacetPinDensity ν f eps (kernelIFLeftOfBlocks p).1.2.2
        (kernelIFLeftOfBlocks p).1.2.1 (fun _ => 1) x else 0) +
    ∑' p : KernelIFBlockIndex, if A (kernelIFRightOfBlocks p).1 then
      kernelIFFacetPinDensity ν f eps (kernelIFRightOfBlocks p).1.2.2
        (kernelIFRightOfBlocks p).1.2.1 (fun _ => 1) x else 0

theorem kernel_IF_pin_mass_reindex (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (eps : ℝ) (A : KernelIFSourceIndex → Prop) (x : ℝ) :
    kernelIFPinSourceMass ν f eps A x = kernelIFPinBlockMass ν f eps A x := by
  classical
  apply kernel_IF_source_tsum_blocks
  intro b hl hr
  by_cases hA : A b
  · simp only [if_pos hA]
    unfold kernelIFFacetPinDensity
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
theorem kernel_IF_pin_oriented_eq_tsum (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (eps : ℝ) (k i : ℕ) (A : FluxFacetIndex k → Prop) [DecidablePred A] (x : ℝ) :
    kernelIFPinOrientedDensity ν f eps k i A x =
      ∑' q : FluxFacetIndex k, if A q then kernelIFFacetPinDensity ν f eps q i (fun _ => 1) x else 0 :=
  (Fintype.equivFin (FluxFacetIndex k)).symm.tsum_eq
    (fun q => if A q then kernelIFFacetPinDensity ν f eps q i (fun _ => 1) x else 0)

/-- Both orientations, or any chosen collection of original facets, are
reindexed before taking real parts. This equality is valid even when infinite. -/
theorem kernel_IF_oriented_mass_eq_blocks (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (eps : ℝ) (A : KernelIFSourceIndex → Prop) [DecidablePred A] (x : ℝ) :
    (∑' b : FluxInfluenceIndex, kernelIFPinOrientedDensity ν f eps b.1 b.2
      (fun q => A ⟨b.1, b.2, q⟩) x) = kernelIFPinBlockMass ν f eps A x := by
  rw [← kernel_IF_pin_mass_reindex]
  unfold kernelIFPinSourceMass
  rw [ENNReal.tsum_sigma' (f := fun b : FluxInfluenceIndex =>
    kernelIFPinOrientedDensity ν f eps b.1 b.2 (fun q => A ⟨b.1, b.2, q⟩) x)]
  rw [ENNReal.tsum_sigma']
  apply tsum_congr
  intro k
  simp_rw [kernel_IF_pin_oriented_eq_tsum]
  exact ENNReal.tsum_prod.symm

/-- This is the full mass of the original candidate densities, not a grouped
signed derivative. Thus later absolute bounds apply to the same physical sum. -/
theorem kernel_IF_actual_oriented_mass_eq_blocks_ae (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} {D : ℝ} (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u)
    (hfD : ∀ u, f u ≤ D) (hfneg : ∀ u, u ≤ 0 → f u = 0)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun u => ENNReal.ofReal (f u)))
    (hpos : ∀ᵐ u ∂(ν : Measure ℝ), 0 < u)
    {eps : ℝ} (heps : 0 ≤ eps)
    (A : KernelIFSourceIndex → Prop) [DecidablePred A] :
    (fun x => ∑' b : FluxInfluenceIndex,
      kernelIFOrientedDensity ν (fun u => ENNReal.ofReal (f u)) eps b.1 b.2
        (fun q => A ⟨b.1, b.2, q⟩) (fun _ => 1) x)
      =ᵐ[volume.restrict (Ioi 0)] kernelIFPinBlockMass ν f eps A := by
  have hh : ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)), ∀ b : FluxInfluenceIndex,
      kernelIFOrientedDensity ν (fun u => ENNReal.ofReal (f u)) eps b.1 b.2
          (fun q => A ⟨b.1, b.2, q⟩) (fun _ => 1) x =
        kernelIFPinOrientedDensity ν f eps b.1 b.2 (fun q => A ⟨b.1, b.2, q⟩) x :=
    ae_all_iff.mpr fun b => kernel_IF_oriented_pins_ae ν hf hf0 hfD hfneg hν hpos heps b.2.isLt _
  filter_upwards [hh] with x hx
  rw [← kernel_IF_oriented_mass_eq_blocks]
  exact tsum_congr hx

end
end PGM
