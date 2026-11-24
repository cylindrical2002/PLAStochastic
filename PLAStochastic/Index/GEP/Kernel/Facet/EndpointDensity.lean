import PLAStochastic.Index.GEP.Kernel.Facet.SelectedDensity

/-!
# Explicit densities of the original polyhedral section endpoints

The artificial zero in the lower endpoint is removed only on the positive
half-line. Actual active-event and reward weights remain in the density.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem kernel_map_restrict_positive {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {E : Ω → ℝ} (hE : Measurable E) (S : Set Ω) :
    ((P.restrict (S ∩ E ⁻¹' Ioi 0)).map E).restrict (Ioi 0) =
      ((P.restrict S).map E).restrict (Ioi 0) := by
  rw [Measure.restrict_map hE measurableSet_Ioi, Measure.restrict_map hE measurableSet_Ioi,
    Measure.restrict_restrict (hE measurableSet_Ioi),
    Measure.restrict_restrict (hE measurableSet_Ioi)]
  congr 2
  ext ω
  simp only [mem_inter_iff]
  tauto

theorem kernel_selected_positive_facet_map_density (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hν : (ν : Measure ℝ) = volume.withDensity f)
    (eps : ℝ) (k i : ℕ) {E : (ℕ → ℝ) → ℝ} (hE : Measurable E)
    {S : Set (ℕ → ℝ)} (hS : MeasurableSet S)
    (hsel : ∀ g ∈ S, 0 < E g → ∃ q : FluxFacetIndex k,
      E g = fluxPrefixRHS eps k i q g / fluxFacetCoef eps q i)
    {W : (ℕ → ℝ) → ℝ≥0∞} (hW : Measurable W) :
    ((((iidLaw ν).withDensity W).restrict S).map E).restrict (Ioi 0) =
      (volume.restrict (Ioi 0)).withDensity
        (kernelSelectedFacetDensity ν f eps k i E (S ∩ E ⁻¹' Ioi 0) W) := by
  have hp := kernel_selected_facet_map_density ν hf hν eps k i hE
    (hS.inter (hE measurableSet_Ioi)) (fun g hg => hsel g hg.1 hg.2) hW
  rw [kernel_map_restrict_positive _ hE S] at hp
  exact hp

def kernelPrefixLower (eps : ℝ) (k i : ℕ) : (ℕ → ℝ) → ℝ :=
  fluxPolyLower (fun q : FluxFacetIndex k => fluxFacetCoef eps q i)
    (fluxPrefixRHS eps k i)

/-- The real lower endpoint of the original finite prefix inequalities. -/
theorem kernel_prefix_lower_density (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hν : (ν : Measure ℝ) = volume.withDensity f)
    (eps : ℝ) (k i : ℕ) {S : Set (ℕ → ℝ)} (hS : MeasurableSet S)
    {W : (ℕ → ℝ) → ℝ≥0∞} (hW : Measurable W) :
    ((((iidLaw ν).withDensity W).restrict S).map (kernelPrefixLower eps k i)).restrict
        (Ioi 0) =
      (volume.restrict (Ioi 0)).withDensity (kernelSelectedFacetDensity ν f eps k i
        (kernelPrefixLower eps k i) (S ∩ (kernelPrefixLower eps k i) ⁻¹' Ioi 0) W) := by
  apply kernel_selected_positive_facet_map_density ν hf hν eps k i
    (measurable_fluxPolyLower _ (measurable_fluxPrefixRHS eps k i)) hS ?_ hW
  intro g _ hg
  exact fluxPolyLower_select _ _ g hg

def kernelPrefixUpper (eps : ℝ) (k i : ℕ)
    (h : (fluxPos (fun q : FluxFacetIndex k => fluxFacetCoef eps q i)).Nonempty) :
    (ℕ → ℝ) → ℝ :=
  fluxPolyUpper (fun q : FluxFacetIndex k => fluxFacetCoef eps q i)
    (fluxPrefixRHS eps k i) h

/-- The real finite upper endpoint; the half-line case has no upper mass. -/
theorem kernel_prefix_upper_density (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hν : (ν : Measure ℝ) = volume.withDensity f)
    (eps : ℝ) (k i : ℕ)
    (h : (fluxPos (fun q : FluxFacetIndex k => fluxFacetCoef eps q i)).Nonempty)
    {S : Set (ℕ → ℝ)} (hS : MeasurableSet S)
    {W : (ℕ → ℝ) → ℝ≥0∞} (hW : Measurable W) :
    ((((iidLaw ν).withDensity W).restrict S).map (kernelPrefixUpper eps k i h)).restrict
        (Ioi 0) =
      (volume.restrict (Ioi 0)).withDensity (kernelSelectedFacetDensity ν f eps k i
        (kernelPrefixUpper eps k i h) S W) := by
  apply kernel_selected_facet_map_density ν hf hν eps k i
    (measurable_fluxPolyUpper _ (measurable_fluxPrefixRHS eps k i) h) hS ?_ hW
  intro g _
  exact fluxPolyUpper_select _ _ h g

end
end PGM
