import PLAStochastic.Index.GEP.Kernel.Facet.RootDensity
import PLAStochastic.Index.GEP.Kernel.Flux.Sections.ActiveRootPartition

/-!
# Explicit densities of selected actual facet endpoints

Each candidate uses a fixed nonzero coefficient if one exists. Zero candidates
contribute no mass on the positive half-line. The first-attaining partition
retains all ties and full-path dependence of the original selector.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal

def kernelFacetCandidateDensity (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ≥0∞)
    (eps : ℝ) (k i : ℕ) (q : FluxFacetIndex k) (W : (ℕ → ℝ) → ℝ≥0∞) : ℝ → ℝ≥0∞ :=
  if h : ∃ m ∈ (range k).erase i, kernelFacetRootCoef eps q i m ≠ 0 then
    kernelFacetRootDensity ν f eps k i q h.choose W
  else 0

theorem measurable_kernelFacetCandidateDensity (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (eps : ℝ) (k i : ℕ) (q : FluxFacetIndex k)
    {W : (ℕ → ℝ) → ℝ≥0∞} (hW : Measurable W) :
    Measurable (kernelFacetCandidateDensity ν f eps k i q W) := by
  unfold kernelFacetCandidateDensity
  split_ifs
  · exact measurable_kernelLinearDensity (iidLaw ν) _
      (Finset.measurable_sum _ fun j _ => measurable_const.mul (measurable_pi_apply j))
      (measurable_kernelIIDRootWeight hf _ hW)
  · exact measurable_const

theorem kernel_facet_root_positive_density (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hν : (ν : Measure ℝ) = volume.withDensity f)
    (eps : ℝ) (k i : ℕ) (q : FluxFacetIndex k)
    {W : (ℕ → ℝ) → ℝ≥0∞} (hW : Measurable W) :
    (((iidLaw ν).withDensity W).map
        (fun g => fluxPrefixRHS eps k i q g / fluxFacetCoef eps q i)).restrict (Ioi 0) =
      (volume.withDensity (kernelFacetCandidateDensity ν f eps k i q W)).restrict (Ioi 0) := by
  unfold kernelFacetCandidateDensity
  split_ifs with h
  · rw [kernel_facet_root_weighted_density ν hf hν eps k i q
      h.choose_spec.1 h.choose_spec.2 hW]
  · rw [withDensity_zero, Measure.restrict_zero]
    apply kernel_facet_root_degenerate
    simpa only [not_exists, not_and, not_not] using h

/-- Finite enumeration of the original facet roots. -/
def kernelEnumeratedRoot (eps : ℝ) (k i : ℕ)
    (q : Fin (Fintype.card (FluxFacetIndex k))) (g : ℕ → ℝ) : ℝ :=
  fluxPrefixRHS eps k i ((Fintype.equivFin (FluxFacetIndex k)).symm q) g /
    fluxFacetCoef eps ((Fintype.equivFin (FluxFacetIndex k)).symm q) i

theorem measurable_kernelEnumeratedRoot (eps : ℝ) (k i : ℕ)
    (q : Fin (Fintype.card (FluxFacetIndex k))) :
    Measurable (kernelEnumeratedRoot eps k i q) :=
  (measurable_fluxPrefixRHS eps k i _).div_const _

def kernelSelectedFacetDensity (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ≥0∞)
    (eps : ℝ) (k i : ℕ) (E : (ℕ → ℝ) → ℝ) (S : Set (ℕ → ℝ))
    (W : (ℕ → ℝ) → ℝ≥0∞) : ℝ → ℝ≥0∞ :=
  ∑' q : Fin (Fintype.card (FluxFacetIndex k)),
    kernelFacetCandidateDensity ν f eps k i ((Fintype.equivFin (FluxFacetIndex k)).symm q)
      ((S ∩ fluxFirstRoot E (kernelEnumeratedRoot eps k i) q).indicator W)

/-- The original selected endpoint has the explicit sum of weighted facet
densities. The only selection hypothesis is the actual finite root identity;
independence and almost-everywhere uniqueness are not assumed. -/
theorem kernel_selected_facet_map_density (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hν : (ν : Measure ℝ) = volume.withDensity f)
    (eps : ℝ) (k i : ℕ) {E : (ℕ → ℝ) → ℝ} (hE : Measurable E)
    {S : Set (ℕ → ℝ)} (hS : MeasurableSet S)
    (hsel : ∀ g ∈ S, ∃ q : FluxFacetIndex k,
      E g = fluxPrefixRHS eps k i q g / fluxFacetCoef eps q i)
    {W : (ℕ → ℝ) → ℝ≥0∞} (hW : Measurable W) :
    ((((iidLaw ν).withDensity W).restrict S).map E).restrict (Ioi 0) =
      (volume.restrict (Ioi 0)).withDensity
        (kernelSelectedFacetDensity ν f eps k i E S W) := by
  have hF (q : FluxFacetIndex k) :
      Measurable (fun g => fluxPrefixRHS eps k i q g / fluxFacetCoef eps q i) :=
    (measurable_fluxPrefixRHS eps k i q).div_const _
  have he := flux_map_selected_eq_sum_fintype ((iidLaw ν).withDensity W) hS hE hF hsel
  change (((iidLaw ν).withDensity W).restrict S).map E = _ at he
  rw [he, Measure.restrict_sum _ measurableSet_Ioi]
  unfold kernelSelectedFacetDensity
  have hm (q : Fin (Fintype.card (FluxFacetIndex k))) :
      MeasurableSet (S ∩ fluxFirstRoot E (kernelEnumeratedRoot eps k i) q) :=
    hS.inter (measurableSet_fluxFirstRoot hE (measurable_kernelEnumeratedRoot eps k i) q)
  rw [withDensity_tsum (fun q => measurable_kernelFacetCandidateDensity ν hf eps k i _
    (hW.indicator (hm q)))]
  congr 1
  funext q
  have hpiece := kernel_facet_root_positive_density ν hf hν eps k i
    ((Fintype.equivFin (FluxFacetIndex k)).symm q) (hW.indicator (hm q))
  rw [withDensity_indicator (hm q), ← restrict_withDensity (hm q)] at hpiece
  rw [restrict_withDensity measurableSet_Ioi] at hpiece
  exact hpiece

end
end PGM
