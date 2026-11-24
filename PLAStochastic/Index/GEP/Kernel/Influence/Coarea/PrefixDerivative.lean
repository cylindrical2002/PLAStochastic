import PLAStochastic.Index.GEP.Kernel.Influence.Coarea.OrientedFacets
import PLAStochastic.Index.GEP.Kernel.Facet.ExplicitPrefixDensity

/-!
# The actual finite-prefix derivative as an oriented active-facet sum

The original derivative is identified with the lower-minus-upper physical
facet density. There is no first-attaining selector in the resulting kernel.
The sums remain in ENNReal until after their finite endpoint measures have
been identified; no unproved interchange with `toReal` is needed.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

/-- Positive-local equality of densities gives global equality after the
prescribed zero extension. -/
theorem kernel_IF_positiveDensity_congr {d e : ℝ → ℝ≥0∞}
    (he : d =ᵐ[volume.restrict (Ioi (0 : ℝ))] e) :
    fluxPositiveDensity d =ᵐ[volume] fluxPositiveDensity e := by
  apply (ae_eq_restrict_iff_indicator_ae_eq measurableSet_Ioi).mp
  exact he.fun_comp ENNReal.toReal

/-- Source-side positive truncation changes no positive endpoint density. -/
theorem kernel_IF_selected_density_positive_cut (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hν : (ν : Measure ℝ) = volume.withDensity f)
    (eps : ℝ) (k i : ℕ) {E : (ℕ → ℝ) → ℝ} (hE : Measurable E)
    {S : Set (ℕ → ℝ)} (hS : MeasurableSet S)
    (hsel : ∀ g ∈ S, ∃ q : FluxFacetIndex k,
      E g = fluxPrefixRHS eps k i q g / fluxFacetCoef eps q i)
    {W : (ℕ → ℝ) → ℝ≥0∞} (hW : Measurable W) :
    kernelSelectedFacetDensity ν f eps k i E S W =ᵐ[volume.restrict (Ioi 0)]
      kernelSelectedFacetDensity ν f eps k i E (S ∩ E ⁻¹' Ioi 0) W := by
  apply (withDensity_eq_iff_of_sigmaFinite
    (flux_measurable_selected_density ν hf eps k i hE hS hW).aemeasurable
    (flux_measurable_selected_density ν hf eps k i hE
      (hS.inter (hE measurableSet_Ioi)) hW).aemeasurable).mp
  exact (kernel_selected_facet_map_density ν hf hν eps k i hE hS hsel hW).symm.trans
    (kernel_selected_positive_facet_map_density ν hf hν eps k i hE hS
      (fun g hg _ => hsel g hg) hW)

/-- The derivative of the scalar finite prefix, oriented by the actual
coefficient of the designated gap. -/
def kernelIFPrefixKernel (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ≥0∞)
    (eps : ℝ) (k i : ℕ) (x : ℝ) : ℝ :=
  fluxPositiveDensity (kernelIFOrientedDensity ν f eps k i
    (fun q => fluxFacetCoef eps q i < 0) (fun _ => 1)) x -
  fluxPositiveDensity (kernelIFOrientedDensity ν f eps k i
    (fun q => 0 < fluxFacetCoef eps q i) (fun _ => 1)) x

theorem kernel_IF_prefix_explicit_ae (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hν : (ν : Measure ℝ) = volume.withDensity f)
    (hpos : ∀ᵐ x ∂(ν : Measure ℝ), 0 < x) {eps : ℝ} {k i : ℕ}
    (heps : 0 < eps) (hk : 2 ≤ k) (hi : i < k) :
    fluxPrefixExplicit ν f eps k i =ᵐ[volume] kernelIFPrefixKernel ν f eps k i := by
  classical
  have hL := kernel_IF_positiveDensity_congr
    (kernel_IF_lower_density_eq_active_sum ν hf hν hpos heps hk hi
      (W := fun _ => 1) measurable_const)
  by_cases h : (fluxPos (fun q : FluxFacetIndex k => fluxFacetCoef eps q i)).Nonempty
  · let S := fluxPolyActive (fun q : FluxFacetIndex k => fluxFacetCoef eps q i)
      (fluxPrefixRHS eps k i) h
    have hS : MeasurableSet S := measurableSet_fluxPolyActive _ (measurable_fluxPrefixRHS eps k i) h
    have hU := kernel_IF_upper_density_eq_active_sum ν hf hν hpos heps hk hi h
      (W := fun _ => 1) measurable_const
    have hcut := kernel_IF_selected_density_positive_cut ν hf hν eps k i
      (measurable_fluxPolyUpper _ (measurable_fluxPrefixRHS eps k i) h) hS
      (fun g _ => fluxPolyUpper_select _ _ h g) (W := fun _ => 1) measurable_const
    have hU' := kernel_IF_positiveDensity_congr (hcut.trans hU)
    filter_upwards [hL, hU'] with x hxL hxU
    simpa only [fluxPrefixExplicit, kernelIFPrefixKernel, kernelIFLowerSection, h, dite_true,
      fluxPrefixLowerDensity, kernelPrefixUpper, S] using congrArg₂ (fun a b : ℝ => a - b) hxL hxU
  · have hzero : kernelIFOrientedDensity ν f eps k i
        (fun q => 0 < fluxFacetCoef eps q i) (fun _ => 1) = fun _ => 0 := by
      funext x
      unfold kernelIFOrientedDensity
      rw [tsum_fintype]
      apply Finset.sum_eq_zero
      intro r _
      apply if_neg
      intro hr
      exact h ⟨_, by simpa only [fluxPos, Finset.mem_filter, Finset.mem_univ, true_and] using hr⟩
    filter_upwards [hL] with x hxL
    simpa [fluxPrefixExplicit, kernelIFPrefixKernel, kernelIFLowerSection, h,
      fluxPrefixLowerDensity, hzero, fluxPositiveDensity] using hxL

/-- The actual inserted survival probability has the physical oriented-facet
kernel as an integrable derivative, under the original positive density law. -/
theorem kernel_IF_prefix_aePrimitive (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hν : (ν : Measure ℝ) = volume.withDensity f)
    (hpos : ∀ᵐ x ∂(ν : Measure ℝ), 0 < x) {eps : ℝ} {k i : ℕ}
    (heps : 0 < eps) (hk : 2 ≤ k) (hi : i < k) :
    AEPrimitive (pwQ eps ν k i) (kernelIFPrefixKernel ν f eps k i) ∧
      Integrable (kernelIFPrefixKernel ν f eps k i) := by
  have hp := flux_pwQ_explicit_aePrimitive ν hf hν hpos eps hk i
  have he := kernel_IF_prefix_explicit_ae ν hf hν hpos heps hk hi
  exact ⟨flux_aePrimitive_congr_derivative hp.1 he, hp.2.congr he⟩

end
end PGM
