import PLAStochastic.Index.GEP.Kernel.Facet.IIDLinearRoot
import PLAStochastic.Index.GEP.Kernel.Flux.Prefix.OneGapPrimitive

/-!
# Explicit densities of the actual finite-prefix facet roots

The coefficients come from the original prefix inequalities. An arbitrary
measurable full-path weight may select an active facet. Degenerate roots are
handled separately as mass at zero, without a nondegeneracy assumption on the
original regular law or on the facet enumeration.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal

def kernelFacetRootCoef (eps : ℝ) {k : ℕ} (q : FluxFacetIndex k) (i j : ℕ) : ℝ :=
  -fluxFacetCoef eps q j / fluxFacetCoef eps q i

theorem kernel_facet_root_eq_sum (eps : ℝ) (k i : ℕ) (q : FluxFacetIndex k)
    (g : ℕ → ℝ) :
    fluxPrefixRHS eps k i q g / fluxFacetCoef eps q i =
      ∑ j ∈ (range k).erase i, kernelFacetRootCoef eps q i j * g j := by
  simp only [fluxPrefixRHS, neg_div, sum_div, ← sum_neg_distrib]
  apply sum_congr rfl
  intro j _
  unfold kernelFacetRootCoef
  ring

def kernelFacetRootDensity (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ≥0∞)
    (eps : ℝ) (k i : ℕ) (q : FluxFacetIndex k) (m : ℕ)
    (W : (ℕ → ℝ) → ℝ≥0∞) : ℝ → ℝ≥0∞ :=
  kernelLinearDensity (iidLaw ν) (kernelFacetRootCoef eps q i m)
    (fun g => ∑ j ∈ ((range k).erase i).erase m, kernelFacetRootCoef eps q i j * g j)
    (kernelIIDRootWeight f m W)

/-- A nonzero coefficient supplies the exact actual facet-root density. -/
theorem kernel_facet_root_weighted_density (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hν : (ν : Measure ℝ) = volume.withDensity f)
    (eps : ℝ) (k i : ℕ) (q : FluxFacetIndex k) {m : ℕ}
    (hm : m ∈ (range k).erase i) (hc : kernelFacetRootCoef eps q i m ≠ 0)
    {W : (ℕ → ℝ) → ℝ≥0∞} (hW : Measurable W) :
    ((iidLaw ν).withDensity W).map
        (fun g => fluxPrefixRHS eps k i q g / fluxFacetCoef eps q i) =
      volume.withDensity (kernelFacetRootDensity ν f eps k i q m W) := by
  simp_rw [kernel_facet_root_eq_sum]
  exact kernel_iid_linear_map_density ν hf hν ((range k).erase i)
    (kernelFacetRootCoef eps q i) hm hc hW

/-- In particular the full-path active event can be retained as an indicator. -/
theorem kernel_facet_root_restricted_density (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hν : (ν : Measure ℝ) = volume.withDensity f)
    (eps : ℝ) (k i : ℕ) (q : FluxFacetIndex k) {m : ℕ}
    (hm : m ∈ (range k).erase i) (hc : kernelFacetRootCoef eps q i m ≠ 0)
    {S : Set (ℕ → ℝ)} (hS : MeasurableSet S) :
    ((iidLaw ν).restrict S).map
        (fun g => fluxPrefixRHS eps k i q g / fluxFacetCoef eps q i) =
      volume.withDensity (kernelFacetRootDensity ν f eps k i q m
        (S.indicator (fun _ => 1))) := by
  rw [← withDensity_indicator_one hS]
  exact kernel_facet_root_weighted_density ν hf hν eps k i q hm hc
    (measurable_const.indicator hS)

/-- All-zero roots have no positive-half-line contribution, even when the
weight has infinite total mass. -/
theorem kernel_facet_root_degenerate (ν : ProbabilityMeasure ℝ)
    (eps : ℝ) (k i : ℕ) (q : FluxFacetIndex k)
    (hc : ∀ m ∈ (range k).erase i, kernelFacetRootCoef eps q i m = 0)
    (W : (ℕ → ℝ) → ℝ≥0∞) :
    (((iidLaw ν).withDensity W).map
      (fun g => fluxPrefixRHS eps k i q g / fluxFacetCoef eps q i)).restrict (Ioi 0) = 0 := by
  have he : (fun g => fluxPrefixRHS eps k i q g / fluxFacetCoef eps q i) =
      fun _ : ℕ → ℝ => (0 : ℝ) := by
    funext g
    rw [kernel_facet_root_eq_sum]
    exact sum_eq_zero fun m hm => by rw [hc m hm, zero_mul]
  rw [he, Measure.map_const, Measure.restrict_smul]
  simp

/-- Every original facet is either harmless at zero or has one of the explicit
density representatives above. No additional hypothesis on a facet is needed. -/
theorem kernel_facet_root_density_cases (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hν : (ν : Measure ℝ) = volume.withDensity f)
    (eps : ℝ) (k i : ℕ) (q : FluxFacetIndex k)
    {W : (ℕ → ℝ) → ℝ≥0∞} (hW : Measurable W) :
    (((iidLaw ν).withDensity W).map
        (fun g => fluxPrefixRHS eps k i q g / fluxFacetCoef eps q i)).restrict (Ioi 0) = 0 ∨
      ∃ m ∈ (range k).erase i, kernelFacetRootCoef eps q i m ≠ 0 ∧
        ((iidLaw ν).withDensity W).map
          (fun g => fluxPrefixRHS eps k i q g / fluxFacetCoef eps q i) =
            volume.withDensity (kernelFacetRootDensity ν f eps k i q m W) := by
  by_cases h : ∃ m ∈ (range k).erase i, kernelFacetRootCoef eps q i m ≠ 0
  · obtain ⟨m, hm, hc⟩ := h
    exact Or.inr ⟨m, hm, hc, kernel_facet_root_weighted_density ν hf hν eps k i q hm hc hW⟩
  · left
    apply kernel_facet_root_degenerate
    simpa only [not_exists, not_and, not_not] using h

end
end PGM
