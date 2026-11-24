import PLAStochastic.Index.GEP.Kernel.Facet.ExplicitEndpointDensity
import PLAStochastic.Index.GEP.Kernel.Flux.Weighted.PrefixBound

/-!
# Explicit signed facet density of the actual finite prefix

The original inserted survival probability has derivative equal to the explicit
selected lower endpoint density minus the explicit upper endpoint density. The
half-line case contains only the actual lower endpoint. Every density is zero
extended outside the positive half-line.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

def fluxPrefixLowerDensity (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ≥0∞)
    (eps : ℝ) (k i : ℕ) (S : Set (ℕ → ℝ)) : ℝ → ℝ≥0∞ :=
  kernelSelectedFacetDensity ν f eps k i (kernelPrefixLower eps k i)
    (S ∩ (kernelPrefixLower eps k i) ⁻¹' Ioi 0) (fun _ => 1)

def fluxPrefixExplicit (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ≥0∞)
    (eps : ℝ) (k i : ℕ) : ℝ → ℝ :=
  if h : (fluxPos (fun q : FluxFacetIndex k => fluxFacetCoef eps q i)).Nonempty then
    let S := fluxPolyActive (fun q : FluxFacetIndex k => fluxFacetCoef eps q i) (fluxPrefixRHS eps k i) h
    fun x => fluxPositiveDensity (fluxPrefixLowerDensity ν f eps k i S) x -
      fluxPositiveDensity (kernelSelectedFacetDensity ν f eps k i (kernelPrefixUpper eps k i h) S (fun _ => 1)) x
  else
    fluxPositiveDensity (fluxPrefixLowerDensity ν f eps k i
      (fluxPolyZeroOK (fun q : FluxFacetIndex k => fluxFacetCoef eps q i) (fluxPrefixRHS eps k i)))

theorem flux_pwQ_eq_poly_all {ν : ProbabilityMeasure ℝ}
    (hpos : ∀ᵐ x ∂(ν : Measure ℝ), 0 < x) (eps : ℝ) {k : ℕ} (hk : 2 ≤ k) (i : ℕ)
    {x : ℝ} (hx : 0 < x) :
    pwQ eps ν k i x = (iidLaw ν).real
      {g | ∀ q : FluxFacetIndex k, fluxFacetCoef eps q i * x ≤ fluxPrefixRHS eps k i q g} := by
  have hgs : ∀ᵐ g ∂iidLaw ν, ∀ l, 0 < g l := by
    rw [ae_all_iff]
    intro l
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => (ν : Measure ℝ)) l).quasiMeasurePreserving
      |>.ae hpos
  apply measureReal_congr
  filter_upwards [hgs] with g hg
  apply propext
  change ((k : ℕ∞) < gapSegLen eps (Function.update g i x)) ↔ _
  rw [gapSegLen, lt_segLen_iff]
  exact flux_prefix_update_iff_all hk hx (fun j _ _ => hg j)

/-- The actual finite-prefix derivative is the explicitly defined signed sum
of selected facet densities. No RN derivative remains in the conclusion. -/
theorem flux_pwQ_explicit_aePrimitive (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hν : (ν : Measure ℝ) = volume.withDensity f)
    (hpos : ∀ᵐ x ∂(ν : Measure ℝ), 0 < x) (eps : ℝ) {k : ℕ} (hk : 2 ≤ k) (i : ℕ) :
    AEPrimitive (pwQ eps ν k i) (fluxPrefixExplicit ν f eps k i) ∧
      Integrable (fluxPrefixExplicit ν f eps k i) := by
  classical
  let c := fun q : FluxFacetIndex k => fluxFacetCoef eps q i
  let d := fluxPrefixRHS eps k i
  have hd : ∀ q, Measurable (d q) := measurable_fluxPrefixRHS eps k i
  have hL : Measurable (kernelPrefixLower eps k i) := measurable_fluxPolyLower c hd
  by_cases h : (fluxPos c).Nonempty
  · let S := fluxPolyActive c d h
    let Q := (iidLaw ν).restrict S
    have hS : MeasurableSet S := measurableSet_fluxPolyActive c hd h
    have hU : Measurable (kernelPrefixUpper eps k i h) := measurable_fluxPolyUpper c hd h
    let dL := fluxPrefixLowerDensity ν f eps k i S
    let dU := kernelSelectedFacetDensity ν f eps k i (kernelPrefixUpper eps k i h) S (fun _ => 1)
    have hdL : Measurable dL := flux_measurable_selected_density ν hf eps k i hL
      (hS.inter (hL measurableSet_Ioi)) measurable_const
    have hdU : Measurable dU := flux_measurable_selected_density ν hf eps k i hU hS measurable_const
    have heL : (Q.map (kernelPrefixLower eps k i)).restrict (Ioi 0) =
        (volume.restrict (Ioi 0)).withDensity dL := by
      simpa only [Q, dL, fluxPrefixLowerDensity, ← Pi.one_def, withDensity_one] using kernel_prefix_lower_density ν hf hν eps k i hS (W := fun _ => 1) measurable_const
    have heU : (Q.map (kernelPrefixUpper eps k i h)).restrict (Ioi 0) =
        (volume.restrict (Ioi 0)).withDensity dU := by
      simpa only [Q, dU, ← Pi.one_def, withDensity_one] using kernel_prefix_upper_density ν hf hν eps k i h hS (W := fun _ => 1) measurable_const
    have horder : ∀ᵐ g ∂Q, kernelPrefixLower eps k i g ≤ kernelPrefixUpper eps k i h g := by
      filter_upwards [ae_restrict_mem hS] with g hg
      exact hg.2
    obtain ⟨hI, a, ha⟩ := flux_closed_section_explicit_aePrimitive Q hL hU horder hdL hdU heL heU
    have hji := (flux_integrable_positive_density _ hdL heL).sub (flux_integrable_positive_density _ hdU heU)
    have hdef : fluxPrefixExplicit ν f eps k i = fun x => fluxPositiveDensity dL x - fluxPositiveDensity dU x := by
      simp only [fluxPrefixExplicit, show (fluxPos (fun q : FluxFacetIndex k => fluxFacetCoef eps q i)).Nonempty from h, dite_true]
      rfl
    rw [hdef]
    refine ⟨⟨hI, a, ?_⟩, hji⟩
    filter_upwards [ha, ae_restrict_mem measurableSet_Ioi] with x hax hx
    rw [flux_pwQ_eq_poly_all hpos eps hk i hx]
    have he : (iidLaw ν).real {g | ∀ q, c q * x ≤ d q g} =
        Q.real {g | kernelPrefixLower eps k i g ≤ x ∧ x ≤ kernelPrefixUpper eps k i h g} := by
      have hm : MeasurableSet {g | kernelPrefixLower eps k i g ≤ x ∧ x ≤ kernelPrefixUpper eps k i h g} :=
        (measurableSet_le hL measurable_const).inter (measurableSet_le measurable_const hU)
      rw [show Q = (iidLaw ν).restrict S from rfl, measureReal_restrict_apply hm]
      congr 1
      ext g
      change (∀ q, c q * x ≤ d q g) ↔
        ((fluxPolyLower c d g ≤ x ∧ x ≤ fluxPolyUpper c d h g) ∧
          (g ∈ fluxPolyZeroOK c d ∧ fluxPolyLower c d g ≤ fluxPolyUpper c d h g))
      rw [fluxPoly_iff_interval c d h g hx]
      constructor
      · rintro ⟨hz, hl, hu⟩
        exact ⟨⟨hl, hu⟩, hz, hl.trans hu⟩
      · rintro ⟨⟨hl, hu⟩, hz, _⟩
        exact ⟨hz, hl, hu⟩
    rw [he]
    exact hax
  · let S := fluxPolyZeroOK c d
    let Q := (iidLaw ν).restrict S
    have hS : MeasurableSet S := measurableSet_fluxPolyZeroOK c hd
    let dL := fluxPrefixLowerDensity ν f eps k i S
    have hdL : Measurable dL := flux_measurable_selected_density ν hf eps k i hL
      (hS.inter (hL measurableSet_Ioi)) measurable_const
    have heL : (Q.map (kernelPrefixLower eps k i)).restrict (Ioi 0) =
        (volume.restrict (Ioi 0)).withDensity dL := by
      simpa only [Q, dL, fluxPrefixLowerDensity, ← Pi.one_def, withDensity_one] using kernel_prefix_lower_density ν hf hν eps k i hS (W := fun _ => 1) measurable_const
    obtain ⟨hI, a, ha⟩ := flux_cdf_explicit_aePrimitive _ hdL heL
    have hdef : fluxPrefixExplicit ν f eps k i = fluxPositiveDensity dL := by
      simp only [fluxPrefixExplicit, show ¬ (fluxPos (fun q : FluxFacetIndex k => fluxFacetCoef eps q i)).Nonempty from h, dite_false]
      rfl
    rw [hdef]
    refine ⟨⟨hI, a, ?_⟩, flux_integrable_positive_density _ hdL heL⟩
    filter_upwards [ha, ae_restrict_mem measurableSet_Ioi] with x hax hx
    rw [flux_pwQ_eq_poly_all hpos eps hk i hx]
    have he : (iidLaw ν).real {g | ∀ q, c q * x ≤ d q g} =
        (Q.map (kernelPrefixLower eps k i)).real (Iic x) := by
      rw [map_measureReal_apply hL measurableSet_Iic,
        show Q = (iidLaw ν).restrict S from rfl, measureReal_restrict_apply (hL measurableSet_Iic)]
      congr 1
      ext g
      change (∀ q, c q * x ≤ d q g) ↔ fluxPolyLower c d g ≤ x ∧ g ∈ fluxPolyZeroOK c d
      rw [fluxPoly_iff_halfLine c d h g hx]
      exact and_comm
    rw [he]
    exact hax

end
end PGM
