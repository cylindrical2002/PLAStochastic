import PLAStochastic.Index.GEP.Kernel.Influence.Coarea.OrientedFacets
import PLAStochastic.Index.GEP.Kernel.Influence.Pins.NonDirac
import PLAStochastic.Index.GEP.Kernel.Influence.Pins.DiracPins

/-! # Every original active facet as physical rows and pins, including Dirac -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option maxHeartbeats 1200000

def kernelIFLeftDiracPinDensity (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (eps : ℝ)
    {k : ℕ} (q : FluxFacetIndex k) (W : (ℕ → ℝ) → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (kernelFacetQ eps q/x) *
    ((∫⁻ g, ENNReal.ofReal (kernelIFOuterSurvival eps (kernelFacetP eps q/x) q g) * W g ∂iidLaw ν) *
      ENNReal.ofReal (krDens (Icc 0 (2*eps)) ν f 1 (kernelFacetP eps q/x)
        (q.2.2.1-q.2.1) (eps+fluxFacetSign q*eps) (eps-fluxFacetSign q*eps)))

def kernelIFRightDiracPinDensity (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (eps : ℝ)
    {k : ℕ} (q : FluxFacetIndex k) (W : (ℕ → ℝ) → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (kernelFacetP eps q/x) *
    ((∫⁻ g, ENNReal.ofReal (kernelIFOuterSurvival eps (kernelFacetQ eps q/x) q g) * W g ∂iidLaw ν) *
      ENNReal.ofReal (krDens (Icc 0 (2*eps)) ν f 1 (kernelFacetQ eps q/x)
        (q.2.1-q.1) (eps-fluxFacetSign q*eps) (eps+fluxFacetSign q*eps)))

/-- The zero-zero marked bridge uses its actual deterministic-root density.
All other cases use the full marked density, with both short random sides. -/
def kernelIFFacetPinDensity (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (eps : ℝ)
    {k : ℕ} (q : FluxFacetIndex k) (i : ℕ) (W : (ℕ → ℝ) → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ := by
  classical
  exact if kernelFacetEffective eps q then
    if (q.1 : ℕ) ≤ i ∧ i < q.2.1 then
      if (q.1 : ℕ)+1 < q.2.1 then kernelIFLeftPinDensity ν f eps q i W x
      else kernelIFLeftDiracPinDensity ν f eps q W x
    else if (q.2.1 : ℕ) ≤ i ∧ i < q.2.2.1 then
      if (q.2.1 : ℕ)+1 < q.2.2.1 then kernelIFRightPinDensity ν f eps q i W x
      else kernelIFRightDiracPinDensity ν f eps q W x
    else 0
  else 0

theorem kernel_IF_activeWeight_zero_of_ineffective {eps : ℝ} {k i : ℕ}
    (hi : i < k) (q : FluxFacetIndex k) (hne : ¬kernelFacetEffective eps q)
    (W : (ℕ → ℝ) → ℝ≥0∞) : kernelIFActiveWeight eps k i q W = 0 := by
  funext g
  apply indicator_of_notMem
  intro hg
  have hx := hg.1 i hi
  rw [Function.update_self] at hx
  apply hne
  apply kernel_active_root_effective hi q g hx
  · intro j hj hji
    simpa only [Function.update_of_ne hji] using hg.1 j hj
  · rfl

theorem kernel_IF_activeWeight_zero_of_coef_zero {eps : ℝ} {k i : ℕ}
    (hi : i < k) (q : FluxFacetIndex k) (hc : fluxFacetCoef eps q i = 0)
    (W : (ℕ → ℝ) → ℝ≥0∞) : kernelIFActiveWeight eps k i q W = 0 := by
  funext g
  apply indicator_of_notMem
  intro hg
  have hx := hg.1 i hi
  simp only [Function.update_self, kernelFacetRoot, hc, div_zero, lt_self_iff_false] at hx

/-- One common density represents every original facet, including ineffective
facets, exterior marks, either orientation, and the true one-gap Dirac case. -/
theorem kernel_IF_candidate_facet_pins_ae (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} {D : ℝ} (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u)
    (hfD : ∀ u, f u ≤ D) (hfneg : ∀ u, u ≤ 0 → f u = 0)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun u => ENNReal.ofReal (f u)))
    (hpos : ∀ᵐ u ∂(ν : Measure ℝ), 0 < u)
    {eps : ℝ} (heps : 0 ≤ eps) {k i : ℕ} (hi : i < k) (q : FluxFacetIndex k)
    {W : (ℕ → ℝ) → ℝ≥0∞}
    (hW : Measurable[kCoordSigma (Iio (q.1 : ℕ) ∪ Ici (q.2.2.1 : ℕ))] W) :
    kernelFacetCandidateDensity ν (fun u => ENNReal.ofReal (f u)) eps k i q
      (kernelIFActiveWeight eps k i q W) =ᵐ[volume.restrict (Ioi 0)]
        kernelIFFacetPinDensity ν f eps q i W := by
  classical
  unfold kernelIFFacetPinDensity
  have hWm : Measurable W := hW.mono (kCoordSigma_le _) le_rfl
  by_cases hq : kernelFacetEffective eps q
  · by_cases hl : (q.1 : ℕ) ≤ i ∧ i < q.2.1
    · by_cases hlong : (q.1 : ℕ)+1 < q.2.1
      · simpa only [if_pos hq, if_pos hl, if_pos hlong] using
          kernel_IF_left_candidate_pins_ae ν hf hf0 hfD hfneg hν hpos hq hlong hl.1 hl.2 hW
      · have hshort : (q.1 : ℕ)+1 = q.2.1 := by have := hq.1.1; omega
        have hiq : i = q.1 := by omega
        subst i
        have hst := hq.1.2
        have hh := kernel_IF_left_short_candidate_ae ν hf.ennreal_ofReal hν hq hshort
          (m := (q.2.2.1 : ℕ)-1) (by omega) (by omega) hWm
        filter_upwards [hh, ae_restrict_mem measurableSet_Ioi] with x hx hxp
        rw [hx]
        simpa only [if_pos hq, if_pos hl, if_neg hlong, kernelIFLeftDiracPinDensity] using
          kernel_IF_left_short_density_pins ν hf hf0 hfD hfneg hpos hq hshort heps hxp hW
    · by_cases hr : (q.2.1 : ℕ) ≤ i ∧ i < q.2.2.1
      · by_cases hlong : (q.2.1 : ℕ)+1 < q.2.2.1
        · simpa only [if_pos hq, if_neg hl, if_pos hr, if_pos hlong] using
            kernel_IF_right_candidate_pins_ae ν hf hf0 hfD hfneg hν hpos hq hlong hr.1 hr.2 hW
        · have hshort : (q.2.1 : ℕ)+1 = q.2.2.1 := by have := hq.1.2; omega
          have hiq : i = q.2.1 := by omega
          subst i
          have hrs := hq.1.1
          have hh := kernel_IF_right_short_candidate_ae ν hf.ennreal_ofReal hν hq hshort
            (m := (q.2.1 : ℕ)-1) (by omega) (by omega) hWm
          filter_upwards [hh, ae_restrict_mem measurableSet_Ioi] with x hx hxp
          rw [hx]
          simpa only [if_pos hq, if_neg hl, if_pos hr, if_neg hlong, kernelIFRightDiracPinDensity] using
            kernel_IF_right_short_density_pins ν hf hf0 hfD hfneg hpos hq hshort heps hxp hW
      · have hc : fluxFacetCoef eps q i = 0 :=
          kernel_facet_coef_eq_zero_outside (by have := hq.1.1; have := hq.1.2; omega)
        rw [kernel_IF_activeWeight_zero_of_coef_zero hi q hc, Pi.zero_def,
          kernel_facet_candidate_density_zero]
        exact Eventually.of_forall fun x => by
          simp only [if_pos hq, if_neg hl, if_neg hr, Pi.zero_apply]
  · rw [kernel_IF_activeWeight_zero_of_ineffective hi q hq, Pi.zero_def,
      kernel_facet_candidate_density_zero]
    exact Eventually.of_forall fun x => by
      simp only [if_neg hq, Pi.zero_apply]

end
end PGM
