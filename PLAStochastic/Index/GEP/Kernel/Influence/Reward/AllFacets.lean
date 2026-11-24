import PLAStochastic.Index.GEP.Kernel.Influence.Reward.TotalSum

/-! # Every original active facet with an arbitrary measurable total-sum reward -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option maxHeartbeats 1200000

def kernelIFFacetTotalPinDensity (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (eps : ℝ)
    {k : ℕ} (q : FluxFacetIndex k) (i : ℕ) (H : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ := by
  classical
  exact if kernelFacetEffective eps q then
    if (q.1 : ℕ) ≤ i ∧ i < q.2.1 then
      if (q.1 : ℕ)+1 < q.2.1 then kernelIFLeftTotalPinDensity ν f eps q i H x
      else kernelIFLeftTotalDiracPinDensity ν f eps q H x
    else if (q.2.1 : ℕ) ≤ i ∧ i < q.2.2.1 then
      if (q.2.1 : ℕ)+1 < q.2.2.1 then kernelIFRightTotalPinDensity ν f eps q i H x
      else kernelIFRightTotalDiracPinDensity ν f eps q H x
    else 0
  else 0

theorem kernel_IF_total_candidate_facet_pins_ae (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} {D : ℝ} (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u)
    (hfD : ∀ u, f u ≤ D) (hfneg : ∀ u, u ≤ 0 → f u = 0)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun u => ENNReal.ofReal (f u)))
    (hpos : ∀ᵐ u ∂(ν : Measure ℝ), 0 < u)
    {eps : ℝ} (heps : 0 ≤ eps) {k i : ℕ} (hi : i < k) (q : FluxFacetIndex k)
    {H : ℝ → ℝ≥0∞} (hH : Measurable H) :
    kernelFacetCandidateDensity ν (fun u => ENNReal.ofReal (f u)) eps k i q
      (kernelIFActiveWeight eps k i q (fun g => H (gapKeys g k))) =ᵐ[volume.restrict (Ioi 0)]
        kernelIFFacetTotalPinDensity ν f eps q i H := by
  classical
  unfold kernelIFFacetTotalPinDensity
  have hWm : Measurable (fun g : ℕ → ℝ => H (gapKeys g k)) := hH.comp (by unfold gapKeys; fun_prop)
  by_cases hq : kernelFacetEffective eps q
  · by_cases hl : (q.1 : ℕ) ≤ i ∧ i < q.2.1
    · by_cases hlong : (q.1 : ℕ)+1 < q.2.1
      · simpa only [if_pos hq, if_pos hl, if_pos hlong] using
          kernel_IF_left_total_candidate_pins_ae ν hf hf0 hfD hfneg hν hpos hq hlong hl.1 hl.2 hH
      · have hshort : (q.1 : ℕ)+1 = q.2.1 := by have := hq.1.1; omega
        have hiq : i = q.1 := by omega
        subst i
        have hst := hq.1.2
        have hh := kernel_IF_left_short_candidate_ae ν hf.ennreal_ofReal hν hq hshort
          (m := (q.2.2.1 : ℕ)-1) (by omega) (by omega) hWm
        filter_upwards [hh, ae_restrict_mem measurableSet_Ioi] with x hx hxp
        rw [hx]
        simpa only [if_pos hq, if_pos hl, if_neg hlong, kernelIFLeftTotalDiracPinDensity] using
          kernel_IF_left_total_short_density_pins ν hf hf0 hfD hfneg hpos hq hshort heps hxp hH
    · by_cases hr : (q.2.1 : ℕ) ≤ i ∧ i < q.2.2.1
      · by_cases hlong : (q.2.1 : ℕ)+1 < q.2.2.1
        · simpa only [if_pos hq, if_neg hl, if_pos hr, if_pos hlong] using
            kernel_IF_right_total_candidate_pins_ae ν hf hf0 hfD hfneg hν hpos hq hlong hr.1 hr.2 hH
        · have hshort : (q.2.1 : ℕ)+1 = q.2.2.1 := by have := hq.1.2; omega
          have hiq : i = q.2.1 := by omega
          subst i
          have hrs := hq.1.1
          have hh := kernel_IF_right_short_candidate_ae ν hf.ennreal_ofReal hν hq hshort
            (m := (q.2.1 : ℕ)-1) (by omega) (by omega) hWm
          filter_upwards [hh, ae_restrict_mem measurableSet_Ioi] with x hx hxp
          rw [hx]
          simpa only [if_pos hq, if_neg hl, if_pos hr, if_neg hlong, kernelIFRightTotalDiracPinDensity] using
            kernel_IF_right_total_short_density_pins ν hf hf0 hfD hfneg hpos hq hshort heps hxp hH
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
