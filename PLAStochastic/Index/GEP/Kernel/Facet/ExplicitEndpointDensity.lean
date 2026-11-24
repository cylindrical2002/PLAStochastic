import PLAStochastic.Index.GEP.Kernel.Facet.EndpointDensity
import PLAStochastic.Index.GEP.Kernel.Flux.Sections.IntervalPrimitive

/-!
# Explicit positive endpoint densities as actual spatial derivatives

The root pushforward densities are extended by zero off the positive half-line.
They agree almost everywhere with the actual RN derivatives, giving the original
primitive interface and global integrability for finite endpoint measures.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

def fluxPositiveDensity (d : ℝ → ℝ≥0∞) : ℝ → ℝ :=
  (Ioi (0 : ℝ)).indicator (fun x => (d x).toReal)

theorem measurable_fluxPositiveDensity {d : ℝ → ℝ≥0∞} (hd : Measurable d) :
    Measurable (fluxPositiveDensity d) := hd.ennreal_toReal.indicator measurableSet_Ioi

theorem flux_measurable_selected_density (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (eps : ℝ) (k i : ℕ)
    {E : (ℕ → ℝ) → ℝ} (hE : Measurable E) {S : Set (ℕ → ℝ)} (hS : MeasurableSet S)
    {W : (ℕ → ℝ) → ℝ≥0∞} (hW : Measurable W) :
    Measurable (kernelSelectedFacetDensity ν f eps k i E S W) := by
  change Measurable (fun x => kernelSelectedFacetDensity ν f eps k i E S W x)
  simp only [kernelSelectedFacetDensity, tsum_fintype, Finset.sum_apply]
  apply Finset.measurable_sum
  intro q _
  apply measurable_kernelFacetCandidateDensity ν hf eps k i _
  exact hW.indicator (hS.inter (measurableSet_fluxFirstRoot hE (measurable_kernelEnumeratedRoot eps k i) q))

theorem flux_positive_density_eq_rnDeriv (μ : Measure ℝ) {d : ℝ → ℝ≥0∞}
    (hd : Measurable d) (hμ : μ.restrict (Ioi 0) = (volume.restrict (Ioi 0)).withDensity d) :
    fluxEndpointDensity (μ.restrict (Ioi 0)) =ᵐ[volume] fluxPositiveDensity d := by
  have he : μ.restrict (Ioi 0) = volume.withDensity ((Ioi (0 : ℝ)).indicator d) := by
    rw [withDensity_indicator measurableSet_Ioi]
    exact hμ
  have hh := Measure.rnDeriv_withDensity volume (hd.indicator (measurableSet_Ioi (a := (0 : ℝ))))
  filter_upwards [hh] with x hx
  change ((μ.restrict (Ioi 0)).rnDeriv volume x).toReal = _
  rw [he, hx]
  by_cases hx0 : x ∈ Ioi (0 : ℝ)
  · simp only [indicator_of_mem hx0, fluxPositiveDensity]
  · simp only [indicator_of_notMem hx0, ENNReal.toReal_zero, fluxPositiveDensity]

theorem flux_integrable_positive_density (μ : Measure ℝ) [IsFiniteMeasure μ]
    {d : ℝ → ℝ≥0∞} (hd : Measurable d)
    (hμ : μ.restrict (Ioi 0) = (volume.restrict (Ioi 0)).withDensity d) :
    Integrable (fluxPositiveDensity d) :=
  (integrable_fluxEndpointDensity (μ.restrict (Ioi 0))).congr (flux_positive_density_eq_rnDeriv μ hd hμ)

theorem flux_aePrimitive_congr_derivative {J j j' : ℝ → ℝ}
    (hp : AEPrimitive J j) (he : j =ᵐ[volume] j') : AEPrimitive J j' := by
  refine ⟨fun R => (hp.1 R).congr_ae (ae_restrict_of_ae he), hp.2.choose, ?_⟩
  filter_upwards [hp.2.choose_spec] with x hx
  rw [← intervalIntegral.integral_congr_ae_restrict (ae_restrict_of_ae he)]
  exact hx

theorem flux_cdf_explicit_aePrimitive (μ : Measure ℝ) [IsFiniteMeasure μ]
    {d : ℝ → ℝ≥0∞} (hd : Measurable d)
    (hμ : μ.restrict (Ioi 0) = (volume.restrict (Ioi 0)).withDensity d) :
    AEPrimitive (fun x => μ.real (Iic x)) (fluxPositiveDensity d) := by
  have hac : μ.restrict (Ioi 0) ≪ volume := by
    rw [hμ]
    exact (withDensity_absolutelyContinuous _ _).trans Measure.absolutelyContinuous_restrict
  exact flux_aePrimitive_congr_derivative (flux_cdf_aePrimitive_of_ac_positive μ hac)
    (flux_positive_density_eq_rnDeriv μ hd hμ)

/-- Explicit lower-minus-upper density for the actual closed section. -/
theorem flux_closed_section_explicit_aePrimitive {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {L U : Ω → ℝ}
    (hL : Measurable L) (hU : Measurable U) (hLU : ∀ᵐ ω ∂P, L ω ≤ U ω)
    {dL dU : ℝ → ℝ≥0∞} (hdL : Measurable dL) (hdU : Measurable dU)
    (heL : (P.map L).restrict (Ioi 0) = (volume.restrict (Ioi 0)).withDensity dL)
    (heU : (P.map U).restrict (Ioi 0) = (volume.restrict (Ioi 0)).withDensity dU) :
    AEPrimitive (fun x => P.real {ω | L ω ≤ x ∧ x ≤ U ω})
      (fun x => fluxPositiveDensity dL x - fluxPositiveDensity dU x) := by
  have hacL : (P.map L).restrict (Ioi 0) ≪ volume := by
    rw [heL]
    exact (withDensity_absolutelyContinuous _ _).trans Measure.absolutelyContinuous_restrict
  have hacU : (P.map U).restrict (Ioi 0) ≪ volume := by
    rw [heU]
    exact (withDensity_absolutelyContinuous _ _).trans Measure.absolutelyContinuous_restrict
  apply flux_aePrimitive_congr_derivative
    (flux_closed_section_aePrimitive_of_ac_positive P hL hU hLU hacL hacU)
  exact (flux_positive_density_eq_rnDeriv (P.map L) hdL heL).sub
    (flux_positive_density_eq_rnDeriv (P.map U) hdU heU)

end
end PGM
