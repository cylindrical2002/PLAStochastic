import PLAStochastic.Index.GEP.Response.Defs
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

/-!
# WP4: the a.e. primitive of a random interval section

A random interval `[L,U)` has probability equal to the difference of the two
endpoint CDFs. If the endpoint pushforwards are absolutely continuous, its actual
derivative is the difference of their Radon–Nikodym densities. This yields
`AEPrimitive`, not just pointwise differentiability. The theorem permits arbitrary
finite measures, so one can restrict to an individual active-facet event.

This file does not construct the endpoints of the PLA feasible section or prove
their absolute continuity. Those are geometric obligations of the flux proof.
-/

namespace PGM

noncomputable section

open MeasureTheory Set Filter

/-- The real Radon–Nikodym density of an endpoint law. -/
def fluxEndpointDensity (μ : Measure ℝ) (x : ℝ) : ℝ := (μ.rnDeriv volume x).toReal

theorem integrable_fluxEndpointDensity (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (fluxEndpointDensity μ) := Measure.integrable_toReal_rnDeriv

/-- The CDF of an absolutely continuous finite measure is an integral primitive
of its actual Radon–Nikodym density, on both sides of zero. -/
theorem flux_cdf_eq_integral (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : μ ≪ volume) (x : ℝ) :
    μ.real (Iic x) = μ.real (Iic 0) + ∫ t in (0 : ℝ)..x, fluxEndpointDensity μ t := by
  have hi := integrable_fluxEndpointDensity μ
  have h0 : (∫ t in Iic (0 : ℝ), fluxEndpointDensity μ t) = μ.real (Iic 0) :=
    Measure.setIntegral_toReal_rnDeriv hμ _
  have hx : (∫ t in Iic x, fluxEndpointDensity μ t) = μ.real (Iic x) :=
    Measure.setIntegral_toReal_rnDeriv hμ _
  have hh := intervalIntegral.integral_Iic_sub_Iic
    (hi.integrableOn (s := Iic (0 : ℝ))) (hi.integrableOn (s := Iic x))
  rw [h0, hx] at hh
  linarith

theorem flux_cdf_aePrimitive (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : μ ≪ volume) :
    AEPrimitive (fun x => μ.real (Iic x)) (fluxEndpointDensity μ) := by
  refine ⟨fun R => (integrable_fluxEndpointDensity μ).intervalIntegrable, μ.real (Iic 0), ?_⟩
  exact Eventually.of_forall (flux_cdf_eq_integral μ hμ)

/-- For a primitive on `(0,∞)`, only the positive part of the endpoint law
needs a density. In particular, a fixed endpoint at zero is allowed. -/
theorem flux_cdf_aePrimitive_of_ac_positive (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : μ.restrict (Ioi 0) ≪ volume) :
    AEPrimitive (fun x => μ.real (Iic x)) (fluxEndpointDensity (μ.restrict (Ioi 0))) := by
  have hi := integrable_fluxEndpointDensity (μ.restrict (Ioi 0))
  refine ⟨fun R => hi.intervalIntegrable, μ.real (Iic 0), ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 ≤ x := le_of_lt hx
  have hsplit := measureReal_union (μ := μ) (Iic_disjoint_Ioc (a := (0 : ℝ)) le_rfl)
    (measurableSet_Ioc (a := (0 : ℝ)) (b := x))
  rw [Iic_union_Ioc_eq_Iic hx0] at hsplit
  have hc := flux_cdf_eq_integral (μ.restrict (Ioi 0)) hμ x
  have hz : (μ.restrict (Ioi 0)).real (Iic 0) = 0 := by
    rw [measureReal_restrict_apply measurableSet_Iic, inter_comm, Ioi_inter_Iic]
    simp
  have hp : (μ.restrict (Ioi 0)).real (Iic x) = μ.real (Ioc 0 x) := by
    rw [measureReal_restrict_apply measurableSet_Iic, inter_comm, Ioi_inter_Iic]
  rw [hz, zero_add, hp] at hc
  rw [← hc]
  exact hsplit

/-- The difference of endpoint CDFs has the difference of endpoint densities as
an a.e. primitive; all normalization constants are retained. -/
theorem flux_cdf_sub_aePrimitive (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ ≪ volume) (hν : ν ≪ volume) :
    AEPrimitive (fun x => μ.real (Iic x) - ν.real (Iic x))
      (fun x => fluxEndpointDensity μ x - fluxEndpointDensity ν x) := by
  have hIμ := integrable_fluxEndpointDensity μ
  have hIν := integrable_fluxEndpointDensity ν
  refine ⟨fun R => (hIμ.sub hIν).intervalIntegrable, μ.real (Iic 0) - ν.real (Iic 0), ?_⟩
  apply Eventually.of_forall
  intro x
  dsimp only
  rw [intervalIntegral.integral_sub hIμ.intervalIntegrable hIν.intervalIntegrable,
    flux_cdf_eq_integral μ hμ x, flux_cdf_eq_integral ν hν x]
  ring

/-- Local positive-half-line version of the difference-of-CDF primitive. -/
theorem flux_cdf_sub_aePrimitive_of_ac_positive (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ.restrict (Ioi 0) ≪ volume) (hν : ν.restrict (Ioi 0) ≪ volume) :
    AEPrimitive (fun x => μ.real (Iic x) - ν.real (Iic x))
      (fun x => fluxEndpointDensity (μ.restrict (Ioi 0)) x -
        fluxEndpointDensity (ν.restrict (Ioi 0)) x) := by
  obtain ⟨hIμ, cμ, hcμ⟩ := flux_cdf_aePrimitive_of_ac_positive μ hμ
  obtain ⟨hIν, cν, hcν⟩ := flux_cdf_aePrimitive_of_ac_positive ν hν
  refine ⟨fun R => (hIμ R).sub (hIν R), cμ - cν, ?_⟩
  filter_upwards [hcμ, hcν] with x hxμ hxν
  rw [hxμ, hxν, intervalIntegral.integral_sub (hIμ x) (hIν x)]
  ring

/-- The probability (or finite mass) that a point belongs to a random half-open interval. -/
def fluxSectionMass {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (L U : Ω → ℝ) (x : ℝ) : ℝ := P.real {ω | L ω ≤ x ∧ x < U ω}

/-- Exact interval/CDF identity; endpoint order need hold only almost everywhere. -/
theorem fluxSectionMass_eq_cdf_sub {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {L U : Ω → ℝ}
    (hL : Measurable L) (hU : Measurable U) (hLU : ∀ᵐ ω ∂P, L ω ≤ U ω) (x : ℝ) :
    fluxSectionMass P L U x = (P.map L).real (Iic x) - (P.map U).real (Iic x) := by
  have he : {ω | L ω ≤ x ∧ x < U ω} = (L ⁻¹' Iic x) \ (U ⁻¹' Iic x) := by
    ext ω
    simp only [mem_ofPred_eq, Set.mem_sdiff, mem_preimage, mem_Iic, not_le]
  have hu : ((L ⁻¹' Iic x) ∪ (U ⁻¹' Iic x) : Set Ω) =ᵐ[P] L ⁻¹' Iic x := by
    refine hLU.mono fun ω hω => ?_
    change (ω ∈ (L ⁻¹' Iic x) ∪ (U ⁻¹' Iic x)) = (ω ∈ L ⁻¹' Iic x)
    simp only [mem_union, mem_preimage, mem_Iic]
    exact propext ⟨fun h => h.elim id (hω.trans ·), Or.inl⟩
  rw [fluxSectionMass, he, measureReal_sdiff' (hU measurableSet_Iic), measureReal_congr hu,
    map_measureReal_apply hL measurableSet_Iic, map_measureReal_apply hU measurableSet_Iic]

/-- The actual random-section mass has derivative given by the two endpoint
Radon–Nikodym densities. Absolute continuity is required of the endpoint laws,
not of a conveniently substituted kernel. -/
theorem fluxSectionMass_aePrimitive {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {L U : Ω → ℝ}
    (hL : Measurable L) (hU : Measurable U) (hLU : ∀ᵐ ω ∂P, L ω ≤ U ω)
    (hacL : P.map L ≪ volume) (hacU : P.map U ≪ volume) :
    AEPrimitive (fluxSectionMass P L U)
      (fun x => fluxEndpointDensity (P.map L) x - fluxEndpointDensity (P.map U) x) := by
  have he : fluxSectionMass P L U =
      (fun x => (P.map L).real (Iic x) - (P.map U).real (Iic x)) :=
    funext (fluxSectionMass_eq_cdf_sub P hL hU hLU)
  rw [he]
  exact flux_cdf_sub_aePrimitive (P.map L) (P.map U) hacL hacU

/-- The random-section primitive also allows atoms at the fixed endpoint zero. -/
theorem fluxSectionMass_aePrimitive_of_ac_positive {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {L U : Ω → ℝ}
    (hL : Measurable L) (hU : Measurable U) (hLU : ∀ᵐ ω ∂P, L ω ≤ U ω)
    (hacL : (P.map L).restrict (Ioi 0) ≪ volume)
    (hacU : (P.map U).restrict (Ioi 0) ≪ volume) :
    AEPrimitive (fluxSectionMass P L U)
      (fun x => fluxEndpointDensity ((P.map L).restrict (Ioi 0)) x -
        fluxEndpointDensity ((P.map U).restrict (Ioi 0)) x) := by
  have he : fluxSectionMass P L U =
      (fun x => (P.map L).real (Iic x) - (P.map U).real (Iic x)) :=
    funext (fluxSectionMass_eq_cdf_sub P hL hU hLU)
  rw [he]
  exact flux_cdf_sub_aePrimitive_of_ac_positive (P.map L) (P.map U) hacL hacU

/-- Closing the upper endpoint does not change section mass when its law is
absolutely continuous. This applies at every fixed spatial point. -/
theorem flux_closed_section_eq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {L U : Ω → ℝ} (hU : Measurable U)
    (hacU : P.map U ≪ volume) (x : ℝ) :
    P.real {ω | L ω ≤ x ∧ x ≤ U ω} = fluxSectionMass P L U x := by
  have hnull : P (U ⁻¹' {x}) = 0 := by
    rw [← Measure.map_apply hU (measurableSet_singleton x)]
    exact hacU (Real.volume_singleton)
  apply measureReal_congr
  refine (measure_eq_zero_iff_ae_notMem.mp hnull).mono fun ω hω => ?_
  change (L ω ≤ x ∧ x ≤ U ω) = (L ω ≤ x ∧ x < U ω)
  have hne : U ω ≠ x := hω
  exact propext ⟨fun h => ⟨h.1, lt_of_le_of_ne h.2 hne.symm⟩,
    fun h => ⟨h.1, h.2.le⟩⟩

/-- The closed-section version matches the convention for feasible PLA prefixes. -/
theorem flux_closed_section_aePrimitive {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {L U : Ω → ℝ}
    (hL : Measurable L) (hU : Measurable U) (hLU : ∀ᵐ ω ∂P, L ω ≤ U ω)
    (hacL : P.map L ≪ volume) (hacU : P.map U ≪ volume) :
    AEPrimitive (fun x => P.real {ω | L ω ≤ x ∧ x ≤ U ω})
      (fun x => fluxEndpointDensity (P.map L) x - fluxEndpointDensity (P.map U) x) := by
  have he : (fun x => P.real {ω | L ω ≤ x ∧ x ≤ U ω}) = fluxSectionMass P L U :=
    funext (flux_closed_section_eq P hU hacU)
  rw [he]
  exact fluxSectionMass_aePrimitive P hL hU hLU hacL hacU

/-- At a positive spatial point, a possible atom at endpoint zero does not
affect the closed/half-open section identity. -/
theorem flux_closed_section_eq_of_ac_positive {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {L U : Ω → ℝ} (hU : Measurable U)
    (hacU : (P.map U).restrict (Ioi 0) ≪ volume) {x : ℝ} (hx : 0 < x) :
    P.real {ω | L ω ≤ x ∧ x ≤ U ω} = fluxSectionMass P L U x := by
  have hnull : P (U ⁻¹' {x}) = 0 := by
    rw [← Measure.map_apply hU (measurableSet_singleton x)]
    have hxx : ({x} : Set ℝ) ∩ Ioi 0 = {x} :=
      inter_eq_left.mpr (singleton_subset_iff.mpr hx)
    have hh := hacU (Real.volume_singleton (a := x))
    rwa [Measure.restrict_apply (measurableSet_singleton x), hxx] at hh
  apply measureReal_congr
  refine (measure_eq_zero_iff_ae_notMem.mp hnull).mono fun ω hω => ?_
  change (L ω ≤ x ∧ x ≤ U ω) = (L ω ≤ x ∧ x < U ω)
  have hne : U ω ≠ x := hω
  exact propext ⟨fun h => ⟨h.1, lt_of_le_of_ne h.2 hne.symm⟩,
    fun h => ⟨h.1, h.2.le⟩⟩

/-- Closed random sections have the desired primitive under positive-local
absolute continuity, including the degenerate interval `[0,0]`. -/
theorem flux_closed_section_aePrimitive_of_ac_positive {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {L U : Ω → ℝ}
    (hL : Measurable L) (hU : Measurable U) (hLU : ∀ᵐ ω ∂P, L ω ≤ U ω)
    (hacL : (P.map L).restrict (Ioi 0) ≪ volume)
    (hacU : (P.map U).restrict (Ioi 0) ≪ volume) :
    AEPrimitive (fun x => P.real {ω | L ω ≤ x ∧ x ≤ U ω})
      (fun x => fluxEndpointDensity ((P.map L).restrict (Ioi 0)) x -
        fluxEndpointDensity ((P.map U).restrict (Ioi 0)) x) := by
  obtain ⟨hI, c, hc⟩ := fluxSectionMass_aePrimitive_of_ac_positive P hL hU hLU hacL hacU
  refine ⟨hI, c, ?_⟩
  filter_upwards [hc, ae_restrict_mem measurableSet_Ioi] with x hcx hx
  rw [flux_closed_section_eq_of_ac_positive P hU hacU hx]
  exact hcx

/-- A measurable endpoint selected from countably many absolutely continuous
candidate endpoints still has an absolutely continuous law. Selection may depend
arbitrarily on the whole sample; no independence of the selector is required. -/
theorem fluxEndpoint_ac_of_countable_selection {Ω ι : Type*} [MeasurableSpace Ω]
    [Countable ι] (P : Measure Ω) {F : ι → Ω → ℝ} {E : Ω → ℝ}
    (hF : ∀ i, Measurable (F i)) (hE : Measurable E)
    (hac : ∀ i, P.map (F i) ≪ volume)
    (hsel : ∀ᵐ ω ∂P, ∃ i, E ω = F i ω) : P.map E ≪ volume := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hs0
  rw [Measure.map_apply hE hs]
  apply measure_eq_zero_iff_ae_notMem.mpr
  have havoid : ∀ᵐ ω ∂P, ∀ i, F i ω ∉ s := by
    rw [ae_all_iff]
    intro i
    have hi : P ((F i) ⁻¹' s) = 0 := by
      rw [← Measure.map_apply (hF i) hs]
      exact hac i hs0
    exact measure_eq_zero_iff_ae_notMem.mp hi
  filter_upwards [havoid, hsel] with ω hω ⟨i, hi⟩
  change E ω ∉ s
  rw [hi]
  exact hω i

/-- A fixed zero endpoint causes no difficulty on the open positive half-line:
only positive selected values must come from the absolutely continuous candidates. -/
theorem fluxEndpoint_ac_positive_of_countable_selection {Ω ι : Type*} [MeasurableSpace Ω]
    [Countable ι] (P : Measure Ω) {F : ι → Ω → ℝ} {E : Ω → ℝ}
    (hF : ∀ i, Measurable (F i)) (hE : Measurable E)
    (hac : ∀ i, P.map (F i) ≪ volume)
    (hsel : ∀ᵐ ω ∂P, 0 < E ω → ∃ i, E ω = F i ω) :
    (P.map E).restrict (Ioi 0) ≪ volume := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hs0
  rw [Measure.restrict_apply hs, Measure.map_apply hE (hs.inter measurableSet_Ioi)]
  apply measure_eq_zero_iff_ae_notMem.mpr
  have havoid : ∀ᵐ ω ∂P, ∀ i, F i ω ∉ s := by
    rw [ae_all_iff]
    intro i
    have hi : P ((F i) ⁻¹' s) = 0 := by
      rw [← Measure.map_apply (hF i) hs]
      exact hac i hs0
    exact measure_eq_zero_iff_ae_notMem.mp hi
  filter_upwards [havoid, hsel] with ω hω hselω
  rintro ⟨hsω, hpos⟩
  obtain ⟨i, hi⟩ := hselω hpos
  exact hω i (hi ▸ hsω)

end

end PGM
