import PLAStochastic.Index.GEP.Kernel.Flux.Sections.Polyhedron

namespace PGM

noncomputable section

open MeasureTheory Set Filter Finset

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
theorem fluxPolyLower_select (c : ι → ℝ) (d : ι → Ω → ℝ) (ω : Ω)
    (hx : 0 < fluxPolyLower c d ω) : ∃ q, fluxPolyLower c d ω = d q ω / c q := by
  classical
  unfold fluxPolyLower at hx ⊢
  split_ifs at hx ⊢ with h
  · obtain ⟨q, hq, he⟩ := (fluxNeg c).exists_mem_eq_sup' h (fun q => d q ω / c q)
    refine ⟨q, ?_⟩
    rw [he] at hx ⊢
    exact max_eq_right (le_of_lt (by simpa only [lt_max_iff, lt_self_iff_false, false_or] using hx))
  · exact False.elim (lt_irrefl _ hx)

omit [MeasurableSpace Ω] in
theorem fluxPolyUpper_select (c : ι → ℝ) (d : ι → Ω → ℝ)
    (h : (fluxPos c).Nonempty) (ω : Ω) : ∃ q, fluxPolyUpper c d h ω = d q ω / c q := by
  obtain ⟨q, _, he⟩ := (fluxPos c).exists_mem_eq_inf' h (fun q => d q ω / c q)
  exact ⟨q, he⟩

theorem fluxPolyLower_ac_positive (P : Measure Ω) (c : ι → ℝ) {d : ι → Ω → ℝ}
    (hd : ∀ q, Measurable (d q))
    (hac : ∀ q, (P.map (fun ω => d q ω / c q)).restrict (Ioi 0) ≪ volume) :
    (P.map (fluxPolyLower c d)).restrict (Ioi 0) ≪ volume :=
  fluxEndpoint_local_ac_selection P (fun q => (hd q).div_const _)
    (measurable_fluxPolyLower c hd) hac
    (Eventually.of_forall fun ω hx => fluxPolyLower_select c d ω hx)

theorem fluxPolyUpper_ac_positive (P : Measure Ω) (c : ι → ℝ) {d : ι → Ω → ℝ}
    (hd : ∀ q, Measurable (d q))
    (hac : ∀ q, (P.map (fun ω => d q ω / c q)).restrict (Ioi 0) ≪ volume)
    (h : (fluxPos c).Nonempty) :
    (P.map (fluxPolyUpper c d h)).restrict (Ioi 0) ≪ volume :=
  fluxEndpoint_local_ac_selection P (fun q => (hd q).div_const _)
    (measurable_fluxPolyUpper c hd h) hac
    (Eventually.of_forall fun ω _ => fluxPolyUpper_select c d h ω)

/-- Restricting to an active or nonempty-section event preserves the endpoint density. -/
theorem flux_endpoint_restrict_ac_positive (P : Measure Ω) {E : Ω → ℝ} (hE : Measurable E)
    (hac : (P.map E).restrict (Ioi 0) ≪ volume) (S : Set Ω) :
    ((P.restrict S).map E).restrict (Ioi 0) ≪ volume :=
  (Measure.absolutelyContinuous_restrict.map hE).restrict (Ioi 0) |>.trans hac

/-- The nonempty bounded section event, including the zero-coefficient conditions. -/
def fluxPolyActive (c : ι → ℝ) (d : ι → Ω → ℝ) (h : (fluxPos c).Nonempty) : Set Ω :=
  fluxPolyZeroOK c d ∩ {ω | fluxPolyLower c d ω ≤ fluxPolyUpper c d h ω}

theorem measurableSet_fluxPolyActive (c : ι → ℝ) {d : ι → Ω → ℝ}
    (hd : ∀ q, Measurable (d q)) (h : (fluxPos c).Nonempty) :
    MeasurableSet (fluxPolyActive c d h) :=
  (measurableSet_fluxPolyZeroOK c hd).inter
    (measurableSet_le (measurable_fluxPolyLower c hd) (measurable_fluxPolyUpper c hd h))

/-- Total mass of a positive-local endpoint density is bounded by the mass of
the underlying finite measure; no density smoothness is used. -/
theorem flux_endpoint_density_mass_le (P : Measure Ω) [IsFiniteMeasure P]
    {E : Ω → ℝ} (hE : Measurable E) :
    (∫ x, ‖fluxEndpointDensity ((P.map E).restrict (Ioi 0)) x‖) ≤ P.real univ := by
  have he : (fun x => ‖fluxEndpointDensity ((P.map E).restrict (Ioi 0)) x‖) =
      fluxEndpointDensity ((P.map E).restrict (Ioi 0)) := by
    funext x
    exact Real.norm_of_nonneg ENNReal.toReal_nonneg
  rw [he]
  unfold fluxEndpointDensity
  rw [Measure.integral_toReal_rnDeriv']
  calc
    _ ≤ ((P.map E).restrict (Ioi 0)).real univ := sub_le_self _ measureReal_nonneg
    _ = (P.map E).real (Ioi 0) := measureReal_restrict_apply_univ _
    _ ≤ (P.map E).real univ := measureReal_mono (subset_univ _)
    _ = P.real univ := by rw [map_measureReal_apply hE MeasurableSet.univ, preimage_univ]

theorem flux_endpoint_difference_mass_le (P : Measure Ω) [IsFiniteMeasure P]
    {L U : Ω → ℝ} (hL : Measurable L) (hU : Measurable U) :
    (∫ x, ‖fluxEndpointDensity ((P.map L).restrict (Ioi 0)) x -
      fluxEndpointDensity ((P.map U).restrict (Ioi 0)) x‖) ≤ 2 * P.real univ := by
  have hI₁ := integrable_fluxEndpointDensity ((P.map L).restrict (Ioi 0))
  have hI₂ := integrable_fluxEndpointDensity ((P.map U).restrict (Ioi 0))
  calc
    _ ≤ ∫ x, ‖fluxEndpointDensity ((P.map L).restrict (Ioi 0)) x‖ +
        ‖fluxEndpointDensity ((P.map U).restrict (Ioi 0)) x‖ :=
      integral_mono (hI₁.sub hI₂).norm (hI₁.norm.add hI₂.norm) (fun x => norm_sub_le _ _)
    _ = (∫ x, ‖fluxEndpointDensity ((P.map L).restrict (Ioi 0)) x‖) +
        (∫ x, ‖fluxEndpointDensity ((P.map U).restrict (Ioi 0)) x‖) := integral_add hI₁.norm hI₂.norm
    _ ≤ 2 * P.real univ := by
      linarith [flux_endpoint_density_mass_le P hL, flux_endpoint_density_mass_le P hU]

/-- Every finite system of affine inequalities with positive-local absolutely
continuous roots has an actual a.e. derivative for its section probability.
The half-line case is proved separately, rather than inserting an artificial finite endpoint. -/
theorem fluxPoly_aePrimitive (P : Measure Ω) [IsFiniteMeasure P]
    (c : ι → ℝ) {d : ι → Ω → ℝ} (hd : ∀ q, Measurable (d q))
    (hac : ∀ q, (P.map (fun ω => d q ω / c q)).restrict (Ioi 0) ≪ volume) :
    ∃ j : ℝ → ℝ, AEPrimitive (fun x => P.real {ω | ∀ q, c q * x ≤ d q ω}) j ∧
      Integrable j ∧ (∫ x, ‖j x‖) ≤ 2 * P.real univ := by
  classical
  have hL := measurable_fluxPolyLower c hd
  have hacL := fluxPolyLower_ac_positive P c hd hac
  by_cases h : (fluxPos c).Nonempty
  · let S := fluxPolyActive c d h
    let Q := P.restrict S
    have hS : MeasurableSet S := measurableSet_fluxPolyActive c hd h
    have hU := measurable_fluxPolyUpper c hd h
    have hacLQ := flux_endpoint_restrict_ac_positive P hL hacL S
    have hacUQ := flux_endpoint_restrict_ac_positive P hU (fluxPolyUpper_ac_positive P c hd hac h) S
    have horder : ∀ᵐ ω ∂Q, fluxPolyLower c d ω ≤ fluxPolyUpper c d h ω := by
      filter_upwards [ae_restrict_mem hS] with ω hω
      exact hω.2
    let j := fun x => fluxEndpointDensity ((Q.map (fluxPolyLower c d)).restrict (Ioi 0)) x -
      fluxEndpointDensity ((Q.map (fluxPolyUpper c d h)).restrict (Ioi 0)) x
    have hj : Integrable j := (integrable_fluxEndpointDensity _).sub (integrable_fluxEndpointDensity _)
    have hb : (∫ x, ‖j x‖) ≤ 2 * P.real univ := by
      refine (flux_endpoint_difference_mass_le Q hL hU).trans ?_
      rw [show Q = P.restrict S from rfl, measureReal_restrict_apply_univ]
      exact mul_le_mul_of_nonneg_left (measureReal_mono (subset_univ S)) (by norm_num)
    obtain ⟨hI, a, ha⟩ := flux_closed_section_aePrimitive_of_ac_positive Q hL hU horder hacLQ hacUQ
    refine ⟨j, ⟨hI, a, ?_⟩, hj, hb⟩
    filter_upwards [ha, ae_restrict_mem measurableSet_Ioi] with x hax hx
    have he : P.real {ω | ∀ q, c q * x ≤ d q ω} =
        Q.real {ω | fluxPolyLower c d ω ≤ x ∧ x ≤ fluxPolyUpper c d h ω} := by
      have hm : MeasurableSet {ω | fluxPolyLower c d ω ≤ x ∧ x ≤ fluxPolyUpper c d h ω} :=
        (measurableSet_le hL measurable_const).inter (measurableSet_le measurable_const hU)
      rw [show Q = P.restrict S from rfl, measureReal_restrict_apply hm]
      congr 1
      ext ω
      change (∀ q, c q * x ≤ d q ω) ↔
        ((fluxPolyLower c d ω ≤ x ∧ x ≤ fluxPolyUpper c d h ω) ∧
          (ω ∈ fluxPolyZeroOK c d ∧ fluxPolyLower c d ω ≤ fluxPolyUpper c d h ω))
      rw [fluxPoly_iff_interval c d h ω hx]
      constructor
      · rintro ⟨hz, hl, hu⟩
        exact ⟨⟨hl, hu⟩, hz, hl.trans hu⟩
      · rintro ⟨⟨hl, hu⟩, hz, _⟩
        exact ⟨hz, hl, hu⟩
    rw [he]
    exact hax
  · let S := fluxPolyZeroOK c d
    let Q := P.restrict S
    have hS : MeasurableSet S := measurableSet_fluxPolyZeroOK c hd
    have hacLQ := flux_endpoint_restrict_ac_positive P hL hacL S
    let j := fluxEndpointDensity ((Q.map (fluxPolyLower c d)).restrict (Ioi 0))
    have hj : Integrable j := integrable_fluxEndpointDensity _
    have hb : (∫ x, ‖j x‖) ≤ 2 * P.real univ := by
      refine (flux_endpoint_density_mass_le Q hL).trans ?_
      rw [show Q = P.restrict S from rfl, measureReal_restrict_apply_univ]
      have hm : P.real S ≤ P.real univ := measureReal_mono (subset_univ S)
      linarith [measureReal_nonneg (μ := P) (s := univ)]
    obtain ⟨hI, a, ha⟩ := flux_cdf_aePrimitive_of_ac_positive (Q.map (fluxPolyLower c d)) hacLQ
    refine ⟨j, ⟨hI, a, ?_⟩, hj, hb⟩
    filter_upwards [ha, ae_restrict_mem measurableSet_Ioi] with x hax hx
    have he : P.real {ω | ∀ q, c q * x ≤ d q ω} =
        (Q.map (fluxPolyLower c d)).real (Iic x) := by
      rw [map_measureReal_apply hL measurableSet_Iic,
        measureReal_restrict_apply (hL measurableSet_Iic)]
      congr 1
      ext ω
      change (∀ q, c q * x ≤ d q ω) ↔ fluxPolyLower c d ω ≤ x ∧ ω ∈ fluxPolyZeroOK c d
      rw [fluxPoly_iff_halfLine c d h ω hx]
      exact and_comm
    rw [he]
    exact hax

end

end PGM
