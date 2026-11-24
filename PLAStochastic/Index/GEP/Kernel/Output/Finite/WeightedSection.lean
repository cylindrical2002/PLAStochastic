import PLAStochastic.Index.GEP.Kernel.Flux.Weighted.Dominated

/-!
# The actual endpoint CDF of a moving weighted section

The boundary derivative is identified with the difference of the two endpoint
reward CDFs. Rewards are evaluated at the original endpoints, before the law
is pushed forward. This retains the boundary object needed by weighted coarea.
Only local endpoint moments are required.
-/

namespace PGM
noncomputable section
open MeasureTheory Set Filter
open scoped Interval

theorem output_weighted_section_boundary_primitive {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {L U : Ω → ℝ} {F f : Ω → ℝ → ℝ}
    (hL : Measurable L) (hU : Measurable U)
    (hacL : (P.map L).restrict (Ioi 0) ≪ volume)
    (hacU : (P.map U).restrict (Ioi 0) ≪ volume)
    (hLU : ∀ᵐ ω ∂P, 0 ≤ L ω ∧ L ω ≤ U ω)
    (hFL : Measurable (fun ω => F ω (L ω))) (hFU : Measurable (fun ω => F ω (U ω)))
    (hiL : ∀ R : ℝ, IntegrableOn (fun ω => F ω (L ω)) {ω | L ω ≤ R} P)
    (hiU : ∀ R : ℝ, IntegrableOn (fun ω => F ω (U ω)) {ω | U ω ≤ R} P)
    (hF : ∀ᵐ ω ∂P, ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      (∫ t in a..b, f ω t) = F ω b - F ω a)
    (hprod : ∀ R : ℝ, Integrable
      (fun p : Ω × ℝ => (Ioc (L p.1) (U p.1)).indicator (f p.1) p.2)
      (P.prod (volume.restrict (Ι (0 : ℝ) R)))) :
    ∃ B : ℝ → ℝ,
      AEPrimitive (fun x =>
        (∫ ω in {ω | L ω ≤ x}, F ω (L ω) ∂P) -
          ∫ ω in {ω | U ω ≤ x}, F ω (U ω) ∂P) B ∧
      AEPrimitive (fun x => ∫ ω, (Ioc (L ω) (U ω)).indicator (F ω) x ∂P)
        (fun x => (∫ ω, (Ioc (L ω) (U ω)).indicator (f ω) x ∂P) + B x) := by
  obtain ⟨jL, hIL, cL, hcL⟩ := flux_cdf_local_weight_aePrimitive P hL hacL hFL hiL
  obtain ⟨jU, hIU, cU, hcU⟩ := flux_cdf_local_weight_aePrimitive P hU hacU hFU hiU
  let H : ℝ → ℝ := fun x => ∫ ω, (Ioc (L ω) (U ω)).indicator (f ω) x ∂P
  have hH : ∀ R : ℝ, IntervalIntegrable H volume 0 R := by
    intro R
    rw [intervalIntegrable_iff]
    exact (hprod R).integral_prod_right
  refine ⟨fun x => jL x - jU x, ?_, ⟨fun R => (hH R).add ((hIL R).sub (hIU R)), cL - cU, ?_⟩⟩
  · refine ⟨fun R => (hIL R).sub (hIU R), cL - cU, ?_⟩
    filter_upwards [hcL, hcU] with x hcxL hcxU
    rw [hcxL, hcxU, intervalIntegral.integral_sub (hIL x) (hIU x)]
    ring
  · filter_upwards [hcL, hcU, ae_restrict_mem measurableSet_Ioi] with x hcxL hcxU hx
    have hx0 : 0 < x := hx
    have he : ∀ᵐ ω ∂P,
        (Ioc (L ω) (U ω)).indicator (F ω) x =
          {ω | L ω ≤ x}.indicator (fun ω => F ω (L ω)) ω -
          {ω | U ω ≤ x}.indicator (fun ω => F ω (U ω)) ω +
          ∫ t in (0 : ℝ)..x, (Ioc (L ω) (U ω)).indicator (f ω) t := by
      filter_upwards [hLU, hF, flux_endpoint_ae_ne_positive P hL hacL hx,
        flux_endpoint_ae_ne_positive P hU hacU hx] with ω hω hωF hnL hnU
      have hh := flux_weighted_interval_identity hω.1 hω.2 hx.le hωF
      have hleL : L ω < x ↔ L ω ≤ x := ⟨le_of_lt, fun h => lt_of_le_of_ne h hnL⟩
      have hleU : U ω < x ↔ U ω ≤ x := ⟨le_of_lt, fun h => lt_of_le_of_ne h hnU⟩
      simp only [hleL, hleU] at hh
      simpa only [indicator_apply, mem_ofPred_eq] using hh
    have hSL : MeasurableSet {ω | L ω ≤ x} := hL measurableSet_Iic
    have hSU : MeasurableSet {ω | U ω ≤ x} := hU measurableSet_Iic
    have hiLi : Integrable ({ω | L ω ≤ x}.indicator (fun ω => F ω (L ω))) P :=
      (integrable_indicator_iff hSL).2 (hiL x)
    have hiUi : Integrable ({ω | U ω ≤ x}.indicator (fun ω => F ω (U ω))) P :=
      (integrable_indicator_iff hSU).2 (hiU x)
    have hiInt : Integrable
        (fun ω => ∫ t in (0 : ℝ)..x, (Ioc (L ω) (U ω)).indicator (f ω) t) P := by
      simpa only [intervalIntegral.integral_of_le hx0.le, uIoc_of_le hx0.le] using
        (hprod x).integral_prod_left
    have hiDiff : Integrable (fun ω =>
        {ω | L ω ≤ x}.indicator (fun ω => F ω (L ω)) ω -
        {ω | U ω ≤ x}.indicator (fun ω => F ω (U ω)) ω) P := hiLi.sub hiUi
    have hiJDiff : IntervalIntegrable (fun t => jL t - jU t) volume 0 x := (hIL x).sub (hIU x)
    rw [integral_congr_ae he, integral_add hiDiff hiInt, integral_sub hiLi hiUi,
      integral_indicator hSL, integral_indicator hSU,
      hcxL, hcxU, ← intervalIntegral_integral_swap (μ := P) (a := 0) (b := x)
        (f := fun t ω => (Ioc (L ω) (U ω)).indicator (f ω) t) (hprod x).swap,
      intervalIntegral.integral_add (hH x) hiJDiff,
      intervalIntegral.integral_sub (hIL x) (hIU x)]
    ring


theorem output_weighted_halfLine_boundary_primitive {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {L : Ω → ℝ} {F f : Ω → ℝ → ℝ}
    (hL : Measurable L) (hacL : (P.map L).restrict (Ioi 0) ≪ volume)
    (hL0 : ∀ᵐ ω ∂P, 0 ≤ L ω) (hFL : Measurable (fun ω => F ω (L ω)))
    (hiL : ∀ R : ℝ, IntegrableOn (fun ω => F ω (L ω)) {ω | L ω ≤ R} P)
    (hF : ∀ᵐ ω ∂P, ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      (∫ t in a..b, f ω t) = F ω b - F ω a)
    (hprod : ∀ R : ℝ, Integrable
      (fun p : Ω × ℝ => (Ioi (L p.1)).indicator (f p.1) p.2)
      (P.prod (volume.restrict (Ι (0 : ℝ) R)))) :
    ∃ B : ℝ → ℝ,
      AEPrimitive (fun x => ∫ ω in {ω | L ω ≤ x}, F ω (L ω) ∂P) B ∧
      AEPrimitive (fun x => ∫ ω, (Ioi (L ω)).indicator (F ω) x ∂P)
        (fun x => (∫ ω, (Ioi (L ω)).indicator (f ω) x ∂P) + B x) := by
  obtain ⟨jL, hIL, cL, hcL⟩ := flux_cdf_local_weight_aePrimitive P hL hacL hFL hiL
  let H : ℝ → ℝ := fun x => ∫ ω, (Ioi (L ω)).indicator (f ω) x ∂P
  have hH : ∀ R : ℝ, IntervalIntegrable H volume 0 R := by
    intro R
    rw [intervalIntegrable_iff]
    exact (hprod R).integral_prod_right
  refine ⟨jL, ⟨hIL, cL, hcL⟩, ⟨fun R => (hH R).add (hIL R), cL, ?_⟩⟩
  filter_upwards [hcL, ae_restrict_mem measurableSet_Ioi] with x hcxL hx
  have hx0 : 0 < x := hx
  have he : ∀ᵐ ω ∂P,
      (Ioi (L ω)).indicator (F ω) x =
        {ω | L ω ≤ x}.indicator (fun ω => F ω (L ω)) ω +
        ∫ t in (0 : ℝ)..x, (Ioi (L ω)).indicator (f ω) t := by
    filter_upwards [hL0, hF, flux_endpoint_ae_ne_positive P hL hacL hx0] with ω hω hωF hnL
    have hh := flux_halfLine_weighted_identity hω hx0.le hωF
    have hleL : L ω < x ↔ L ω ≤ x := ⟨le_of_lt, fun h => lt_of_le_of_ne h hnL⟩
    simp only [hleL] at hh
    simpa only [indicator_apply, mem_ofPred_eq] using hh
  have hSL : MeasurableSet {ω | L ω ≤ x} := hL measurableSet_Iic
  have hiLi : Integrable ({ω | L ω ≤ x}.indicator (fun ω => F ω (L ω))) P :=
    (integrable_indicator_iff hSL).2 (hiL x)
  have hiInt : Integrable (fun ω => ∫ t in (0 : ℝ)..x, (Ioi (L ω)).indicator (f ω) t) P := by
    simpa only [intervalIntegral.integral_of_le hx0.le, uIoc_of_le hx0.le] using
      (hprod x).integral_prod_left
  rw [integral_congr_ae he, integral_add hiLi hiInt, integral_indicator hSL, hcxL,
    ← intervalIntegral_integral_swap (μ := P) (a := 0) (b := x)
      (f := fun t ω => (Ioi (L ω)).indicator (f ω) t) (hprod x).swap,
    intervalIntegral.integral_add (hH x) (hIL x)]
  ring


theorem output_weighted_section_boundary_of_local_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {L U : Ω → ℝ} {F f : Ω → ℝ → ℝ}
    {BF Bf : ℝ → Ω → ℝ} (hL : Measurable L) (hU : Measurable U)
    (hacL : (P.map L).restrict (Ioi 0) ≪ volume)
    (hacU : (P.map U).restrict (Ioi 0) ≪ volume)
    (hLU : ∀ᵐ ω ∂P, 0 ≤ L ω ∧ L ω ≤ U ω)
    (hFm : Measurable (fun p : Ω × ℝ => F p.1 p.2))
    (hfm : Measurable (fun p : Ω × ℝ => f p.1 p.2))
    (hBFi : ∀ R, Integrable (BF R) P) (hBfi : ∀ R, Integrable (Bf R) P)
    (hBF : ∀ R, ∀ᵐ ω ∂P, ∀ x ∈ Icc (0 : ℝ) (max 0 R), ‖F ω x‖ ≤ BF R ω)
    (hBf : ∀ R, ∀ᵐ ω ∂P, ∀ x ∈ Icc (0 : ℝ) (max 0 R), ‖f ω x‖ ≤ Bf R ω)
    (hF : ∀ᵐ ω ∂P, ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      (∫ t in a..b, f ω t) = F ω b - F ω a) :
    ∃ B : ℝ → ℝ,
      AEPrimitive (fun x =>
        (∫ ω in {ω | L ω ≤ x}, F ω (L ω) ∂P) -
          ∫ ω in {ω | U ω ≤ x}, F ω (U ω) ∂P) B ∧
      AEPrimitive (fun x => ∫ ω, (Ioc (L ω) (U ω)).indicator (F ω) x ∂P)
        (fun x => (∫ ω, (Ioc (L ω) (U ω)).indicator (f ω) x ∂P) + B x) := by
  refine output_weighted_section_boundary_primitive P hL hU hacL hacU hLU
    (hFm.comp (measurable_id.prodMk hL)) (hFm.comp (measurable_id.prodMk hU))
    (flux_endpoint_integrableOn_of_local_bound P hL (hLU.mono fun ω hω => hω.1) hFm hBFi hBF)
    (flux_endpoint_integrableOn_of_local_bound P hU
      (hLU.mono fun ω hω => hω.1.trans hω.2) hFm hBFi hBF) hF ?_
  intro R
  let A : Set (Ω × ℝ) := {p | L p.1 < p.2 ∧ p.2 ≤ U p.1}
  have hA : MeasurableSet A :=
    (measurableSet_lt (hL.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd (hU.comp measurable_fst))
  have hA0 : ∀ᵐ ω ∂P, ∀ t, (ω, t) ∈ A → 0 ≤ t :=
    hLU.mono fun ω hω t ht => hω.1.trans ht.1.le
  exact flux_section_integrable_prod_of_local_bound P hA hA0 hfm hBfi hBf R

/-- The same domination criterion covers an unbounded section. -/
theorem output_weighted_halfLine_boundary_of_local_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {L : Ω → ℝ} {F f : Ω → ℝ → ℝ}
    {BF Bf : ℝ → Ω → ℝ} (hL : Measurable L)
    (hacL : (P.map L).restrict (Ioi 0) ≪ volume) (hL0 : ∀ᵐ ω ∂P, 0 ≤ L ω)
    (hFm : Measurable (fun p : Ω × ℝ => F p.1 p.2))
    (hfm : Measurable (fun p : Ω × ℝ => f p.1 p.2))
    (hBFi : ∀ R, Integrable (BF R) P) (hBfi : ∀ R, Integrable (Bf R) P)
    (hBF : ∀ R, ∀ᵐ ω ∂P, ∀ x ∈ Icc (0 : ℝ) (max 0 R), ‖F ω x‖ ≤ BF R ω)
    (hBf : ∀ R, ∀ᵐ ω ∂P, ∀ x ∈ Icc (0 : ℝ) (max 0 R), ‖f ω x‖ ≤ Bf R ω)
    (hF : ∀ᵐ ω ∂P, ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      (∫ t in a..b, f ω t) = F ω b - F ω a) :
    ∃ B : ℝ → ℝ,
      AEPrimitive (fun x => ∫ ω in {ω | L ω ≤ x}, F ω (L ω) ∂P) B ∧
      AEPrimitive (fun x => ∫ ω, (Ioi (L ω)).indicator (F ω) x ∂P)
        (fun x => (∫ ω, (Ioi (L ω)).indicator (f ω) x ∂P) + B x) := by
  refine output_weighted_halfLine_boundary_primitive P hL hacL hL0
    (hFm.comp (measurable_id.prodMk hL))
    (flux_endpoint_integrableOn_of_local_bound P hL hL0 hFm hBFi hBF) hF ?_
  intro R
  let A : Set (Ω × ℝ) := {p | L p.1 < p.2}
  have hA : MeasurableSet A := measurableSet_lt (hL.comp measurable_fst) measurable_snd
  have hA0 : ∀ᵐ ω ∂P, ∀ t, (ω, t) ∈ A → 0 ≤ t :=
    hL0.mono fun ω hω t ht => hω.trans ht.le
  exact flux_section_integrable_prod_of_local_bound P hA hA0 hfm hBfi hBf R


end
end PGM
