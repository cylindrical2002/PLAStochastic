import PLAStochastic.Index.GEP.Kernel.Flux.Weighted.SectionBound

/-!
# Local variation controlled by path majorants

The expected compact-spatial majorant controls the endpoint flux even when the
selected endpoint itself has no global exponential moment.
-/

namespace PGM
noncomputable section
open MeasureTheory Set Filter
open scoped Interval

theorem flux_endpoint_local_mass_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {E : Ω → ℝ} {F : Ω → ℝ → ℝ} {B : ℝ → Ω → ℝ}
    (hE : Measurable E) (hE0 : ∀ᵐ ω ∂P, 0 ≤ E ω)
    (hF : Measurable (fun p : Ω × ℝ => F p.1 p.2))
    (hBi : ∀ R, Integrable (B R) P)
    (hB : ∀ R, ∀ᵐ ω ∂P, ∀ x ∈ Icc (0 : ℝ) (max 0 R), ‖F ω x‖ ≤ B R ω) (R : ℝ) :
    (∫ ω in {ω | E ω ≤ max 0 R}, |F ω (E ω)| ∂P) ≤ ∫ ω, B R ω ∂P := by
  have hW := flux_endpoint_integrableOn_of_local_bound P hE hE0 hF hBi hB (max 0 R)
  have hS : MeasurableSet {ω | E ω ≤ max 0 R} := hE measurableSet_Iic
  calc
    _ ≤ ∫ ω in {ω | E ω ≤ max 0 R}, B R ω ∂P := by
      apply integral_mono_ae hW.abs (hBi R).integrableOn
      filter_upwards [ae_restrict_of_ae hE0, ae_restrict_of_ae (hB R), ae_restrict_mem hS]
        with ω hω0 hωB hωR
      exact hωB (E ω) ⟨hω0, hωR⟩
    _ ≤ _ := setIntegral_le_integral (hBi R) ((hB R).mono fun ω hω =>
      (norm_nonneg _).trans (hω 0 ⟨le_rfl, le_max_left _ _⟩))

theorem flux_weighted_section_bound_of_local_bound {Ω : Type*} [MeasurableSpace Ω]
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
      AEPrimitive (fun x => ∫ ω, (Ioc (L ω) (U ω)).indicator (F ω) x ∂P)
        (fun x => (∫ ω, (Ioc (L ω) (U ω)).indicator (f ω) x ∂P) + B x) ∧
      (∀ R : ℝ, IntervalIntegrable B volume 0 R) ∧
      ∀ R : ℝ, (∫ x in Ι (0 : ℝ) R, ‖B x‖) ≤ 2 * ∫ ω, BF R ω ∂P := by
  have hh := flux_weighted_section_aePrimitive_bound P (F := F) (f := f) hL hU hacL hacU hLU
    (hFm.comp (measurable_id.prodMk hL)) (hFm.comp (measurable_id.prodMk hU))
    (flux_endpoint_integrableOn_of_local_bound P hL (hLU.mono fun ω hω => hω.1) hFm hBFi hBF)
    (flux_endpoint_integrableOn_of_local_bound P hU
      (hLU.mono fun ω hω => hω.1.trans hω.2) hFm hBFi hBF) hF
  have hprod : ∀ R : ℝ, Integrable
      (fun p : Ω × ℝ => (Ioc (L p.1) (U p.1)).indicator (f p.1) p.2)
      (P.prod (volume.restrict (Ι (0 : ℝ) R))) := by
    intro R
    let A : Set (Ω × ℝ) := {p | L p.1 < p.2 ∧ p.2 ≤ U p.1}
    have hA : MeasurableSet A :=
      (measurableSet_lt (hL.comp measurable_fst) measurable_snd).inter
        (measurableSet_le measurable_snd (hU.comp measurable_fst))
    have hA0 : ∀ᵐ ω ∂P, ∀ t, (ω, t) ∈ A → 0 ≤ t :=
      hLU.mono fun ω hω t ht => hω.1.trans ht.1.le
    exact flux_section_integrable_prod_of_local_bound P hA hA0 hfm hBfi hBf R
  obtain ⟨B, hB, hBI, hbound⟩ := hh hprod
  refine ⟨B, hB, hBI, fun R => ?_⟩
  have hLmass := flux_endpoint_local_mass_le P hL (hLU.mono fun ω hω => hω.1) hFm hBFi hBF R
  have hUmass := flux_endpoint_local_mass_le P hU (hLU.mono fun ω hω => hω.1.trans hω.2) hFm hBFi hBF R
  exact (hbound R).trans (by linarith)

/-- The same domination criterion covers an unbounded section. -/
theorem flux_weighted_halfLine_bound_of_local_bound {Ω : Type*} [MeasurableSpace Ω]
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
      AEPrimitive (fun x => ∫ ω, (Ioi (L ω)).indicator (F ω) x ∂P)
        (fun x => (∫ ω, (Ioi (L ω)).indicator (f ω) x ∂P) + B x) ∧
      (∀ R : ℝ, IntervalIntegrable B volume 0 R) ∧
      ∀ R : ℝ, (∫ x in Ι (0 : ℝ) R, ‖B x‖) ≤ ∫ ω, BF R ω ∂P := by
  have hh := flux_weighted_halfLine_aePrimitive_bound P (F := F) (f := f) hL hacL hL0
    (hFm.comp (measurable_id.prodMk hL))
    (flux_endpoint_integrableOn_of_local_bound P hL hL0 hFm hBFi hBF) hF
  have hprod : ∀ R : ℝ, Integrable
      (fun p : Ω × ℝ => (Ioi (L p.1)).indicator (f p.1) p.2)
      (P.prod (volume.restrict (Ι (0 : ℝ) R))) := by
    intro R
    let A : Set (Ω × ℝ) := {p | L p.1 < p.2}
    have hA : MeasurableSet A := measurableSet_lt (hL.comp measurable_fst) measurable_snd
    have hA0 : ∀ᵐ ω ∂P, ∀ t, (ω, t) ∈ A → 0 ≤ t :=
      hL0.mono fun ω hω t ht => hω.trans ht.le
    exact flux_section_integrable_prod_of_local_bound P hA hA0 hfm hBfi hBf R
  obtain ⟨B, hB, hBI, hbound⟩ := hh hprod
  refine ⟨B, hB, hBI, fun R => ?_⟩
  exact (hbound R).trans (flux_endpoint_local_mass_le P hL hL0 hFm hBFi hBF R)

end
end PGM
