import PLAStochastic.Index.GEP.Kernel.Flux.Weighted.HalfLine

/-!
# Local domination for weighted sections

An integrable path majorant on each compact spatial interval proves both
endpoint-reward integrability and the local product integrability required by
the weighted section formula.
-/

namespace PGM

noncomputable section

open MeasureTheory Set Filter
open scoped Interval

theorem flux_endpoint_integrableOn_of_local_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {E : Ω → ℝ} {F : Ω → ℝ → ℝ} {B : ℝ → Ω → ℝ}
    (hE : Measurable E) (hE0 : ∀ᵐ ω ∂P, 0 ≤ E ω)
    (hF : Measurable (fun p : Ω × ℝ => F p.1 p.2))
    (hBi : ∀ R, Integrable (B R) P)
    (hB : ∀ R, ∀ᵐ ω ∂P, ∀ x ∈ Icc (0 : ℝ) (max 0 R), ‖F ω x‖ ≤ B R ω) (R : ℝ) :
    IntegrableOn (fun ω => F ω (E ω)) {ω | E ω ≤ R} P := by
  have hS : MeasurableSet {ω | E ω ≤ R} := hE measurableSet_Iic
  refine (hBi R).integrableOn.mono'
    ((hF.comp (measurable_id.prodMk hE)).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_of_ae hE0, ae_restrict_of_ae (hB R), ae_restrict_mem hS]
    with ω hω0 hωB hωR
  exact hωB (E ω) ⟨hω0, hωR.trans (le_max_right _ _)⟩

/-- A positive spatial section can be arbitrary and path dependent. Its
indicator converts compact-spatial domination into the needed product L¹ bound. -/
theorem flux_section_integrable_prod_of_local_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {A : Set (Ω × ℝ)} {f : Ω → ℝ → ℝ} {B : ℝ → Ω → ℝ}
    (hA : MeasurableSet A) (hA0 : ∀ᵐ ω ∂P, ∀ t, (ω, t) ∈ A → 0 ≤ t)
    (hf : Measurable (fun p : Ω × ℝ => f p.1 p.2))
    (hBi : ∀ R, Integrable (B R) P)
    (hB : ∀ R, ∀ᵐ ω ∂P, ∀ x ∈ Icc (0 : ℝ) (max 0 R), ‖f ω x‖ ≤ B R ω) (R : ℝ) :
    Integrable (A.indicator (fun p : Ω × ℝ => f p.1 p.2))
      (P.prod (volume.restrict (Ι (0 : ℝ) R))) := by
  have : IsFiniteMeasure (volume.restrict (Ι (0 : ℝ) R)) := ⟨by simp [Real.volume_uIoc]⟩
  have hi := (hBi R).comp_fst (volume.restrict (Ι (0 : ℝ) R))
  refine hi.mono' (hf.indicator hA).aestronglyMeasurable ?_
  filter_upwards [Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually (hB R),
    Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually hA0,
    Measure.quasiMeasurePreserving_snd.tendsto_ae.eventually (ae_restrict_mem measurableSet_uIoc)]
    with p hpB hpA hpR
  by_cases hp : p ∈ A
  · rw [indicator_of_mem hp]
    exact hpB p.2 ⟨hpA p.2 hp, hpR.2⟩
  · rw [indicator_of_notMem hp, norm_zero]
    exact (norm_nonneg (f p.1 0)).trans (hpB 0 ⟨le_rfl, le_max_left _ _⟩)

/-- Joint measurability and ordinary compact-spatial majorants discharge all
analytic hypotheses of the weighted bounded-section primitive. -/
theorem flux_weighted_section_aePrimitive_of_local_bound {Ω : Type*} [MeasurableSpace Ω]
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
        (fun x => (∫ ω, (Ioc (L ω) (U ω)).indicator (f ω) x ∂P) + B x) := by
  refine flux_weighted_section_aePrimitive P hL hU hacL hacU hLU
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
theorem flux_weighted_halfLine_aePrimitive_of_local_bound {Ω : Type*} [MeasurableSpace Ω]
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
        (fun x => (∫ ω, (Ioi (L ω)).indicator (f ω) x ∂P) + B x) := by
  refine flux_weighted_halfLine_aePrimitive P hL hacL hL0
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
