import PLAStochastic.Index.GEP.Kernel.Flux.Weighted.Dominated
import PLAStochastic.Index.GEP.Kernel.Flux.Sections.PolyPrimitive

/-!
# The actual weighted finite polyhedral event

The original inequalities, including zero coefficients and empty sections, are
identified with their actual bounded or unbounded sections. Local domination
then yields an interior-plus-boundary primitive for their weighted integrals.
-/

namespace PGM

noncomputable section

open MeasureTheory Set Filter

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]

theorem flux_poly_weighted_integral_bounded (P : Measure Ω) (c : ι → ℝ)
    {d : ι → Ω → ℝ} (hd : ∀ q, Measurable (d q))
    (hacL : (P.map (fluxPolyLower c d)).restrict (Ioi 0) ≪ volume)
    (h : (fluxPos c).Nonempty) (F : Ω → ℝ → ℝ) {x : ℝ} (hx : 0 < x) :
    (∫ ω, {ω | ∀ q, c q * x ≤ d q ω}.indicator (fun ω => F ω x) ω ∂P) =
      ∫ ω, (Ioc (fluxPolyLower c d ω) (fluxPolyUpper c d h ω)).indicator (F ω) x
        ∂P.restrict (fluxPolyActive c d h) := by
  classical
  let S := fluxPolyActive c d h
  have hS : MeasurableSet S := measurableSet_fluxPolyActive c hd h
  rw [← integral_indicator hS]
  apply integral_congr_ae
  filter_upwards [flux_endpoint_ae_ne_positive P (measurable_fluxPolyLower c hd) hacL hx]
    with ω hne
  have he : (∀ q, c q * x ≤ d q ω) ↔
      ω ∈ S ∧ fluxPolyLower c d ω < x ∧ x ≤ fluxPolyUpper c d h ω := by
    rw [fluxPoly_iff_interval c d h ω hx]
    change (ω ∈ fluxPolyZeroOK c d ∧ fluxPolyLower c d ω ≤ x ∧ x ≤ fluxPolyUpper c d h ω) ↔
      ((ω ∈ fluxPolyZeroOK c d ∧ fluxPolyLower c d ω ≤ fluxPolyUpper c d h ω) ∧
        fluxPolyLower c d ω < x ∧ x ≤ fluxPolyUpper c d h ω)
    constructor
    · rintro ⟨hz, hl, hu⟩
      exact ⟨⟨hz, hl.trans hu⟩, lt_of_le_of_ne hl hne, hu⟩
    · rintro ⟨⟨hz, _⟩, hl, hu⟩
      exact ⟨hz, hl.le, hu⟩
  simp only [indicator_apply, mem_Ioc, mem_ofPred_eq, he]
  by_cases hs : ω ∈ S <;> simp [hs]

theorem flux_poly_weighted_integral_halfLine (P : Measure Ω) (c : ι → ℝ)
    {d : ι → Ω → ℝ} (hd : ∀ q, Measurable (d q))
    (hacL : (P.map (fluxPolyLower c d)).restrict (Ioi 0) ≪ volume)
    (h : ¬ (fluxPos c).Nonempty) (F : Ω → ℝ → ℝ) {x : ℝ} (hx : 0 < x) :
    (∫ ω, {ω | ∀ q, c q * x ≤ d q ω}.indicator (fun ω => F ω x) ω ∂P) =
      ∫ ω, (Ioi (fluxPolyLower c d ω)).indicator (F ω) x
        ∂P.restrict (fluxPolyZeroOK c d) := by
  classical
  let S := fluxPolyZeroOK c d
  have hS : MeasurableSet S := measurableSet_fluxPolyZeroOK c hd
  rw [← integral_indicator hS]
  apply integral_congr_ae
  filter_upwards [flux_endpoint_ae_ne_positive P (measurable_fluxPolyLower c hd) hacL hx]
    with ω hne
  have he : (∀ q, c q * x ≤ d q ω) ↔ ω ∈ S ∧ fluxPolyLower c d ω < x := by
    rw [fluxPoly_iff_halfLine c d h ω hx]
    exact and_congr_right fun _ => ⟨fun hl => lt_of_le_of_ne hl hne, le_of_lt⟩
  simp only [indicator_apply, mem_Ioi, mem_ofPred_eq, he]
  by_cases hs : ω ∈ S <;> simp [hs]

/-- Weighted finite affine inequalities have the actual interior-plus-boundary
primitive under local path majorants and positive-local AC candidate roots. -/
theorem fluxPoly_weighted_aePrimitive (P : Measure Ω) [IsFiniteMeasure P]
    (c : ι → ℝ) {d : ι → Ω → ℝ} (hd : ∀ q, Measurable (d q))
    (hac : ∀ q, (P.map (fun ω => d q ω / c q)).restrict (Ioi 0) ≪ volume)
    {F f : Ω → ℝ → ℝ} {BF Bf : ℝ → Ω → ℝ}
    (hFm : Measurable (fun p : Ω × ℝ => F p.1 p.2))
    (hfm : Measurable (fun p : Ω × ℝ => f p.1 p.2))
    (hBFi : ∀ R, Integrable (BF R) P) (hBfi : ∀ R, Integrable (Bf R) P)
    (hBF : ∀ R, ∀ᵐ ω ∂P, ∀ x ∈ Icc (0 : ℝ) (max 0 R), ‖F ω x‖ ≤ BF R ω)
    (hBf : ∀ R, ∀ᵐ ω ∂P, ∀ x ∈ Icc (0 : ℝ) (max 0 R), ‖f ω x‖ ≤ Bf R ω)
    (hF : ∀ᵐ ω ∂P, ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      (∫ t in a..b, f ω t) = F ω b - F ω a) :
    ∃ B : ℝ → ℝ,
      AEPrimitive
        (fun x => ∫ ω, {ω | ∀ q, c q * x ≤ d q ω}.indicator (fun ω => F ω x) ω ∂P)
        (fun x => (∫ ω, {ω | ∀ q, c q * x ≤ d q ω}.indicator (fun ω => f ω x) ω ∂P) + B x) := by
  classical
  let J : (Ω → ℝ → ℝ) → ℝ → ℝ := fun G x =>
    ∫ ω, {ω | ∀ q, c q * x ≤ d q ω}.indicator (fun ω => G ω x) ω ∂P
  have hL := measurable_fluxPolyLower c hd
  have hacL := fluxPolyLower_ac_positive P c hd hac
  by_cases h : (fluxPos c).Nonempty
  · let S := fluxPolyActive c d h
    let Q := P.restrict S
    have hS : MeasurableSet S := measurableSet_fluxPolyActive c hd h
    have hU := measurable_fluxPolyUpper c hd h
    have hacLQ := flux_endpoint_restrict_ac_positive P hL hacL S
    have hacUQ := flux_endpoint_restrict_ac_positive P hU
      (fluxPolyUpper_ac_positive P c hd hac h) S
    have hLU : ∀ᵐ ω ∂Q, 0 ≤ fluxPolyLower c d ω ∧
        fluxPolyLower c d ω ≤ fluxPolyUpper c d h ω := by
      filter_upwards [ae_restrict_mem hS] with ω hω
      exact ⟨fluxPolyLower_nonneg c d ω, hω.2⟩
    obtain ⟨B, hI, a, ha⟩ := flux_weighted_section_aePrimitive_of_local_bound Q hL hU
      hacLQ hacUQ hLU hFm hfm (fun R => (hBFi R).integrableOn)
      (fun R => (hBfi R).integrableOn) (fun R => ae_restrict_of_ae (hBF R))
      (fun R => ae_restrict_of_ae (hBf R)) (ae_restrict_of_ae hF)
    let H : ℝ → ℝ := fun x =>
      ∫ ω, (Ioc (fluxPolyLower c d ω) (fluxPolyUpper c d h ω)).indicator (f ω) x ∂Q
    have hder : (fun x => J f x + (H x + B x - J f x)) = fun x => H x + B x := by
      funext x
      ring
    refine ⟨fun x => H x + B x - J f x, ?_⟩
    change AEPrimitive (J F) (fun x => J f x + (H x + B x - J f x))
    rw [hder]
    refine ⟨hI, a, ?_⟩
    filter_upwards [ha, ae_restrict_mem measurableSet_Ioi] with x hax hx
    rw [show J F x = _ from flux_poly_weighted_integral_bounded P c hd hacL h F hx]
    exact hax
  · let S := fluxPolyZeroOK c d
    let Q := P.restrict S
    have hacLQ := flux_endpoint_restrict_ac_positive P hL hacL S
    have hL0 : ∀ᵐ ω ∂Q, 0 ≤ fluxPolyLower c d ω :=
      Eventually.of_forall fun ω => fluxPolyLower_nonneg c d ω
    obtain ⟨B, hI, a, ha⟩ := flux_weighted_halfLine_aePrimitive_of_local_bound Q hL
      hacLQ hL0 hFm hfm (fun R => (hBFi R).integrableOn)
      (fun R => (hBfi R).integrableOn) (fun R => ae_restrict_of_ae (hBF R))
      (fun R => ae_restrict_of_ae (hBf R)) (ae_restrict_of_ae hF)
    let H : ℝ → ℝ := fun x => ∫ ω, (Ioi (fluxPolyLower c d ω)).indicator (f ω) x ∂Q
    have hder : (fun x => J f x + (H x + B x - J f x)) = fun x => H x + B x := by
      funext x
      ring
    refine ⟨fun x => H x + B x - J f x, ?_⟩
    change AEPrimitive (J F) (fun x => J f x + (H x + B x - J f x))
    rw [hder]
    refine ⟨hI, a, ?_⟩
    filter_upwards [ha, ae_restrict_mem measurableSet_Ioi] with x hax hx
    rw [show J F x = _ from flux_poly_weighted_integral_halfLine P c hd hacL h F hx]
    exact hax

end

end PGM
