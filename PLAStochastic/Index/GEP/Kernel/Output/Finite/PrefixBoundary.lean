import PLAStochastic.Index.GEP.Kernel.Output.Finite.WeightedSection
import PLAStochastic.Index.GEP.Kernel.Flux.Weighted.PrefixBound

/-!
# Identified endpoint boundary of the original finite prefix

The endpoint reward CDF is explicit. Its derivative agrees almost everywhere
on the positive half-line with the boundary term of the original inserted
survival event. The harmless correction off that half-line preserves the
original `AEPrimitive` convention without imposing conditions on negative gaps.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter

/-- The signed CDF of rewards at the actual finite polyhedral endpoints. -/
def outputPolyBoundaryCDF {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (P : Measure Ω) (c : ι → ℝ) (d : ι → Ω → ℝ) (F : Ω → ℝ → ℝ) (x : ℝ) : ℝ :=
  if h : (fluxPos c).Nonempty then
    (∫ ω in {ω | fluxPolyLower c d ω ≤ x}, F ω (fluxPolyLower c d ω)
      ∂P.restrict (fluxPolyActive c d h)) -
    ∫ ω in {ω | fluxPolyUpper c d h ω ≤ x}, F ω (fluxPolyUpper c d h ω)
      ∂P.restrict (fluxPolyActive c d h)
  else
    ∫ ω in {ω | fluxPolyLower c d ω ≤ x}, F ω (fluxPolyLower c d ω)
      ∂P.restrict (fluxPolyZeroOK c d)

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]

theorem output_poly_boundary_primitive (P : Measure Ω) [IsFiniteMeasure P]
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
    ∃ j B : ℝ → ℝ,
      AEPrimitive (outputPolyBoundaryCDF P c d F) j ∧
      B =ᵐ[volume.restrict (Ioi (0 : ℝ))] j ∧
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
    obtain ⟨B, hBC, hI, a, ha⟩ := output_weighted_section_boundary_of_local_bound Q hL hU
      hacLQ hacUQ hLU hFm hfm (fun R => (hBFi R).integrableOn)
      (fun R => (hBfi R).integrableOn) (fun R => ae_restrict_of_ae (hBF R))
      (fun R => ae_restrict_of_ae (hBf R)) (ae_restrict_of_ae hF)
    let H : ℝ → ℝ := fun x =>
      ∫ ω, (Ioc (fluxPolyLower c d ω) (fluxPolyUpper c d h ω)).indicator (f ω) x ∂Q
    have hder : (fun x => J f x + (H x + B x - J f x)) = fun x => H x + B x := by
      funext x
      ring
    refine ⟨B, fun x => H x + B x - J f x, ?_, ?_, ?_⟩
    · convert hBC using 1
      funext x
      simp only [outputPolyBoundaryCDF, dif_pos h]
      rfl
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have he : J f x = H x := flux_poly_weighted_integral_bounded P c hd hacL h f hx
      rw [he]
      ring
    · change AEPrimitive (J F) (fun x => J f x + (H x + B x - J f x))
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
    obtain ⟨B, hBC, hI, a, ha⟩ := output_weighted_halfLine_boundary_of_local_bound Q hL
      hacLQ hL0 hFm hfm (fun R => (hBFi R).integrableOn)
      (fun R => (hBfi R).integrableOn) (fun R => ae_restrict_of_ae (hBF R))
      (fun R => ae_restrict_of_ae (hBf R)) (ae_restrict_of_ae hF)
    let H : ℝ → ℝ := fun x => ∫ ω, (Ioi (fluxPolyLower c d ω)).indicator (f ω) x ∂Q
    have hder : (fun x => J f x + (H x + B x - J f x)) = fun x => H x + B x := by
      funext x
      ring
    refine ⟨B, fun x => H x + B x - J f x, ?_, ?_, ?_⟩
    · convert hBC using 1
      funext x
      simp only [outputPolyBoundaryCDF, dif_neg h]
      rfl
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have he : J f x = H x := flux_poly_weighted_integral_halfLine P c hd hacL h f hx
      rw [he]
      ring
    · change AEPrimitive (J F) (fun x => J f x + (H x + B x - J f x))
      rw [hder]
      refine ⟨hI, a, ?_⟩
      filter_upwards [ha, ae_restrict_mem measurableSet_Ioi] with x hax hx
      rw [show J F x = _ from flux_poly_weighted_integral_halfLine P c hd hacL h F hx]
      exact hax


/-- The original prefix's endpoint reward CDF, retaining every actual facet. -/
def outputPrefixBoundaryCDF (P : Measure (ℕ → ℝ)) (eps : ℝ) (k i : ℕ)
    (F : (ℕ → ℝ) → ℝ → ℝ) : ℝ → ℝ :=
  outputPolyBoundaryCDF P (fun q : FluxFacetIndex k => fluxFacetCoef eps q i)
    (fluxPrefixRHS eps k i) F

/-- The actual prefix boundary is the derivative of its explicit endpoint CDF.
This includes coordinates outside the prefix; no extra facet assumptions occur. -/
theorem output_prefix_boundary_primitive {ν : ProbabilityMeasure ℝ}
    (hac : (ν : Measure ℝ) ≪ volume) (hpos : ∀ᵐ x ∂(ν : Measure ℝ), 0 < x)
    (P : Measure (ℕ → ℝ)) [IsFiniteMeasure P] (hP : P ≪ iidLaw ν)
    (eps : ℝ) {k : ℕ} (hk : 2 ≤ k) (i : ℕ)
    {F f : (ℕ → ℝ) → ℝ → ℝ} {BF Bf : ℝ → (ℕ → ℝ) → ℝ}
    (hFm : Measurable (fun p : (ℕ → ℝ) × ℝ => F p.1 p.2))
    (hfm : Measurable (fun p : (ℕ → ℝ) × ℝ => f p.1 p.2))
    (hBFi : ∀ R, Integrable (BF R) P) (hBfi : ∀ R, Integrable (Bf R) P)
    (hBF : ∀ R, ∀ᵐ g ∂P, ∀ x ∈ Icc (0 : ℝ) (max 0 R), ‖F g x‖ ≤ BF R g)
    (hBf : ∀ R, ∀ᵐ g ∂P, ∀ x ∈ Icc (0 : ℝ) (max 0 R), ‖f g x‖ ≤ Bf R g)
    (hF : ∀ᵐ g ∂P, ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      (∫ t in a..b, f g t) = F g b - F g a) :
    ∃ j B : ℝ → ℝ,
      AEPrimitive (outputPrefixBoundaryCDF P eps k i F) j ∧
      B =ᵐ[volume.restrict (Ioi (0 : ℝ))] j ∧
      AEPrimitive (fluxPrefixWeighted P eps k i F)
        (fun x => fluxPrefixWeighted P eps k i f x + B x) := by
  have hroot (q : FluxFacetIndex k) :
      (P.map (fun g => fluxPrefixRHS eps k i q g / fluxFacetCoef eps q i)).restrict (Ioi 0) ≪ volume :=
    ((hP.map ((measurable_fluxPrefixRHS eps k i q).div_const _)).restrict (Ioi 0)).trans
      (fluxPrefixRHS_root_ac hac eps k i q)
  obtain ⟨j, B, hBC, hBj, hI, a, ha⟩ := output_poly_boundary_primitive P
    (fun q : FluxFacetIndex k => fluxFacetCoef eps q i)
    (fun q => measurable_fluxPrefixRHS eps k i q) hroot hFm hfm hBFi hBfi hBF hBf hF
  let H : ℝ → ℝ := fun x =>
    ∫ g, {g | ∀ q : FluxFacetIndex k, fluxFacetCoef eps q i * x ≤ fluxPrefixRHS eps k i q g}.indicator
      (fun g => f g x) g ∂P
  let B' : ℝ → ℝ := fun x => H x + B x - fluxPrefixWeighted P eps k i f x
  have he : (fun x => fluxPrefixWeighted P eps k i f x + B' x) = fun x => H x + B x := by
    funext x
    dsimp [B']
    ring
  refine ⟨j, B', hBC, ?_, ?_⟩
  · filter_upwards [hBj, ae_restrict_mem measurableSet_Ioi] with x hxj hx
    dsimp [B']
    rw [flux_prefix_weighted_eq_poly_all hpos P hP eps hk i f hx, hxj]
    change H x + j x - H x = j x
    ring
  · rw [he]
    refine ⟨hI, a, ?_⟩
    filter_upwards [ha, ae_restrict_mem measurableSet_Ioi] with x hax hx
    rw [flux_prefix_weighted_eq_poly_all hpos P hP eps hk i F hx]
    exact hax

end
end PGM
