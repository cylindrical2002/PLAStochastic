import PLAStochastic.Index.GEP.Kernel.Flux.Prefix.OneGapPrimitive
import PLAStochastic.Index.GEP.Kernel.Flux.Weighted.Polyhedron

/-!
# Moving rewards on the original finite PLA prefix

The polyhedral section theorem is connected to the original inserted stopping
event under the original iid assumptions. The derivative's interior term is
the actual insertion-weighted first derivative of the reward.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter

/-- Weighted original finite-prefix survival after fixing one gap. -/
def fluxPrefixWeighted (P : Measure (ℕ → ℝ)) (eps : ℝ) (k i : ℕ)
    (F : (ℕ → ℝ) → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ g, {g | (k : ℕ∞) < gapSegLen eps (Function.update g i x)}.indicator
    (fun g => F g x) g ∂P

theorem flux_prefix_weighted_eq_poly {ν : ProbabilityMeasure ℝ}
    (hpos : ∀ᵐ x ∂(ν : Measure ℝ), 0 < x) (P : Measure (ℕ → ℝ)) (hP : P ≪ iidLaw ν)
    (eps : ℝ) {k i : ℕ} (hk : 2 ≤ k) (hi : i < k) (F : (ℕ → ℝ) → ℝ → ℝ)
    {x : ℝ} (hx : 0 < x) :
    fluxPrefixWeighted P eps k i F x =
      ∫ g, {g | ∀ q : FluxFacetIndex k, fluxFacetCoef eps q i * x ≤ fluxPrefixRHS eps k i q g}.indicator
        (fun g => F g x) g ∂P := by
  have hgs : ∀ᵐ g ∂iidLaw ν, ∀ l, 0 < g l := by
    rw [ae_all_iff]
    intro l
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => (ν : Measure ℝ)) l).quasiMeasurePreserving
      |>.ae hpos
  apply integral_congr_ae
  filter_upwards [hP hgs] with g hg
  have he : ((k : ℕ∞) < gapSegLen eps (Function.update g i x)) ↔
      ∀ q : FluxFacetIndex k, fluxFacetCoef eps q i * x ≤ fluxPrefixRHS eps k i q g := by
    rw [gapSegLen, lt_segLen_iff]
    exact flux_prefix_update_iff hk hi hx (fun l _ _ => hg l)
  simp only [indicator_apply, mem_ofPred_eq, he]

/-- The actual finite PLA prefix has the interior-plus-boundary primitive for
every reward satisfying measurable first-primitive and local domination data.
Absolute continuity of the actual facet endpoints is proved from the input law. -/
theorem flux_prefix_moving_weight_aePrimitive {ν : ProbabilityMeasure ℝ}
    (hac : (ν : Measure ℝ) ≪ volume) (hpos : ∀ᵐ x ∂(ν : Measure ℝ), 0 < x)
    (P : Measure (ℕ → ℝ)) [IsFiniteMeasure P] (hP : P ≪ iidLaw ν)
    (eps : ℝ) {k i : ℕ} (hk : 2 ≤ k) (hi : i < k)
    {F f : (ℕ → ℝ) → ℝ → ℝ} {BF Bf : ℝ → (ℕ → ℝ) → ℝ}
    (hFm : Measurable (fun p : (ℕ → ℝ) × ℝ => F p.1 p.2))
    (hfm : Measurable (fun p : (ℕ → ℝ) × ℝ => f p.1 p.2))
    (hBFi : ∀ R, Integrable (BF R) P) (hBfi : ∀ R, Integrable (Bf R) P)
    (hBF : ∀ R, ∀ᵐ g ∂P, ∀ x ∈ Icc (0 : ℝ) (max 0 R), ‖F g x‖ ≤ BF R g)
    (hBf : ∀ R, ∀ᵐ g ∂P, ∀ x ∈ Icc (0 : ℝ) (max 0 R), ‖f g x‖ ≤ Bf R g)
    (hF : ∀ᵐ g ∂P, ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      (∫ t in a..b, f g t) = F g b - F g a) :
    ∃ B : ℝ → ℝ,
      AEPrimitive (fluxPrefixWeighted P eps k i F)
        (fun x => fluxPrefixWeighted P eps k i f x + B x) := by
  have hroot (q : FluxFacetIndex k) :
      (P.map (fun g => fluxPrefixRHS eps k i q g / fluxFacetCoef eps q i)).restrict (Ioi 0) ≪ volume :=
    ((hP.map ((measurable_fluxPrefixRHS eps k i q).div_const _)).restrict (Ioi 0)).trans
      (fluxPrefixRHS_root_ac hac eps k i q)
  obtain ⟨B, hI, a, ha⟩ := fluxPoly_weighted_aePrimitive P
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
  refine ⟨B', ?_⟩
  rw [he]
  refine ⟨hI, a, ?_⟩
  filter_upwards [ha, ae_restrict_mem measurableSet_Ioi] with x hax hx
  rw [flux_prefix_weighted_eq_poly hpos P hP eps hk hi F hx]
  exact hax

end

end PGM
