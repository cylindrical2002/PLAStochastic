import PLAStochastic.Index.GEP.Kernel.Flux.Weighted.PolyhedronBound
import PLAStochastic.Index.GEP.Kernel.Flux.Weighted.Prefix

/-!
# Quantitative moving rewards for every inserted coordinate

The marked coordinate may be outside the finite prefix; in that case its
coefficient is exactly zero and the original section is constant. This includes
the last marked gap in the finite stopping-time decomposition.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Interval

theorem fluxFacetCoef_eq_zero_of_le (eps : ℝ) {k i : ℕ} (hi : k ≤ i)
    (q : FluxFacetIndex k) : fluxFacetCoef eps q i = 0 := by
  have h0 : ¬ i < (q.1 : ℕ) := by omega
  have h1 : ¬ i < (q.2.1 : ℕ) := by omega
  have h2 : ¬ i < (q.2.2.1 : ℕ) := by omega
  simp [fluxFacetCoef, h0, h1, h2]

theorem flux_prefix_update_iff_all {eps x : ℝ} {g : ℕ → ℝ} {k i : ℕ}
    (hk : 2 ≤ k) (hx : 0 < x) (hg : ∀ j < k, j ≠ i → 0 < g j) :
    prefixAffineFeasible eps (gapKeys (Function.update g i x)) (k + 1) ↔
      ∀ q : FluxFacetIndex k, fluxFacetCoef eps q i * x ≤ fluxPrefixRHS eps k i q g := by
  by_cases hi : i < k
  · exact flux_prefix_update_iff hk hi hx hg
  have hki : k ≤ i := Nat.le_of_not_gt hi
  have hpos : ∀ j < k, 0 < Function.update g i x j := by
    intro j hj
    rw [Function.update_of_ne (by omega : j ≠ i)]
    exact hg j hj (by omega)
  rw [flux_prefix_iff_constraints hk hpos]
  apply forall_congr'
  intro q
  have he : (∑ j ∈ Finset.range k, fluxFacetCoef eps q j * Function.update g i x j) =
      ∑ j ∈ Finset.range k, fluxFacetCoef eps q j * g j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (by have := Finset.mem_range.mp hj; omega : j ≠ i)]
  rw [he, fluxFacetCoef_eq_zero_of_le eps hki q, zero_mul, fluxPrefixRHS,
    Finset.erase_eq_of_notMem (by simpa only [Finset.mem_range] using hi)]
  constructor <;> intro h <;> linarith

theorem flux_prefix_weighted_eq_poly_all {ν : ProbabilityMeasure ℝ}
    (hpos : ∀ᵐ x ∂(ν : Measure ℝ), 0 < x) (P : Measure (ℕ → ℝ)) (hP : P ≪ iidLaw ν)
    (eps : ℝ) {k : ℕ} (hk : 2 ≤ k) (i : ℕ) (F : (ℕ → ℝ) → ℝ → ℝ)
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
    exact flux_prefix_update_iff_all hk hx (fun l _ _ => hg l)
  simp only [indicator_apply, mem_ofPred_eq, he]

theorem flux_prefix_moving_weight_primitive_bound {ν : ProbabilityMeasure ℝ}
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
    ∃ j : ℝ → ℝ, AEPrimitive (fluxPrefixWeighted P eps k i F) j ∧
      ∀ R : ℝ, (∫ x in Ι (0 : ℝ) R, ‖j x‖) ≤
        |R| * (∫ g, Bf R g ∂P) + 2 * ∫ g, BF R g ∂P := by
  have hroot (q : FluxFacetIndex k) :
      (P.map (fun g => fluxPrefixRHS eps k i q g / fluxFacetCoef eps q i)).restrict (Ioi 0) ≪ volume :=
    ((hP.map ((measurable_fluxPrefixRHS eps k i q).div_const _)).restrict (Ioi 0)).trans
      (fluxPrefixRHS_root_ac hac eps k i q)
  obtain ⟨j, ⟨hI, a, ha⟩, hb⟩ := fluxPoly_weighted_primitive_bound P
    (fun q : FluxFacetIndex k => fluxFacetCoef eps q i)
    (fun q => measurable_fluxPrefixRHS eps k i q) hroot hFm hfm hBFi hBfi hBF hBf hF
  refine ⟨j, ⟨hI, a, ?_⟩, hb⟩
  filter_upwards [ha, ae_restrict_mem measurableSet_Ioi] with x hax hx
  rw [flux_prefix_weighted_eq_poly_all hpos P hP eps hk i F hx]
  exact hax

end
end PGM
