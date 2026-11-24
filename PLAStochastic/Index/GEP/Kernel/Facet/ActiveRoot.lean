import PLAStochastic.Index.GEP.Kernel.Facet.EndpointDensity
import PLAStochastic.Index.GEP.Kernel.Facet.BandPath

/-!
# Actual active facet roots and their canonical band paths

The finite coefficients and the one-gap roots used in the density construction
are identified with the signed three-point width of the original updated keys.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Finset

theorem kernel_fluxFacetSign_cases {k : ℕ} (q : FluxFacetIndex k) :
    fluxFacetSign q = 1 ∨ fluxFacetSign q = -1 := by
  unfold fluxFacetSign
  split_ifs <;> simp

theorem kernel_fluxFacetSign_ne_zero {k : ℕ} (q : FluxFacetIndex k) :
    fluxFacetSign q ≠ 0 := by
  rcases kernel_fluxFacetSign_cases q with h | h <;> rw [h] <;> norm_num

theorem kernel_fluxFacetValid_of_coef_ne_zero {eps : ℝ} {k i : ℕ}
    {q : FluxFacetIndex k} (hc : fluxFacetCoef eps q i ≠ 0) : fluxFacetValid q := by
  by_contra h
  exact hc (by simp [fluxFacetCoef, h])

theorem kernel_facet_update_sum (eps x : ℝ) {k i : ℕ} (hi : i < k)
    (q : FluxFacetIndex k) (g : ℕ → ℝ) :
    (∑ j ∈ range k, fluxFacetCoef eps q j * Function.update g i x j) =
      fluxFacetCoef eps q i * x - fluxPrefixRHS eps k i q g := by
  rw [← Finset.sum_erase_add (range k)
    (fun j => fluxFacetCoef eps q j * Function.update g i x j) (mem_range.mpr hi),
    Function.update_self]
  have he : (∑ j ∈ (range k).erase i, fluxFacetCoef eps q j * Function.update g i x j) =
      ∑ j ∈ (range k).erase i, fluxFacetCoef eps q j * g j := by
    apply sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (ne_of_mem_erase hj)]
  rw [he]
  unfold fluxPrefixRHS
  ring

theorem kernel_facet_sum_zero_iff_width {eps : ℝ} {k : ℕ} (q : FluxFacetIndex k)
    (hq : fluxFacetValid q) (g : ℕ → ℝ)
    (hAB : gapKeys g q.2.2.1 - gapKeys g q.1 ≠ 0) :
    (∑ j ∈ range k, fluxFacetCoef eps q j * g j) = 0 ↔
      fluxSignedWidth ((q.2.1 : ℕ) - (q.1 : ℝ))
        ((q.2.2.1 : ℕ) - (q.2.1 : ℝ))
        (gapKeys g q.2.1 - gapKeys g q.1)
        (gapKeys g q.2.2.1 - gapKeys g q.2.1) = fluxFacetSign q * eps := by
  rw [fluxFacetCoef_sum eps q hq g, mul_eq_zero]
  have hs := kernel_fluxFacetSign_ne_zero q
  simp only [hs, false_or]
  rw [flux_boundary_linear (by convert hAB using 1; ring)]
  unfold fluxFacet
  constructor <;> intro h <;> linarith

/-- The actual one-gap root is exactly the geometric active signed width. -/
theorem kernel_facet_root_iff_width {eps x : ℝ} {k i : ℕ} (hi : i < k)
    (q : FluxFacetIndex k) (hc : fluxFacetCoef eps q i ≠ 0) (g : ℕ → ℝ)
    (hAB : gapKeys (Function.update g i x) q.2.2.1 -
      gapKeys (Function.update g i x) q.1 ≠ 0) :
    x = fluxPrefixRHS eps k i q g / fluxFacetCoef eps q i ↔
      fluxSignedWidth ((q.2.1 : ℕ) - (q.1 : ℝ))
        ((q.2.2.1 : ℕ) - (q.2.1 : ℝ))
        (gapKeys (Function.update g i x) q.2.1 - gapKeys (Function.update g i x) q.1)
        (gapKeys (Function.update g i x) q.2.2.1 - gapKeys (Function.update g i x) q.2.1) =
        fluxFacetSign q * eps := by
  rw [← kernel_facet_sum_zero_iff_width q (kernel_fluxFacetValid_of_coef_ne_zero hc)
    (Function.update g i x) hAB, kernel_facet_update_sum eps x hi q g,
    eq_div_iff hc]
  constructor <;> intro h <;> nlinarith

/-- At a positive actual facet root the full original prefix event becomes the
canonical band event, including all points outside the three contacts. -/
theorem kernel_active_root_band_iff {eps x : ℝ} {k i : ℕ} (hi : i < k)
    (q : FluxFacetIndex k) (g : ℕ → ℝ) (hx : 0 < x)
    (hg : ∀ j < k, j ≠ i → 0 < g j)
    (hroot : x = fluxPrefixRHS eps k i q g / fluxFacetCoef eps q i) :
    prefixAffineFeasible eps (gapKeys (Function.update g i x)) (k + 1) ↔
      ∀ j ≤ k, kernelFacetBandCoord eps (fluxFacetSign q)
        (gapKeys (Function.update g i x)) q.1 q.2.1 q.2.2.1 j ∈ Icc 0 (2 * eps) := by
  have hc : fluxFacetCoef eps q i ≠ 0 := by
    intro he
    rw [he, div_zero] at hroot
    exact (ne_of_gt hx) hroot
  have hq := kernel_fluxFacetValid_of_coef_ne_zero hc
  have hpos : ∀ j < k, 0 < Function.update g i x j := by
    intro j hj
    by_cases hji : j = i
    · subst j
      simpa using hx
    · simpa only [Function.update_of_ne hji] using hg j hj hji
  have hAB : gapKeys (Function.update g i x) q.2.2.1 -
      gapKeys (Function.update g i x) q.1 ≠ 0 :=
    (sub_pos.mpr (cert_gapKeys_lt hpos _ _ (lt_trans hq.1 hq.2) (by omega))).ne'
  exact kernel_updated_gap_prefix_facet_band_iff hx hg hq.1 hq.2 (by omega)
    (kernel_fluxFacetSign_cases q) ((kernel_facet_root_iff_width hi q hc g hAB).mp hroot)

/-- A facet is effective when both physical-length numerators are positive. -/
def kernelFacetEffective (eps : ℝ) {k : ℕ} (q : FluxFacetIndex k) : Prop :=
  fluxFacetValid q ∧
    0 < ((q.2.1 : ℕ) : ℝ) - q.1 - 2 * fluxFacetSign q * eps ∧
    0 < ((q.2.2.1 : ℕ) : ℝ) - q.2.1 + 2 * fluxFacetSign q * eps

theorem kernel_active_root_effective {eps x : ℝ} {k i : ℕ} (hi : i < k)
    (q : FluxFacetIndex k) (g : ℕ → ℝ) (hx : 0 < x)
    (hg : ∀ j < k, j ≠ i → 0 < g j)
    (hroot : x = fluxPrefixRHS eps k i q g / fluxFacetCoef eps q i) :
    kernelFacetEffective eps q := by
  have hc : fluxFacetCoef eps q i ≠ 0 := by
    intro he
    rw [he, div_zero] at hroot
    exact (ne_of_gt hx) hroot
  have hq := kernel_fluxFacetValid_of_coef_ne_zero hc
  have hpos : ∀ j < k, 0 < Function.update g i x j := by
    intro j hj
    by_cases hji : j = i
    · subst j
      simpa using hx
    · simpa only [Function.update_of_ne hji] using hg j hj hji
  have hA := sub_pos.mpr (cert_gapKeys_lt hpos _ _ hq.1 (by omega))
  have hB := sub_pos.mpr (cert_gapKeys_lt hpos _ _ hq.2 (by omega))
  have hAB : gapKeys (Function.update g i x) q.2.2.1 -
      gapKeys (Function.update g i x) q.1 ≠ 0 := by linarith
  have hLM : 0 < (((q.2.1 : ℕ) : ℝ) - q.1) +
      (((q.2.2.1 : ℕ) : ℝ) - q.2.1) := by
    have ht : (q.1 : ℝ) < q.2.2.1 := by exact_mod_cast lt_trans hq.1 hq.2
    linarith
  exact ⟨hq, flux_boundary_numerators_pos hA hB hLM
    ((kernel_facet_root_iff_width hi q hc g hAB).mp hroot)⟩

end
end PGM
