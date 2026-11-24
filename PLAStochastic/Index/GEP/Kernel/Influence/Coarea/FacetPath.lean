import PLAStochastic.Index.GEP.Kernel.Facet.CoareaRight
import PLAStochastic.Index.GEP.Kernel.Facet.FourBlocks

/-!
# The actual path on a coarea facet

Both smoothing gaps and the designated gap are reinserted into the same path.
Its two physical bridge sums, its chord slope and its active signed width are
exact identities. The original prefix indicator therefore factors into the
four actual killed blocks at the integration slope.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Finset

theorem kernel_block_sum_update_inside (g : ℕ → ℝ) {r s j : ℕ}
    (hrj : r ≤ j) (hjs : j < s) (u : ℝ) :
    gapKeys (Function.update g j u) s - gapKeys (Function.update g j u) r =
      gapKeys g s - gapKeys g r + u - g j := by
  simp only [kernel_gapKeys_update_affine, hjs, show ¬j < r by omega,
    if_true, if_false]
  ring

theorem kernel_block_sum_update_outside (g : ℕ → ℝ) {r s j : ℕ}
    (hrs : r ≤ s) (hj : j < r ∨ s ≤ j) (u : ℝ) :
    gapKeys (Function.update g j u) s - gapKeys (Function.update g j u) r =
      gapKeys g s - gapKeys g r := by
  rcases hj with hj | hj
  · simp only [kernel_gapKeys_update_affine, hj, lt_of_lt_of_le hj hrs, if_true]
    ring
  · simp only [kernel_gapKeys_update_affine, show ¬j < s by omega,
      show ¬j < r by omega, if_false, add_zero]

/-- The smoothing gaps for a designated gap in the first bridge. -/
def kernelIFLeftPath (eps x a : ℝ) {k : ℕ} (q : FluxFacetIndex k)
    (i j m : ℕ) (g : ℕ → ℝ) : ℕ → ℝ :=
  Function.update (Function.update (Function.update g j
    (kernelFacetP eps q / a - x - kernelFacetRestA q i j g)) m
      (kernelFacetQ eps q / a - kernelFacetRestB q m g)) i x

/-- The smoothing gaps for a designated gap in the second bridge. -/
def kernelIFRightPath (eps x a : ℝ) {k : ℕ} (q : FluxFacetIndex k)
    (i j m : ℕ) (g : ℕ → ℝ) : ℕ → ℝ :=
  Function.update (Function.update (Function.update g j
    (kernelFacetQ eps q / a - x - kernelFacetRestRight q i j g)) m
      (kernelFacetP eps q / a - kernelFacetRestLeft q m g)) i x

theorem measurable_kernelIFLeftPath (eps : ℝ) {k : ℕ} (q : FluxFacetIndex k)
    (i j m : ℕ) : Measurable (fun z : (ℝ × ℝ) × (ℕ → ℝ) =>
      kernelIFLeftPath eps z.1.1 z.1.2 q i j m z.2) := by
  unfold kernelIFLeftPath kernelFacetRestA kernelFacetRestB gapKeys
  fun_prop

theorem measurable_kernelIFRightPath (eps : ℝ) {k : ℕ} (q : FluxFacetIndex k)
    (i j m : ℕ) : Measurable (fun z : (ℝ × ℝ) × (ℕ → ℝ) =>
      kernelIFRightPath eps z.1.1 z.1.2 q i j m z.2) := by
  unfold kernelIFRightPath kernelFacetRestRight kernelFacetRestLeft gapKeys
  fun_prop

theorem kernel_IF_left_sums {eps x a : ℝ} {k i j m : ℕ} {q : FluxFacetIndex k}
    (hq : fluxFacetValid q) (hi₁ : (q.1 : ℕ) ≤ i) (hi₂ : i < q.2.1)
    (hj₁ : (q.1 : ℕ) ≤ j) (hj₂ : j < q.2.1) (hji : j ≠ i)
    (hm₁ : (q.2.1 : ℕ) ≤ m) (hm₂ : m < q.2.2.1) (g : ℕ → ℝ) :
    gapKeys (kernelIFLeftPath eps x a q i j m g) q.2.1 -
        gapKeys (kernelIFLeftPath eps x a q i j m g) q.1 = kernelFacetP eps q / a ∧
    gapKeys (kernelIFLeftPath eps x a q i j m g) q.2.2.1 -
        gapKeys (kernelIFLeftPath eps x a q i j m g) q.2.1 = kernelFacetQ eps q / a := by
  have hmi : i ≠ m := by omega
  have hmj : m ≠ j := by omega
  unfold kernelIFLeftPath
  constructor
  · rw [kernel_block_sum_update_inside _ hi₁ hi₂,
      kernel_block_sum_update_outside _ hq.1.le (Or.inr hm₁),
      kernel_block_sum_update_inside _ hj₁ hj₂]
    simp only [Function.update_of_ne hmi, Function.update_of_ne hji.symm, kernelFacetRestA]
    ring
  · rw [kernel_block_sum_update_outside _ hq.2.le (Or.inl hi₂),
      kernel_block_sum_update_inside _ hm₁ hm₂,
      kernel_block_sum_update_outside _ hq.2.le (Or.inl hj₂)]
    simp only [Function.update_of_ne hmj, kernelFacetRestB]
    ring

theorem kernel_IF_right_sums {eps x a : ℝ} {k i j m : ℕ} {q : FluxFacetIndex k}
    (hq : fluxFacetValid q) (hi₁ : (q.2.1 : ℕ) ≤ i) (hi₂ : i < q.2.2.1)
    (hj₁ : (q.2.1 : ℕ) ≤ j) (hj₂ : j < q.2.2.1) (hji : j ≠ i)
    (hm₁ : (q.1 : ℕ) ≤ m) (hm₂ : m < q.2.1) (g : ℕ → ℝ) :
    gapKeys (kernelIFRightPath eps x a q i j m g) q.2.1 -
        gapKeys (kernelIFRightPath eps x a q i j m g) q.1 = kernelFacetP eps q / a ∧
    gapKeys (kernelIFRightPath eps x a q i j m g) q.2.2.1 -
        gapKeys (kernelIFRightPath eps x a q i j m g) q.2.1 = kernelFacetQ eps q / a := by
  have hmi : i ≠ m := by omega
  have hmj : m ≠ j := by omega
  unfold kernelIFRightPath
  constructor
  · rw [kernel_block_sum_update_outside _ hq.1.le (Or.inr hi₁),
      kernel_block_sum_update_inside _ hm₁ hm₂,
      kernel_block_sum_update_outside _ hq.1.le (Or.inr hj₁)]
    simp only [Function.update_of_ne hmj, kernelFacetRestLeft]
    ring
  · rw [kernel_block_sum_update_inside _ hi₁ hi₂,
      kernel_block_sum_update_outside _ hq.2.le (Or.inl hm₂),
      kernel_block_sum_update_inside _ hj₁ hj₂]
    simp only [Function.update_of_ne hmi, Function.update_of_ne hji.symm,
      kernelFacetRestRight]
    ring

/-- The original root is precisely the integration variable before the
designated coordinate is reinserted. -/
theorem kernel_IF_left_root {eps x a : ℝ} {k i j m : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (ha : a ≠ 0)
    (hi₁ : (q.1 : ℕ) ≤ i) (hi₂ : i < q.2.1)
    (hj₁ : (q.1 : ℕ) ≤ j) (hj₂ : j < q.2.1) (hji : j ≠ i)
    (hm₁ : (q.2.1 : ℕ) ≤ m) (hm₂ : m < q.2.2.1) (g : ℕ → ℝ) :
    kernelFacetRoot eps k i q
      (Function.update (Function.update g j
        (kernelFacetP eps q / a - x - kernelFacetRestA q i j g)) m
          (kernelFacetQ eps q / a - kernelFacetRestB q m g)) = x := by
  rw [kernel_facet_root_two_update hq hi₁ hi₂ hj₁ hj₂ hji hm₁ hm₂]
  have hQ : kernelFacetQ eps q ≠ 0 := hq.2.2.ne'
  field_simp [hQ]
  ring

theorem kernel_IF_right_root {eps x a : ℝ} {k i j m : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (ha : a ≠ 0)
    (hi₁ : (q.2.1 : ℕ) ≤ i) (hi₂ : i < q.2.2.1)
    (hj₁ : (q.2.1 : ℕ) ≤ j) (hj₂ : j < q.2.2.1) (hji : j ≠ i)
    (hm₁ : (q.1 : ℕ) ≤ m) (hm₂ : m < q.2.1) (g : ℕ → ℝ) :
    kernelFacetRoot eps k i q
      (Function.update (Function.update g j
        (kernelFacetQ eps q / a - x - kernelFacetRestRight q i j g)) m
          (kernelFacetP eps q / a - kernelFacetRestLeft q m g)) = x := by
  rw [kernel_facet_root_two_update_right hq hi₁ hi₂ hj₁ hj₂ hji hm₁ hm₂]
  have hP : kernelFacetP eps q ≠ 0 := hq.2.1.ne'
  field_simp [hP]
  ring

theorem kernel_IF_slope_of_sums {eps a : ℝ} {k : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (ha : a ≠ 0) (g : ℕ → ℝ)
    (hA : gapKeys g q.2.1 - gapKeys g q.1 = kernelFacetP eps q / a)
    (hB : gapKeys g q.2.2.1 - gapKeys g q.2.1 = kernelFacetQ eps q / a) :
    fluxSlope ((q.2.1 : ℕ) - (q.1 : ℝ)) ((q.2.2.1 : ℕ) - (q.2.1 : ℝ))
      (gapKeys g q.2.1 - gapKeys g q.1) (gapKeys g q.2.2.1 - gapKeys g q.2.1) = a := by
  have hPQ : kernelFacetP eps q + kernelFacetQ eps q ≠ 0 := (add_pos hq.2.1 hq.2.2).ne'
  have he : ((q.2.1 : ℕ) - (q.1 : ℝ)) + ((q.2.2.1 : ℕ) - (q.2.1 : ℝ)) =
      kernelFacetP eps q + kernelFacetQ eps q := by
    unfold kernelFacetP kernelFacetQ
    ring
  unfold fluxSlope
  rw [hA, hB, ← add_div, he]
  field_simp

theorem kernel_IF_width_of_sums {eps a : ℝ} {k : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (ha : 0 < a) (g : ℕ → ℝ)
    (hA : gapKeys g q.2.1 - gapKeys g q.1 = kernelFacetP eps q / a)
    (hB : gapKeys g q.2.2.1 - gapKeys g q.2.1 = kernelFacetQ eps q / a) :
    fluxSignedWidth ((q.2.1 : ℕ) - (q.1 : ℝ)) ((q.2.2.1 : ℕ) - (q.2.1 : ℝ))
      (gapKeys g q.2.1 - gapKeys g q.1) (gapKeys g q.2.2.1 - gapKeys g q.2.1) =
        fluxFacetSign q * eps := by
  have hAB : (gapKeys g q.2.1 - gapKeys g q.1) +
      (gapKeys g q.2.2.1 - gapKeys g q.2.1) ≠ 0 := by
    rw [hA, hB]
    exact (add_pos (div_pos hq.2.1 ha) (div_pos hq.2.2 ha)).ne'
  rw [flux_boundary_linear hAB, hA, hB]
  change kernelFacetP eps q * (kernelFacetQ eps q / a) =
    kernelFacetQ eps q * (kernelFacetP eps q / a)
  ring

/-- Four-block survival at the actual integration slope, for any path with
the two exact physical sums supplied by the coarea reconstruction. -/
theorem kernel_IF_indicator_of_sums {eps a : ℝ} {k : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (ha : 0 < a) (g : ℕ → ℝ)
    (hg : ∀ l < k, 0 < g l)
    (hA : gapKeys g q.2.1 - gapKeys g q.1 = kernelFacetP eps q / a)
    (hB : gapKeys g q.2.2.1 - gapKeys g q.2.1 = kernelFacetQ eps q / a) :
    {h : ℕ → ℝ | prefixAffineFeasible eps (gapKeys h) (k+1)}.indicator
      (fun _ => (1 : ℝ)) g =
      krAlive (Icc 0 (2*eps)) (-1) (-a) q.1 (eps - fluxFacetSign q * eps)
        (kernelReversePrefix g q.1) *
      (krAlive (Icc 0 (2*eps)) 1 a (q.2.1-q.1) (eps - fluxFacetSign q * eps)
        (fun l => g (l+q.1)) *
      (krAlive (Icc 0 (2*eps)) 1 a (q.2.2.1-q.2.1) (eps + fluxFacetSign q * eps)
        (fun l => g (l+q.2.1)) *
      krAlive (Icc 0 (2*eps)) 1 a (k-q.2.2.1) (eps - fluxFacetSign q * eps)
        (fun l => g (l+q.2.2.1)))) := by
  have h := kernel_prefix_facet_indicator_blocks hg hq.1.1 hq.1.2
    (show (q.2.2.1 : ℕ) ≤ k by have := q.2.2.1.isLt; omega)
    (kernel_fluxFacetSign_cases q) (kernel_IF_width_of_sums hq ha g hA hB)
  dsimp only at h
  rwa [kernel_IF_slope_of_sums hq ha.ne' g hA hB] at h

end
end PGM
