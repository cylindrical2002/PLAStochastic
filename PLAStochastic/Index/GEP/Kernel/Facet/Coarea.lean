import PLAStochastic.Index.GEP.Kernel.Facet.IIDCoarea
import PLAStochastic.Index.GEP.Kernel.Facet.Ties

/-!
# Coarea coordinates for the original finite-prefix facet

The smoothing coordinates are chosen in the two actual bridge blocks. The
linear root is the original `fluxPrefixRHS / fluxFacetCoef`, not a substituted
random variable. All other coordinates and the full active-event weight are
retained by the iid coarea theorem.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal

def kernelFacetP (eps : ℝ) {k : ℕ} (q : FluxFacetIndex k) : ℝ :=
  (q.2.1 : ℕ) - (q.1 : ℝ) - 2 * fluxFacetSign q * eps

def kernelFacetQ (eps : ℝ) {k : ℕ} (q : FluxFacetIndex k) : ℝ :=
  (q.2.2.1 : ℕ) - (q.2.1 : ℝ) + 2 * fluxFacetSign q * eps

def kernelFacetRoot (eps : ℝ) (k i : ℕ) (q : FluxFacetIndex k) (g : ℕ → ℝ) : ℝ :=
  fluxPrefixRHS eps k i q g / fluxFacetCoef eps q i

theorem measurable_kernelFacetRoot (eps : ℝ) (k i : ℕ) (q : FluxFacetIndex k) :
    Measurable (kernelFacetRoot eps k i q) :=
  (measurable_fluxPrefixRHS eps k i q).div_const _

theorem kernel_linear_sum_update (T : Finset ℕ) (c g : ℕ → ℝ) {j : ℕ} (hj : j ∈ T) (u : ℝ) :
    (∑ l ∈ T, c l * Function.update g j u l) =
      (∑ l ∈ T, c l * g l) + c j * (u - g j) := by
  classical
  rw [← sum_erase_add T (fun l => c l * Function.update g j u l) hj,
    ← sum_erase_add T (fun l => c l * g l) hj, Function.update_self]
  have he : (∑ l ∈ T.erase j, c l * Function.update g j u l) =
      ∑ l ∈ T.erase j, c l * g l := by
    apply sum_congr rfl
    intro l hl
    rw [Function.update_of_ne (ne_of_mem_erase hl)]
  rw [he]
  ring

theorem kernel_facet_root_update (eps : ℝ) (k i : ℕ) (q : FluxFacetIndex k)
    (g : ℕ → ℝ) {j : ℕ} (hj : j < k) (hji : j ≠ i) (u : ℝ) :
    kernelFacetRoot eps k i q (Function.update g j u) =
      kernelFacetRoot eps k i q g + kernelFacetRootCoef eps q i j * (u - g j) := by
  unfold kernelFacetRoot
  simp_rw [kernel_facet_root_eq_sum]
  exact kernel_linear_sum_update _ _ g (mem_erase.mpr ⟨hji, mem_range.mpr hj⟩) u

theorem kernel_facet_root_left_coef {eps : ℝ} {k i j : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (hi₁ : (q.1 : ℕ) ≤ i) (hi₂ : i < q.2.1)
    (hj₁ : (q.1 : ℕ) ≤ j) (hj₂ : j < q.2.1) :
    kernelFacetRootCoef eps q i j = -1 := by
  have hQ : kernelFacetQ eps q ≠ 0 := hq.2.2.ne'
  have hs := kernel_fluxFacetSign_ne_zero q
  unfold kernelFacetRootCoef
  rw [kernel_facet_coef_left hq.1 hj₁ hj₂, kernel_facet_coef_left hq.1 hi₁ hi₂]
  change -(-fluxFacetSign q * kernelFacetQ eps q) / (-fluxFacetSign q * kernelFacetQ eps q) = -1
  field_simp

theorem kernel_facet_root_right_coef {eps : ℝ} {k i m : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (hi₁ : (q.1 : ℕ) ≤ i) (hi₂ : i < q.2.1)
    (hm₁ : (q.2.1 : ℕ) ≤ m) (hm₂ : m < q.2.2.1) :
    kernelFacetRootCoef eps q i m = kernelFacetP eps q / kernelFacetQ eps q := by
  have hQ : kernelFacetQ eps q ≠ 0 := hq.2.2.ne'
  have hs := kernel_fluxFacetSign_ne_zero q
  unfold kernelFacetRootCoef
  rw [kernel_facet_coef_right hq.1 hm₁ hm₂, kernel_facet_coef_left hq.1 hi₁ hi₂]
  change -(fluxFacetSign q * kernelFacetP eps q) / (-fluxFacetSign q * kernelFacetQ eps q) = _
  field_simp

/-- Exact physical-block formula for an insertion in the first bridge. -/
theorem kernel_facet_root_blocks {eps : ℝ} {k i : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (hi₁ : (q.1 : ℕ) ≤ i) (hi₂ : i < q.2.1)
    (g : ℕ → ℝ) :
    kernelFacetRoot eps k i q g =
      kernelFacetP eps q / kernelFacetQ eps q * (gapKeys g q.2.2.1 - gapKeys g q.2.1) -
        (gapKeys g q.2.1 - gapKeys g q.1) + g i := by
  have hi : i < k := by have := q.2.2.1.isLt; have := hq.1.2; omega
  have hs := kernel_fluxFacetSign_ne_zero q
  have hQ : kernelFacetQ eps q ≠ 0 := hq.2.2.ne'
  have hcoef : fluxFacetCoef eps q i = -fluxFacetSign q * kernelFacetQ eps q :=
    kernel_facet_coef_left hq.1 hi₁ hi₂
  have hsum := fluxFacetCoef_sum eps q hq.1 g
  have hupdate := kernel_facet_update_sum eps (g i) hi q g
  simp only [Function.update_eq_self, hcoef] at hupdate
  rw [hsum] at hupdate
  change fluxFacetSign q * (kernelFacetP eps q * (gapKeys g q.2.2.1 - gapKeys g q.2.1) -
      kernelFacetQ eps q * (gapKeys g q.2.1 - gapKeys g q.1)) =
      -fluxFacetSign q * kernelFacetQ eps q * g i - fluxPrefixRHS eps k i q g at hupdate
  unfold kernelFacetRoot
  rw [hcoef]
  apply (div_eq_iff (mul_ne_zero (neg_ne_zero.mpr hs) hQ)).mpr
  field_simp
  nlinarith [hupdate]

/-- The remaining physical first and second block sums after removing the
designated gap and the two smoothing coordinates. -/
def kernelFacetRestA {k : ℕ} (q : FluxFacetIndex k) (i j : ℕ) (g : ℕ → ℝ) : ℝ :=
  gapKeys g q.2.1 - gapKeys g q.1 - g i - g j

def kernelFacetRestB {k : ℕ} (q : FluxFacetIndex k) (m : ℕ) (g : ℕ → ℝ) : ℝ :=
  gapKeys g q.2.2.1 - gapKeys g q.2.1 - g m

/-- The original facet root has exactly the affine coordinates required by
the actual iid coarea theorem. -/
theorem kernel_facet_root_two_update {eps : ℝ} {k i j m : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (hi₁ : (q.1 : ℕ) ≤ i) (hi₂ : i < q.2.1)
    (hj₁ : (q.1 : ℕ) ≤ j) (hj₂ : j < q.2.1) (hji : j ≠ i)
    (hm₁ : (q.2.1 : ℕ) ≤ m) (hm₂ : m < q.2.2.1) (g : ℕ → ℝ) (u v : ℝ) :
    kernelFacetRoot eps k i q (Function.update (Function.update g j u) m v) =
      kernelFacetP eps q / kernelFacetQ eps q * (v + kernelFacetRestB q m g) -
        u - kernelFacetRestA q i j g := by
  have hjk : j < k := by have := q.2.2.1.isLt; have := hq.1.2; omega
  have hmk : m < k := by have := q.2.2.1.isLt; omega
  have hmi : m ≠ i := by omega
  have hmj : m ≠ j := by omega
  rw [kernel_facet_root_update eps k i q _ hmk hmi v,
    kernel_facet_root_update eps k i q _ hjk hji u, Function.update_of_ne hmj,
    kernel_facet_root_left_coef hq hi₁ hi₂ hj₁ hj₂,
    kernel_facet_root_right_coef hq hi₁ hi₂ hm₁ hm₂,
    kernel_facet_root_blocks hq hi₁ hi₂]
  unfold kernelFacetRestA kernelFacetRestB
  ring

theorem kernel_gapKeys_update_affine (g : ℕ → ℝ) (j : ℕ) (u : ℝ) (n : ℕ) :
    gapKeys (Function.update g j u) n = gapKeys g n + if j < n then u - g j else 0 := by
  classical
  by_cases hj : j < n
  · rw [if_pos hj]
    exact (by simpa only [one_mul, gapKeys] using
      kernel_linear_sum_update (range n) (fun _ => (1 : ℝ)) g (mem_range.mpr hj) u)
  · simp only [if_neg hj, add_zero]
    unfold gapKeys
    apply sum_congr rfl
    intro l hl
    exact Function.update_of_ne (by have := mem_range.mp hl; omega) _ _

theorem kernel_facet_second_block_two_update {k j m : ℕ} {q : FluxFacetIndex k}
    (hq : fluxFacetValid q) (hj : j < q.2.1)
    (hm₁ : (q.2.1 : ℕ) ≤ m) (hm₂ : m < q.2.2.1) (g : ℕ → ℝ) (u v : ℝ) :
    gapKeys (Function.update (Function.update g j u) m v) q.2.2.1 -
      gapKeys (Function.update (Function.update g j u) m v) q.2.1 =
        v + kernelFacetRestB q m g := by
  have hjt : j < q.2.2.1 := lt_trans hj hq.2
  have hms : ¬m < q.2.1 := by omega
  have hmj : m ≠ j := by omega
  simp only [kernel_gapKeys_update_affine, hj, hjt, hm₂, hms, if_true, if_false,
    Function.update_of_ne hmj, kernelFacetRestB]
  ring

/-- Coarea for an effective original facet, with an arbitrary measurable
active weight supported on its physical positive second block. All affine
root and Jacobian assumptions of the generic theorem are discharged here. -/
theorem kernel_actual_facet_map_coarea (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hν : (ν : Measure ℝ) = volume.withDensity f)
    {eps : ℝ} {k i j m : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (hi₁ : (q.1 : ℕ) ≤ i) (hi₂ : i < q.2.1)
    (hj₁ : (q.1 : ℕ) ≤ j) (hj₂ : j < q.2.1) (hji : j ≠ i)
    (hm₁ : (q.2.1 : ℕ) ≤ m) (hm₂ : m < q.2.2.1)
    {W : (ℕ → ℝ) → ℝ≥0∞} (hW : Measurable W)
    (hpos : ∀ g, gapKeys g q.2.2.1 - gapKeys g q.2.1 ≤ 0 → W g = 0) :
    ((iidLaw ν).withDensity W).map (kernelFacetRoot eps k i q) =
      volume.withDensity (kernelCoareaIIDDensity ν f j m (kernelFacetP eps q) (kernelFacetQ eps q)
        (kernelFacetRestA q i j) (kernelFacetRestB q m) W) := by
  have hc : Measurable (kernelFacetRestA q i j) := by
    unfold kernelFacetRestA gapKeys
    fun_prop
  have hd : Measurable (kernelFacetRestB q m) := by
    unfold kernelFacetRestB gapKeys
    fun_prop
  apply kernel_iid_facet_map_slope_density ν hf hν j m hq.2.1 hq.2.2 hc hd
    (measurable_kernelFacetRoot eps k i q)
    (kernel_facet_root_two_update hq hi₁ hi₂ hj₁ hj₂ hji hm₁ hm₂) hW
  intro g u v hv
  unfold kernelCoareaIIDWeight
  rw [hpos _ ?_, mul_zero]
  rwa [kernel_facet_second_block_two_update hq.1 hj₂ hm₁ hm₂]

end
end PGM
