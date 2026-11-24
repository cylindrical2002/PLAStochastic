import PLAStochastic.Index.GEP.Kernel.Facet.Coarea

/-!
# Coarea for an insertion in the second bridge

The two smoothing gaps remain in their actual disjoint bridge blocks. This is
the second orientation of the original facet, with its reciprocal coefficient
and the corresponding Jacobian.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal

def kernelFacetRestRight {k : ℕ} (q : FluxFacetIndex k) (i j : ℕ)
    (g : ℕ → ℝ) : ℝ :=
  gapKeys g q.2.2.1 - gapKeys g q.2.1 - g i - g j

def kernelFacetRestLeft {k : ℕ} (q : FluxFacetIndex k) (m : ℕ)
    (g : ℕ → ℝ) : ℝ :=
  gapKeys g q.2.1 - gapKeys g q.1 - g m

theorem kernel_facet_root_blocks_right {eps : ℝ} {k i : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (hi₁ : (q.2.1 : ℕ) ≤ i) (hi₂ : i < q.2.2.1)
    (g : ℕ → ℝ) :
    kernelFacetRoot eps k i q g =
      kernelFacetQ eps q / kernelFacetP eps q * (gapKeys g q.2.1 - gapKeys g q.1) -
        (gapKeys g q.2.2.1 - gapKeys g q.2.1) + g i := by
  have hi : i < k := by have := q.2.2.1.isLt; omega
  have hs := kernel_fluxFacetSign_ne_zero q
  have hP : kernelFacetP eps q ≠ 0 := hq.2.1.ne'
  have hcoef : fluxFacetCoef eps q i = fluxFacetSign q * kernelFacetP eps q :=
    kernel_facet_coef_right hq.1 hi₁ hi₂
  have hsum := fluxFacetCoef_sum eps q hq.1 g
  have hupdate := kernel_facet_update_sum eps (g i) hi q g
  simp only [Function.update_eq_self, hcoef] at hupdate
  rw [hsum] at hupdate
  change fluxFacetSign q * (kernelFacetP eps q * (gapKeys g q.2.2.1 - gapKeys g q.2.1) -
      kernelFacetQ eps q * (gapKeys g q.2.1 - gapKeys g q.1)) =
      fluxFacetSign q * kernelFacetP eps q * g i - fluxPrefixRHS eps k i q g at hupdate
  unfold kernelFacetRoot
  rw [hcoef]
  apply (div_eq_iff (mul_ne_zero hs hP)).mpr
  field_simp
  nlinarith [hupdate]

theorem kernel_facet_first_block_two_update {k j m : ℕ} {q : FluxFacetIndex k}
    (hq : fluxFacetValid q) (hj : (q.2.1 : ℕ) ≤ j)
    (hm₁ : (q.1 : ℕ) ≤ m) (hm₂ : m < q.2.1) (g : ℕ → ℝ) (u v : ℝ) :
    gapKeys (Function.update (Function.update g j u) m v) q.2.1 -
      gapKeys (Function.update (Function.update g j u) m v) q.1 =
        v + kernelFacetRestLeft q m g := by
  have hjr : ¬j < q.1 := by have := hq.1; omega
  have hjs : ¬j < q.2.1 := by omega
  have hmr : ¬m < q.1 := by omega
  have hmj : m ≠ j := by omega
  simp only [kernel_gapKeys_update_affine, hjr, hjs, hm₂, hmr, if_true, if_false,
    Function.update_of_ne hmj, kernelFacetRestLeft]
  ring

theorem kernel_facet_root_two_update_right {eps : ℝ} {k i j m : ℕ}
    {q : FluxFacetIndex k} (hq : kernelFacetEffective eps q)
    (hi₁ : (q.2.1 : ℕ) ≤ i) (hi₂ : i < q.2.2.1)
    (hj₁ : (q.2.1 : ℕ) ≤ j) (hj₂ : j < q.2.2.1) (hji : j ≠ i)
    (hm₁ : (q.1 : ℕ) ≤ m) (hm₂ : m < q.2.1) (g : ℕ → ℝ) (u v : ℝ) :
    kernelFacetRoot eps k i q (Function.update (Function.update g j u) m v) =
      kernelFacetQ eps q / kernelFacetP eps q * (v + kernelFacetRestLeft q m g) -
        u - kernelFacetRestRight q i j g := by
  have hjs : ¬j < q.2.1 := by omega
  have hms : m < q.2.1 := hm₂
  have hmt : m < q.2.2.1 := lt_trans hm₂ hq.1.2
  have hmi : i ≠ m := by omega
  have hij : i ≠ j := hji.symm
  have hmj : m ≠ j := by omega
  rw [kernel_facet_root_blocks_right hq hi₁ hi₂,
    kernel_facet_first_block_two_update hq.1 hj₁ hm₁ hm₂]
  simp only [kernel_gapKeys_update_affine, hj₂, hjs, hms, hmt, if_true, if_false,
    Function.update_of_ne hmi, Function.update_of_ne hij, Function.update_of_ne hmj,
    kernelFacetRestRight]
  ring

/-- The actual second-bridge facet pushforward, with the physical first-block
support condition and every remaining path coordinate retained. -/
theorem kernel_actual_facet_map_coarea_right (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hν : (ν : Measure ℝ) = volume.withDensity f)
    {eps : ℝ} {k i j m : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (hi₁ : (q.2.1 : ℕ) ≤ i) (hi₂ : i < q.2.2.1)
    (hj₁ : (q.2.1 : ℕ) ≤ j) (hj₂ : j < q.2.2.1) (hji : j ≠ i)
    (hm₁ : (q.1 : ℕ) ≤ m) (hm₂ : m < q.2.1)
    {W : (ℕ → ℝ) → ℝ≥0∞} (hW : Measurable W)
    (hpos : ∀ g, gapKeys g q.2.1 - gapKeys g q.1 ≤ 0 → W g = 0) :
    ((iidLaw ν).withDensity W).map (kernelFacetRoot eps k i q) =
      volume.withDensity (kernelCoareaIIDDensity ν f j m (kernelFacetQ eps q) (kernelFacetP eps q)
        (kernelFacetRestRight q i j) (kernelFacetRestLeft q m) W) := by
  have hc : Measurable (kernelFacetRestRight q i j) := by
    unfold kernelFacetRestRight gapKeys
    fun_prop
  have hd : Measurable (kernelFacetRestLeft q m) := by
    unfold kernelFacetRestLeft gapKeys
    fun_prop
  apply kernel_iid_facet_map_slope_density ν hf hν j m hq.2.2 hq.2.1 hc hd
    (measurable_kernelFacetRoot eps k i q)
    (kernel_facet_root_two_update_right hq hi₁ hi₂ hj₁ hj₂ hji hm₁ hm₂) hW
  intro g u v hv
  unfold kernelCoareaIIDWeight
  rw [hpos _ ?_, mul_zero]
  rwa [kernel_facet_first_block_two_update hq.1 hj₁ hm₁ hm₂]

end
end PGM
