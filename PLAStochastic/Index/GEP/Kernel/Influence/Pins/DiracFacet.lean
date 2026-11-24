import PLAStochastic.Index.GEP.Kernel.Influence.Pins.OuterSurvival

/-!
# The actual one-gap facet and its deterministic marked bridge

Only one random smoothing coordinate remains. Its affine pushforward is taken
from the original candidate root, including the full active path reward.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option maxHeartbeats 1200000

theorem kernel_facet_root_left_short {eps : ℝ} {k : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (hshort : (q.1 : ℕ)+1 = q.2.1) (g : ℕ → ℝ) :
    kernelFacetRoot eps k q.1 q g =
      kernelFacetP eps q / kernelFacetQ eps q * (gapKeys g q.2.2.1-gapKeys g q.2.1) := by
  have hs : gapKeys g q.2.1-gapKeys g q.1 = g q.1 := by
    rw [← hshort]
    simp only [gapKeys, Finset.sum_range_succ]
    ring
  rw [kernel_facet_root_blocks hq le_rfl hq.1.1, hs]
  ring

theorem kernel_facet_root_left_short_update {eps : ℝ} {k m : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (hshort : (q.1 : ℕ)+1 = q.2.1)
    (hm₁ : (q.2.1 : ℕ) ≤ m) (hm₂ : m < q.2.2.1) (g : ℕ → ℝ) (v : ℝ) :
    kernelFacetRoot eps k q.1 q (Function.update g m v) =
      kernelFacetP eps q / kernelFacetQ eps q * (kernelFacetRestB q m g+v) := by
  rw [kernel_facet_root_left_short hq hshort,
    kernel_block_sum_update_inside _ hm₁ hm₂]
  unfold kernelFacetRestB
  ring

def kernelIFLeftShortPath (eps x : ℝ) {k : ℕ} (q : FluxFacetIndex k)
    (m : ℕ) (g : ℕ → ℝ) : ℕ → ℝ :=
  Function.update (Function.update g m
    (kernelFacetQ eps q/kernelFacetP eps q*x-kernelFacetRestB q m g)) q.1 x

def kernelIFLeftShortDensity (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ≥0∞)
    (eps : ℝ) {k : ℕ} (q : FluxFacetIndex k) (m : ℕ)
    (W : (ℕ → ℝ) → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (kernelFacetQ eps q/kernelFacetP eps q) *
    ∫⁻ g, f (kernelFacetQ eps q/kernelFacetP eps q*x-kernelFacetRestB q m g) *
      kernelIFPathWeight eps k W (kernelIFLeftShortPath eps x q m g) ∂iidLaw ν

theorem measurable_kernelIFLeftShortDensity (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (eps : ℝ) {k : ℕ}
    (q : FluxFacetIndex k) (m : ℕ) {W : (ℕ → ℝ) → ℝ≥0∞} (hW : Measurable W) :
    Measurable (kernelIFLeftShortDensity ν f eps q m W) := by
  have hrest : Measurable (kernelFacetRestB q m) := by
    unfold kernelFacetRestB gapKeys
    fun_prop
  have hp : Measurable (fun p : ℝ × (ℕ → ℝ) => kernelIFLeftShortPath eps p.1 q m p.2) := by
    unfold kernelIFLeftShortPath
    exact (measurable_update_pair (q.1 : ℕ)).comp
      (measurable_fst.prodMk ((measurable_update_pair m).comp
        ((show Measurable (fun p : ℝ × (ℕ → ℝ) =>
          kernelFacetQ eps q/kernelFacetP eps q*p.1-kernelFacetRestB q m p.2) by fun_prop).prodMk
            measurable_snd)))
  have h : Measurable (fun p : ℝ × (ℕ → ℝ) =>
      f (kernelFacetQ eps q/kernelFacetP eps q*p.1-kernelFacetRestB q m p.2) *
        kernelIFPathWeight eps k W (kernelIFLeftShortPath eps p.1 q m p.2)) :=
    (hf.comp (by fun_prop)).mul ((measurable_kernelIFPathWeight eps k hW).comp hp)
  exact measurable_const.mul h.lintegral_prod_right'

theorem kernel_IF_left_short_map_density (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hν : (ν : Measure ℝ) = volume.withDensity f)
    {eps : ℝ} {k m : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (hshort : (q.1 : ℕ)+1 = q.2.1)
    (hm₁ : (q.2.1 : ℕ) ≤ m) (hm₂ : m < q.2.2.1)
    {W : (ℕ → ℝ) → ℝ≥0∞} (hW : Measurable W) :
    ((iidLaw ν).withDensity (kernelIFActiveWeight eps k q.1 q W)).map
      (kernelFacetRoot eps k q.1 q) =
        volume.withDensity (kernelIFLeftShortDensity ν f eps q m W) := by
  have hP : kernelFacetP eps q ≠ 0 := hq.2.1.ne'
  have hQ : kernelFacetQ eps q ≠ 0 := hq.2.2.ne'
  have hb : Measurable (fun g => kernelFacetP eps q/kernelFacetQ eps q * kernelFacetRestB q m g) := by
    unfold kernelFacetRestB gapKeys
    fun_prop
  have hmap := kernel_iid_affine_map_density ν hf hν m (div_ne_zero hP hQ)
    (measurable_kernelFacetRoot eps k q.1 q) hb
    (by intro g v; rw [kernel_facet_root_left_short_update hq hshort hm₁ hm₂]; ring)
    (measurable_kernelIFActiveWeight eps k q.1 q hW)
  rw [hmap]
  congr 1
  funext x
  have hc : |(kernelFacetP eps q/kernelFacetQ eps q)⁻¹| =
      kernelFacetQ eps q/kernelFacetP eps q := by
    rw [inv_div, abs_of_pos (show 0 < kernelFacetQ eps q/kernelFacetP eps q from div_pos hq.2.2 hq.2.1)]
  unfold kernelLinearDensity kernelIFLeftShortDensity
  rw [hc]
  congr 1
  apply lintegral_congr
  intro g
  have he : (x-kernelFacetP eps q/kernelFacetQ eps q*kernelFacetRestB q m g) /
      (kernelFacetP eps q/kernelFacetQ eps q) =
        kernelFacetQ eps q/kernelFacetP eps q*x-kernelFacetRestB q m g := by
    field_simp
  rw [he]
  unfold kernelIIDRootWeight kernelIFActiveWeight
  have hr : kernelFacetRoot eps k q.1 q (Function.update g m
      (kernelFacetQ eps q/kernelFacetP eps q*x-kernelFacetRestB q m g)) = x := by
    rw [kernel_facet_root_left_short_update hq hshort hm₁ hm₂]
    field_simp
    ring
  rw [hr]
  rfl

theorem kernel_IF_left_short_candidate_ae (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hν : (ν : Measure ℝ) = volume.withDensity f)
    {eps : ℝ} {k m : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (hshort : (q.1 : ℕ)+1 = q.2.1)
    (hm₁ : (q.2.1 : ℕ) ≤ m) (hm₂ : m < q.2.2.1)
    {W : (ℕ → ℝ) → ℝ≥0∞} (hW : Measurable W) :
    kernelFacetCandidateDensity ν f eps k q.1 q (kernelIFActiveWeight eps k q.1 q W)
      =ᵐ[volume.restrict (Ioi 0)] kernelIFLeftShortDensity ν f eps q m W := by
  have h := kernel_facet_root_positive_density ν hf hν eps k q.1 q
    (measurable_kernelIFActiveWeight eps k q.1 q hW)
  change (((iidLaw ν).withDensity (kernelIFActiveWeight eps k q.1 q W)).map
    (kernelFacetRoot eps k q.1 q)).restrict (Ioi 0) = _ at h
  rw [kernel_IF_left_short_map_density ν hf hν hq hshort hm₁ hm₂ hW,
    restrict_withDensity measurableSet_Ioi, restrict_withDensity measurableSet_Ioi] at h
  exact (withDensity_eq_iff_of_sigmaFinite
    (measurable_kernelFacetCandidateDensity ν hf eps k q.1 q
      (measurable_kernelIFActiveWeight eps k q.1 q hW)).aemeasurable
    (measurable_kernelIFLeftShortDensity ν hf eps q m hW).aemeasurable).mp h.symm

theorem kernel_facet_root_right_short {eps : ℝ} {k : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (hshort : (q.2.1 : ℕ)+1 = q.2.2.1) (g : ℕ → ℝ) :
    kernelFacetRoot eps k q.2.1 q g =
      kernelFacetQ eps q / kernelFacetP eps q * (gapKeys g q.2.1-gapKeys g q.1) := by
  have hs : gapKeys g q.2.2.1-gapKeys g q.2.1 = g q.2.1 := by
    rw [← hshort]
    simp only [gapKeys, Finset.sum_range_succ]
    ring
  rw [kernel_facet_root_blocks_right hq le_rfl hq.1.2, hs]
  ring

theorem kernel_facet_root_right_short_update {eps : ℝ} {k m : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (hshort : (q.2.1 : ℕ)+1 = q.2.2.1)
    (hm₁ : (q.1 : ℕ) ≤ m) (hm₂ : m < q.2.1) (g : ℕ → ℝ) (v : ℝ) :
    kernelFacetRoot eps k q.2.1 q (Function.update g m v) =
      kernelFacetQ eps q / kernelFacetP eps q * (kernelFacetRestLeft q m g+v) := by
  rw [kernel_facet_root_right_short hq hshort,
    kernel_block_sum_update_inside _ hm₁ hm₂]
  unfold kernelFacetRestLeft
  ring

def kernelIFRightShortPath (eps x : ℝ) {k : ℕ} (q : FluxFacetIndex k)
    (m : ℕ) (g : ℕ → ℝ) : ℕ → ℝ :=
  Function.update (Function.update g m
    (kernelFacetP eps q/kernelFacetQ eps q*x-kernelFacetRestLeft q m g)) q.2.1 x

def kernelIFRightShortDensity (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ≥0∞)
    (eps : ℝ) {k : ℕ} (q : FluxFacetIndex k) (m : ℕ)
    (W : (ℕ → ℝ) → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (kernelFacetP eps q/kernelFacetQ eps q) *
    ∫⁻ g, f (kernelFacetP eps q/kernelFacetQ eps q*x-kernelFacetRestLeft q m g) *
      kernelIFPathWeight eps k W (kernelIFRightShortPath eps x q m g) ∂iidLaw ν

theorem measurable_kernelIFRightShortDensity (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (eps : ℝ) {k : ℕ}
    (q : FluxFacetIndex k) (m : ℕ) {W : (ℕ → ℝ) → ℝ≥0∞} (hW : Measurable W) :
    Measurable (kernelIFRightShortDensity ν f eps q m W) := by
  have hrest : Measurable (kernelFacetRestLeft q m) := by
    unfold kernelFacetRestLeft gapKeys
    fun_prop
  have hp : Measurable (fun p : ℝ × (ℕ → ℝ) => kernelIFRightShortPath eps p.1 q m p.2) := by
    unfold kernelIFRightShortPath
    exact (measurable_update_pair (q.2.1 : ℕ)).comp
      (measurable_fst.prodMk ((measurable_update_pair m).comp
        ((show Measurable (fun p : ℝ × (ℕ → ℝ) =>
          kernelFacetP eps q/kernelFacetQ eps q*p.1-kernelFacetRestLeft q m p.2) by fun_prop).prodMk
            measurable_snd)))
  have h : Measurable (fun p : ℝ × (ℕ → ℝ) =>
      f (kernelFacetP eps q/kernelFacetQ eps q*p.1-kernelFacetRestLeft q m p.2) *
        kernelIFPathWeight eps k W (kernelIFRightShortPath eps p.1 q m p.2)) :=
    (hf.comp (by fun_prop)).mul ((measurable_kernelIFPathWeight eps k hW).comp hp)
  exact measurable_const.mul h.lintegral_prod_right'

theorem kernel_IF_right_short_map_density (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hν : (ν : Measure ℝ) = volume.withDensity f)
    {eps : ℝ} {k m : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (hshort : (q.2.1 : ℕ)+1 = q.2.2.1)
    (hm₁ : (q.1 : ℕ) ≤ m) (hm₂ : m < q.2.1)
    {W : (ℕ → ℝ) → ℝ≥0∞} (hW : Measurable W) :
    ((iidLaw ν).withDensity (kernelIFActiveWeight eps k q.2.1 q W)).map
      (kernelFacetRoot eps k q.2.1 q) =
        volume.withDensity (kernelIFRightShortDensity ν f eps q m W) := by
  have hP : kernelFacetQ eps q ≠ 0 := hq.2.2.ne'
  have hQ : kernelFacetP eps q ≠ 0 := hq.2.1.ne'
  have hb : Measurable (fun g => kernelFacetQ eps q/kernelFacetP eps q * kernelFacetRestLeft q m g) := by
    unfold kernelFacetRestLeft gapKeys
    fun_prop
  have hmap := kernel_iid_affine_map_density ν hf hν m (div_ne_zero hP hQ)
    (measurable_kernelFacetRoot eps k q.2.1 q) hb
    (by intro g v; rw [kernel_facet_root_right_short_update hq hshort hm₁ hm₂]; ring)
    (measurable_kernelIFActiveWeight eps k q.2.1 q hW)
  rw [hmap]
  congr 1
  funext x
  have hc : |(kernelFacetQ eps q/kernelFacetP eps q)⁻¹| =
      kernelFacetP eps q/kernelFacetQ eps q := by
    rw [inv_div, abs_of_pos (show 0 < kernelFacetP eps q/kernelFacetQ eps q from div_pos hq.2.1 hq.2.2)]
  unfold kernelLinearDensity kernelIFRightShortDensity
  rw [hc]
  congr 1
  apply lintegral_congr
  intro g
  have he : (x-kernelFacetQ eps q/kernelFacetP eps q*kernelFacetRestLeft q m g) /
      (kernelFacetQ eps q/kernelFacetP eps q) =
        kernelFacetP eps q/kernelFacetQ eps q*x-kernelFacetRestLeft q m g := by
    field_simp
  rw [he]
  unfold kernelIIDRootWeight kernelIFActiveWeight
  have hr : kernelFacetRoot eps k q.2.1 q (Function.update g m
      (kernelFacetP eps q/kernelFacetQ eps q*x-kernelFacetRestLeft q m g)) = x := by
    rw [kernel_facet_root_right_short_update hq hshort hm₁ hm₂]
    field_simp
    ring
  rw [hr]
  rfl

theorem kernel_IF_right_short_candidate_ae (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hν : (ν : Measure ℝ) = volume.withDensity f)
    {eps : ℝ} {k m : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (hshort : (q.2.1 : ℕ)+1 = q.2.2.1)
    (hm₁ : (q.1 : ℕ) ≤ m) (hm₂ : m < q.2.1)
    {W : (ℕ → ℝ) → ℝ≥0∞} (hW : Measurable W) :
    kernelFacetCandidateDensity ν f eps k q.2.1 q (kernelIFActiveWeight eps k q.2.1 q W)
      =ᵐ[volume.restrict (Ioi 0)] kernelIFRightShortDensity ν f eps q m W := by
  have h := kernel_facet_root_positive_density ν hf hν eps k q.2.1 q
    (measurable_kernelIFActiveWeight eps k q.2.1 q hW)
  change (((iidLaw ν).withDensity (kernelIFActiveWeight eps k q.2.1 q W)).map
    (kernelFacetRoot eps k q.2.1 q)).restrict (Ioi 0) = _ at h
  rw [kernel_IF_right_short_map_density ν hf hν hq hshort hm₁ hm₂ hW,
    restrict_withDensity measurableSet_Ioi, restrict_withDensity measurableSet_Ioi] at h
  exact (withDensity_eq_iff_of_sigmaFinite
    (measurable_kernelFacetCandidateDensity ν hf eps k q.2.1 q
      (measurable_kernelIFActiveWeight eps k q.2.1 q hW)).aemeasurable
    (measurable_kernelIFRightShortDensity ν hf eps q m hW).aemeasurable).mp h.symm

end
end PGM
