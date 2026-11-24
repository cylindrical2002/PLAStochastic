import PLAStochastic.Index.GEP.Kernel.Influence.Coarea.FacetPath

/-!
# The physical active-event measure in actual coarea coordinates

Positivity is retained inside the weight. This supplies the pointwise support
needed by coarea, rather than using an almost-everywhere statement about the
original iid path on an arbitrarily reconstructed path.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal

/-- Positive physical gaps and the original feasible prefix. -/
def kernelIFPathEvent (eps : ℝ) (k : ℕ) : Set (ℕ → ℝ) :=
  {g | (∀ l < k, 0 < g l) ∧ prefixAffineFeasible eps (gapKeys g) (k + 1)}

theorem measurableSet_kernelIFPathEvent (eps : ℝ) (k : ℕ) :
    MeasurableSet (kernelIFPathEvent eps k) := by
  have hp : MeasurableSet {g : ℕ → ℝ | ∀ l < k, 0 < g l} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun l => MeasurableSet.iInter fun _ =>
      measurableSet_lt measurable_const (measurable_pi_apply l)
  exact hp.inter (measurable_gapKeys (measurableSet_prefixAffineFeasible eps (k + 1)))

/-- A reward evaluated on the actual positive feasible path. -/
def kernelIFPathWeight (eps : ℝ) (k : ℕ) (W : (ℕ → ℝ) → ℝ≥0∞) :
    (ℕ → ℝ) → ℝ≥0∞ := (kernelIFPathEvent eps k).indicator W

/-- The original facet weight, before replacing either smoothing coordinate. -/
def kernelIFActiveWeight (eps : ℝ) (k i : ℕ) (q : FluxFacetIndex k)
    (W : (ℕ → ℝ) → ℝ≥0∞) (g : ℕ → ℝ) : ℝ≥0∞ :=
  kernelIFPathWeight eps k W (Function.update g i (kernelFacetRoot eps k i q g))

theorem measurable_kernelIFPathWeight (eps : ℝ) (k : ℕ)
    {W : (ℕ → ℝ) → ℝ≥0∞} (hW : Measurable W) :
    Measurable (kernelIFPathWeight eps k W) :=
  hW.indicator (measurableSet_kernelIFPathEvent eps k)

theorem measurable_kernelIFActiveWeight (eps : ℝ) (k i : ℕ)
    (q : FluxFacetIndex k) {W : (ℕ → ℝ) → ℝ≥0∞} (hW : Measurable W) :
    Measurable (kernelIFActiveWeight eps k i q W) :=
  (measurable_kernelIFPathWeight eps k hW).comp
    ((measurable_update_pair i).comp
      ((measurable_kernelFacetRoot eps k i q).prodMk measurable_id))

/-- Positivity of a bridge disjoint from the designated gap is a pointwise
support property of the actual facet weight. -/
theorem kernel_IF_activeWeight_block_support {eps : ℝ} {k i r s : ℕ}
    (q : FluxFacetIndex k) (W : (ℕ → ℝ) → ℝ≥0∞) (hrs : r < s) (hsk : s ≤ k)
    (hi : i < r ∨ s ≤ i) (g : ℕ → ℝ)
    (hbad : gapKeys g s - gapKeys g r ≤ 0) : kernelIFActiveWeight eps k i q W g = 0 := by
  apply Set.indicator_of_notMem
  intro hg
  have hp := cert_gapKeys_lt hg.1 r s hrs hsk
  have he := kernel_block_sum_update_outside g hrs.le hi (kernelFacetRoot eps k i q g)
  linarith

/-- The left coarea density keeps the full reward and the actual active event. -/
def kernelIFLeftDensity (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ≥0∞)
    (eps : ℝ) {k : ℕ} (q : FluxFacetIndex k) (i j m : ℕ)
    (W : (ℕ → ℝ) → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ g, (∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (kernelFacetQ eps q / a ^ 2) *
    (f (kernelFacetP eps q / a - x - kernelFacetRestA q i j g) *
      f (kernelFacetQ eps q / a - kernelFacetRestB q m g) *
        kernelIFPathWeight eps k W (kernelIFLeftPath eps x a q i j m g))) ∂iidLaw ν

/-- The right coarea density, with its own reciprocal coefficient and Jacobian. -/
def kernelIFRightDensity (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ≥0∞)
    (eps : ℝ) {k : ℕ} (q : FluxFacetIndex k) (i j m : ℕ)
    (W : (ℕ → ℝ) → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ g, (∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (kernelFacetP eps q / a ^ 2) *
    (f (kernelFacetQ eps q / a - x - kernelFacetRestRight q i j g) *
      f (kernelFacetP eps q / a - kernelFacetRestLeft q m g) *
        kernelIFPathWeight eps k W (kernelIFRightPath eps x a q i j m g))) ∂iidLaw ν

theorem measurable_kernelIFLeftDensity (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (eps : ℝ) {k : ℕ}
    (q : FluxFacetIndex k) (i j m : ℕ) {W : (ℕ → ℝ) → ℝ≥0∞} (hW : Measurable W) :
    Measurable (kernelIFLeftDensity ν f eps q i j m W) := by
  have hpath := (measurable_kernelIFLeftPath eps q i j m).comp
    (show Measurable (fun z : (ℝ × (ℕ → ℝ)) × ℝ => ((z.1.1, z.2), z.1.2)) by fun_prop)
  have hweight := (measurable_kernelIFPathWeight eps k hW).comp hpath
  have hrestA : Measurable (kernelFacetRestA q i j) := by
    unfold kernelFacetRestA gapKeys
    fun_prop
  have hrestB : Measurable (kernelFacetRestB q m) := by
    unfold kernelFacetRestB gapKeys
    fun_prop
  have h : Measurable (fun z : (ℝ × (ℕ → ℝ)) × ℝ =>
      ENNReal.ofReal (kernelFacetQ eps q / z.2 ^ 2) *
        (f (kernelFacetP eps q / z.2 - z.1.1 - kernelFacetRestA q i j z.1.2) *
          f (kernelFacetQ eps q / z.2 - kernelFacetRestB q m z.1.2) *
            kernelIFPathWeight eps k W (kernelIFLeftPath eps z.1.1 z.2 q i j m z.1.2))) := by
    apply Measurable.mul (by fun_prop)
    exact ((hf.comp (by fun_prop)).mul (hf.comp (by fun_prop))).mul hweight
  exact (h.lintegral_prod_right').lintegral_prod_right'

theorem measurable_kernelIFRightDensity (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (eps : ℝ) {k : ℕ}
    (q : FluxFacetIndex k) (i j m : ℕ) {W : (ℕ → ℝ) → ℝ≥0∞} (hW : Measurable W) :
    Measurable (kernelIFRightDensity ν f eps q i j m W) := by
  have hpath := (measurable_kernelIFRightPath eps q i j m).comp
    (show Measurable (fun z : (ℝ × (ℕ → ℝ)) × ℝ => ((z.1.1, z.2), z.1.2)) by fun_prop)
  have hweight := (measurable_kernelIFPathWeight eps k hW).comp hpath
  have hrestA : Measurable (kernelFacetRestRight q i j) := by
    unfold kernelFacetRestRight gapKeys
    fun_prop
  have hrestB : Measurable (kernelFacetRestLeft q m) := by
    unfold kernelFacetRestLeft gapKeys
    fun_prop
  have h : Measurable (fun z : (ℝ × (ℕ → ℝ)) × ℝ =>
      ENNReal.ofReal (kernelFacetP eps q / z.2 ^ 2) *
        (f (kernelFacetQ eps q / z.2 - z.1.1 - kernelFacetRestRight q i j z.1.2) *
          f (kernelFacetP eps q / z.2 - kernelFacetRestLeft q m z.1.2) *
            kernelIFPathWeight eps k W (kernelIFRightPath eps z.1.1 z.2 q i j m z.1.2))) := by
    apply Measurable.mul (by fun_prop)
    exact ((hf.comp (by fun_prop)).mul (hf.comp (by fun_prop))).mul hweight
  exact (h.lintegral_prod_right').lintegral_prod_right'

/-- The original weighted active-facet measure has exactly the physical left
coarea density. No independent replacement of the selected path is used. -/
theorem kernel_IF_left_map_density (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hν : (ν : Measure ℝ) = volume.withDensity f)
    {eps : ℝ} {k i j m : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (hi₁ : (q.1 : ℕ) ≤ i) (hi₂ : i < q.2.1)
    (hj₁ : (q.1 : ℕ) ≤ j) (hj₂ : j < q.2.1) (hji : j ≠ i)
    (hm₁ : (q.2.1 : ℕ) ≤ m) (hm₂ : m < q.2.2.1)
    {W : (ℕ → ℝ) → ℝ≥0∞} (hW : Measurable W) :
    ((iidLaw ν).withDensity (kernelIFActiveWeight eps k i q W)).map
      (kernelFacetRoot eps k i q) =
        volume.withDensity (kernelIFLeftDensity ν f eps q i j m W) := by
  have h := kernel_actual_facet_map_coarea ν hf hν hq hi₁ hi₂ hj₁ hj₂ hji hm₁ hm₂
    (measurable_kernelIFActiveWeight eps k i q hW)
    (kernel_IF_activeWeight_block_support q W hq.1.2
      (by have := q.2.2.1.isLt; omega) (Or.inl hi₂))
  rw [h]
  congr 1
  funext x
  apply lintegral_congr
  intro g
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
  change 0 < a at ha
  unfold kernelCoareaIIDWeight kernelIFActiveWeight
  rw [kernel_IF_left_root hq ha.ne' hi₁ hi₂ hj₁ hj₂ hji hm₁ hm₂]
  rfl

theorem kernel_IF_right_map_density (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hν : (ν : Measure ℝ) = volume.withDensity f)
    {eps : ℝ} {k i j m : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (hi₁ : (q.2.1 : ℕ) ≤ i) (hi₂ : i < q.2.2.1)
    (hj₁ : (q.2.1 : ℕ) ≤ j) (hj₂ : j < q.2.2.1) (hji : j ≠ i)
    (hm₁ : (q.1 : ℕ) ≤ m) (hm₂ : m < q.2.1)
    {W : (ℕ → ℝ) → ℝ≥0∞} (hW : Measurable W) :
    ((iidLaw ν).withDensity (kernelIFActiveWeight eps k i q W)).map
      (kernelFacetRoot eps k i q) =
        volume.withDensity (kernelIFRightDensity ν f eps q i j m W) := by
  have h := kernel_actual_facet_map_coarea_right ν hf hν hq hi₁ hi₂ hj₁ hj₂ hji hm₁ hm₂
    (measurable_kernelIFActiveWeight eps k i q hW)
    (kernel_IF_activeWeight_block_support q W hq.1.1
      (by have := q.2.2.1.isLt; have := hq.1.2; omega) (Or.inr hi₁))
  rw [h]
  congr 1
  funext x
  apply lintegral_congr
  intro g
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
  change 0 < a at ha
  unfold kernelCoareaIIDWeight kernelIFActiveWeight
  rw [kernel_IF_right_root hq ha.ne' hi₁ hi₂ hj₁ hj₂ hji hm₁ hm₂]
  rfl

/-- The previously constructed candidate density is the physical coarea
density on the positive half-line. This is an equality of the original
representatives almost everywhere, not a new choice of a flux kernel. -/
theorem kernel_IF_left_candidate_ae (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hν : (ν : Measure ℝ) = volume.withDensity f)
    {eps : ℝ} {k i j m : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (hi₁ : (q.1 : ℕ) ≤ i) (hi₂ : i < q.2.1)
    (hj₁ : (q.1 : ℕ) ≤ j) (hj₂ : j < q.2.1) (hji : j ≠ i)
    (hm₁ : (q.2.1 : ℕ) ≤ m) (hm₂ : m < q.2.2.1)
    {W : (ℕ → ℝ) → ℝ≥0∞} (hW : Measurable W) :
    kernelFacetCandidateDensity ν f eps k i q (kernelIFActiveWeight eps k i q W)
      =ᵐ[volume.restrict (Ioi (0 : ℝ))] kernelIFLeftDensity ν f eps q i j m W := by
  have h := kernel_facet_root_positive_density ν hf hν eps k i q
    (measurable_kernelIFActiveWeight eps k i q hW)
  change (((iidLaw ν).withDensity (kernelIFActiveWeight eps k i q W)).map
    (kernelFacetRoot eps k i q)).restrict (Ioi 0) = _ at h
  rw [kernel_IF_left_map_density ν hf hν hq hi₁ hi₂ hj₁ hj₂ hji hm₁ hm₂ hW,
    restrict_withDensity measurableSet_Ioi, restrict_withDensity measurableSet_Ioi] at h
  exact (withDensity_eq_iff_of_sigmaFinite
    (measurable_kernelFacetCandidateDensity ν hf eps k i q
      (measurable_kernelIFActiveWeight eps k i q hW)).aemeasurable
    (measurable_kernelIFLeftDensity ν hf eps q i j m hW).aemeasurable).mp h.symm

theorem kernel_IF_right_candidate_ae (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hν : (ν : Measure ℝ) = volume.withDensity f)
    {eps : ℝ} {k i j m : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (hi₁ : (q.2.1 : ℕ) ≤ i) (hi₂ : i < q.2.2.1)
    (hj₁ : (q.2.1 : ℕ) ≤ j) (hj₂ : j < q.2.2.1) (hji : j ≠ i)
    (hm₁ : (q.1 : ℕ) ≤ m) (hm₂ : m < q.2.1)
    {W : (ℕ → ℝ) → ℝ≥0∞} (hW : Measurable W) :
    kernelFacetCandidateDensity ν f eps k i q (kernelIFActiveWeight eps k i q W)
      =ᵐ[volume.restrict (Ioi (0 : ℝ))] kernelIFRightDensity ν f eps q i j m W := by
  have h := kernel_facet_root_positive_density ν hf hν eps k i q
    (measurable_kernelIFActiveWeight eps k i q hW)
  change (((iidLaw ν).withDensity (kernelIFActiveWeight eps k i q W)).map
    (kernelFacetRoot eps k i q)).restrict (Ioi 0) = _ at h
  rw [kernel_IF_right_map_density ν hf hν hq hi₁ hi₂ hj₁ hj₂ hji hm₁ hm₂ hW,
    restrict_withDensity measurableSet_Ioi, restrict_withDensity measurableSet_Ioi] at h
  exact (withDensity_eq_iff_of_sigmaFinite
    (measurable_kernelFacetCandidateDensity ν hf eps k i q
      (measurable_kernelIFActiveWeight eps k i q hW)).aemeasurable
    (measurable_kernelIFRightDensity ν hf eps q i j m hW).aemeasurable).mp h.symm

end
end PGM
