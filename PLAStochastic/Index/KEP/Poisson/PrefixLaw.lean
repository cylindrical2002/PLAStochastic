import PLAStochastic.Index.KEP.Poisson.PrefixTransitions
import PLAStochastic.ForMathlib.Probability.Kernel.FromNoise

/-!
# The actual Poisson child prefix law is a Markov-kernel iteration

The representation uses the original child functional and independent fresh
exponential innovations at its natural completed rank. Finiteness of the
leading child block at every anchor suffices; parent finiteness is not assumed.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory

def kepPoissonPrefixUpdate {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (j i : ℕ)
    (p : (ℕ → ℝ) × (ℕ → ℝ)) : ℕ → ℝ :=
  let y := kepPoissonParentAnchor hf eps n x j (gapKeys p.1 i)
  Function.update p.1 i ((f x / f y) * kepPoissonLayerGap hf eps n y j p.2)

theorem measurable_kepPoissonPrefixUpdate {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (j i : ℕ) :
    Measurable (kepPoissonPrefixUpdate hf eps n x j i) := by
  have hS : Measurable (fun p : (ℕ → ℝ) × (ℕ → ℝ) => gapKeys p.1 i) :=
    ((measurable_pi_apply i).comp measurable_gapKeys).comp measurable_fst
  have hy := (measurable_kepPoissonParentAnchor hf eps n x j).comp hS
  have hgap := (measurable_kepPoissonLayerGap hf eps n j).comp (hy.prodMk measurable_snd)
  exact (measurable_sequenceUpdate i).comp
    (measurable_fst.prodMk ((measurable_const.div (hf.continuous.measurable.comp hy)).mul hgap))

theorem kepPoissonPrefixKernel_apply {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (j i : ℕ) (g : ℕ → ℝ) :
    kepPoissonPrefixKernel hf eps n x j i g =
      expSeqMeasure.map (fun z => kepPoissonPrefixUpdate hf eps n x j i (g, z)) := by
  let y := kepPoissonParentAnchor hf eps n x j (gapKeys g i)
  have hD : Measurable (fun z : ℝ => (f x / f y) * z) := measurable_const.mul measurable_id
  have hU : Measurable (fun z : ℝ => Function.update g i z) :=
    (measurable_sequenceUpdate i).comp (measurable_const.prodMk measurable_id)
  rw [kepPoissonPrefixKernel, sequenceUpdateKernel_apply,
    kepPoissonPrefixGapKernel, Kernel.comap_apply, kepPoissonParentStepKernel_apply]
  change ((kepPoissonLayerMeasure hf eps n y j).map (fun z => (f x / f y) * z)).map
    (fun z => Function.update g i z) = _
  rw [Measure.map_map hU hD, kepPoissonLayerMeasure,
    Measure.map_map (hU.comp hD) (measurable_kepPoissonLayerGap_anchor hf eps n y j)]
  rfl

theorem kepPoissonPrefixKernel_eq_fromNoise {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (j i : ℕ) :
    kepPoissonPrefixKernel hf eps n x j i =
      kernelFromNoise expSeqMeasure (kepPoissonPrefixUpdate hf eps n x j i) := by
  ext g : 1
  rw [kepPoissonPrefixKernel_apply,
    kernelFromNoise_apply expSeqMeasure (measurable_kepPoissonPrefixUpdate hf eps n x j i)]

theorem kepPoissonPrefixKernel_comp {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (j i : ℕ)
    (mu : Measure (ℕ → ℝ)) [IsProbabilityMeasure mu] :
    kepPoissonPrefixKernel hf eps n x j i ∘ₘ mu =
      (mu.prod expSeqMeasure).map (kepPoissonPrefixUpdate hf eps n x j i) := by
  rw [kepPoissonPrefixKernel_eq_fromNoise,
    kernelFromNoise_comp expSeqMeasure (measurable_kepPoissonPrefixUpdate hf eps n x j i)]

theorem kepPoissonPrefixState_succ_law {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) {eps n x : ℝ} (hn : n ≠ 0) (j i : ℕ)
    (hm : kepReferenceSpan eps j ≠ 0)
    (hfin : ∀ a : ℕ, ∀ᵐ g ∂expSeqMeasure, kepPoissonPivot hf eps n x j a g ≠ ⊤) :
    expSeqMeasure.map (kepPoissonPrefixState hf eps n x j (i + 1)) =
      kepPoissonPrefixKernel hf eps n x j i ∘ₘ
        (expSeqMeasure.map (kepPoissonPrefixState hf eps n x j i)) := by
  let : IsProbabilityMeasure (expSeqMeasure.map (kepPoissonPrefixState hf eps n x j i)) :=
    Measure.isProbabilityMeasure_map (measurable_kepPoissonPrefixState hf eps n x j i).aemeasurable
  have hnext : kepPoissonPrefixState hf eps n x j (i + 1) =ᵐ[expSeqMeasure]
      fun g => kepPoissonPrefixUpdate hf eps n x j i
        (kepPoissonPrefixState hf eps n x j i g,
          shiftBy (kepPoissonPivot hf eps n x j i) g) := by
    filter_upwards [hfin (i + 1)] with g hg
    rw [kepPoissonPrefixState_succ hf hg]
    dsimp only [kepPoissonPrefixUpdate]
    rw [kepPoissonPrefixState_parentAnchor hf hn j i hm]
  calc
    _ = (expSeqMeasure.map (fun g => (kepPoissonPrefixState hf eps n x j i g,
        shiftBy (kepPoissonPivot hf eps n x j i) g))).map
          (kepPoissonPrefixUpdate hf eps n x j i) := by
      rw [Measure.map_congr hnext]
      exact (Measure.map_map (measurable_kepPoissonPrefixUpdate hf eps n x j i)
        ((measurable_kepPoissonPrefixState hf eps n x j i).prodMk
          (measurable_shiftBy (isStoppingRule_kepPoissonPivot hf eps n x j i)))).symm
    _ = _ := by
      rw [kepPoissonPrefixState_restart_joint hf eps n x j i (hfin i),
        ← kepPoissonPrefixKernel_comp]

theorem kepPoissonPrefixState_law {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) {eps n : ℝ} (hn : n ≠ 0) (j : ℕ)
    (hm : kepReferenceSpan eps j ≠ 0)
    (hfin : ∀ x : ℝ, ∀ᵐ g ∂expSeqMeasure, kepPoissonPivot hf eps n x j 1 g ≠ ⊤)
    (x : ℝ) (i : ℕ) :
    expSeqMeasure.map (kepPoissonPrefixState hf eps n x j i) =
      kernelIterateLaw (kepPoissonPrefixKernel hf eps n x j) (Measure.dirac (fun _ => 0)) i := by
  induction i with
  | zero =>
    have he : kepPoissonPrefixState hf eps n x j 0 = fun _ => (fun _ => (0 : ℝ)) := by
      funext g k
      simp only [kepPoissonPrefixState, Nat.not_lt_zero, if_false]
    rw [he, Measure.map_const, measure_univ, one_smul]
    rfl
  | succ i hi =>
    rw [kepPoissonPrefixState_succ_law hf hn j i hm
      (kepPoissonPivot_all_finite_of_leading hf eps n j hfin x), hi]
    rfl

end

end PGM
