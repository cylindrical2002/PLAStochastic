import PLAStochastic.Index.KEP.Poisson.RestartCoordinates
import PLAStochastic.ForMathlib.Probability.Process.IIDRegeneration
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Fresh exponential innovations at a natural Poisson stopping rank

The actual physical stopped position is a functional of the stopped prefix.
At every almost surely finite natural stopping rank, that position and the
fresh innovation sequence have their product law. Applying the actual layer
functional gives the original state-dependent Poisson kernel.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

def kepPoissonStoppedAnchor {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (n x : ℝ)
    (tau : (ℕ → ℝ) → ℕ∞) (g : ℕ → ℝ) : ℝ :=
  kepPoissonKeys hf n x g (tau g).toNat

theorem measurable_kepPoissonStoppedAnchor {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (n x : ℝ)
    {tau : (ℕ → ℝ) → ℕ∞} (htau : IsStoppingRule tau) :
    Measurable (kepPoissonStoppedAnchor hf n x tau) := by
  have hm : Measurable (fun p : (ℕ → ℝ) × ℕ => gapKeys p.1 p.2) :=
    measurable_from_prod_countable_left fun r =>
      (measurable_pi_apply r).comp measurable_gapKeys
  have hi : Measurable (fun g => (tau g).toNat) :=
    (Measurable.of_discrete (f := ENat.toNat)).comp htau.measurable
  have hs : Measurable (fun g => gapKeys g (tau g).toNat) :=
    hm.comp (measurable_id.prodMk hi)
  change Measurable (fun g => (kepIntensityOrderIso hf).symm
    (kepIntensityPrimitive f x + gapKeys g (tau g).toNat / n))
  exact (kepIntensityOrderIso hf).symm.continuous.measurable.comp
    (measurable_const.add (hs.div_const n))

theorem kepPoissonStoppedAnchor_prefix {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (n x : ℝ)
    {tau : (ℕ → ℝ) → ℕ∞} {g g' : ℕ → ℝ} (ht : tau g = tau g')
    (hp : ∀ i : ℕ, (i : ℕ∞) < tau g → g i = g' i) :
    kepPoissonStoppedAnchor hf n x tau g = kepPoissonStoppedAnchor hf n x tau g' := by
  by_cases htop : tau g = ⊤
  · simp only [kepPoissonStoppedAnchor, ← ht, htop, ENat.toNat_top,
      kepPoissonKeys, gapKeys, Finset.sum_range_zero, kepPoissonArrival_zero]
  · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp htop
    have hr' : tau g = (r : ℕ∞) := hr.symm
    simp only [kepPoissonStoppedAnchor, ← ht, hr', ENat.toNat_natCast, kepPoissonKeys]
    congr 1
    unfold gapKeys
    apply Finset.sum_congr rfl
    intro i hi
    apply hp
    rw [hr', ENat.natCast_lt_natCast]
    exact Finset.mem_range.mp hi

theorem kepPoisson_restart_innovations {tau : (ℕ → ℝ) → ℕ∞}
    (htau : IsStoppingRule tau) (hfin : ∀ᵐ g ∂expSeqMeasure, tau g ≠ ⊤) :
    IdentDistrib (shiftBy tau) id expSeqMeasure expSeqMeasure := by
  have hs : seq expCoord = id := rfl
  have he := identDistrib_shiftBy
    iidSeq_expCoord.measurable iidSeq_expCoord.indep iidSeq_expCoord.ident htau hfin
  simpa only [hs, id_eq] using he

theorem kepPoisson_restart_independent {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (n x : ℝ)
    {tau : (ℕ → ℝ) → ℕ∞} (htau : IsStoppingRule tau)
    (hfin : ∀ᵐ g ∂expSeqMeasure, tau g ≠ ⊤) :
    IndepFun (kepPoissonStoppedAnchor hf n x tau) (shiftBy tau) expSeqMeasure := by
  have hs : seq expCoord = id := rfl
  have he := indepFun_block_shiftBy
    iidSeq_expCoord.measurable iidSeq_expCoord.indep iidSeq_expCoord.ident htau hfin
    (measurable_kepPoissonStoppedAnchor hf n x htau)
    (fun g g' ht hp => kepPoissonStoppedAnchor_prefix hf n x ht hp)
  simpa only [hs, id_eq] using he

theorem kepPoisson_restart_joint {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (n x : ℝ)
    {tau : (ℕ → ℝ) → ℕ∞} (htau : IsStoppingRule tau)
    (hfin : ∀ᵐ g ∂expSeqMeasure, tau g ≠ ⊤) :
    expSeqMeasure.map (fun g => (kepPoissonStoppedAnchor hf n x tau g, shiftBy tau g)) =
      (expSeqMeasure.map (kepPoissonStoppedAnchor hf n x tau)).prod expSeqMeasure := by
  have he := (kepPoisson_restart_independent hf n x htau hfin).map_prod_eq_prod_map_map
    (measurable_kepPoissonStoppedAnchor hf n x htau).aemeasurable
    (measurable_shiftBy htau).aemeasurable
  rw [(kepPoisson_restart_innovations htau hfin).map_eq, Measure.map_id] at he
  exact he

theorem kepPoisson_layer_kernel_comp {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n : ℝ) (j : ℕ)
    (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    kepPoissonLayerKernel hf eps n j ∘ₘ mu =
      (mu.prod expSeqMeasure).map (fun p => kepPoissonLayerGap hf eps n p.1 j p.2) := by
  rw [kepPoissonLayerKernel, ← Measure.map_comp _ _ (measurable_kepPoissonLayerGap hf eps n j),
    ← Measure.compProd_eq_comp_prod, Measure.compProd_const]

theorem kepPoisson_restart_layer_law {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (j : ℕ)
    {tau : (ℕ → ℝ) → ℕ∞} (htau : IsStoppingRule tau)
    (hfin : ∀ᵐ g ∂expSeqMeasure, tau g ≠ ⊤) :
    expSeqMeasure.map (fun g =>
      kepPoissonLayerGap hf eps n (kepPoissonStoppedAnchor hf n x tau g) j (shiftBy tau g)) =
      kepPoissonLayerKernel hf eps n j ∘ₘ
        (expSeqMeasure.map (kepPoissonStoppedAnchor hf n x tau)) := by
  let : IsProbabilityMeasure (expSeqMeasure.map (kepPoissonStoppedAnchor hf n x tau)) :=
    Measure.isProbabilityMeasure_map (measurable_kepPoissonStoppedAnchor hf n x htau).aemeasurable
  rw [kepPoisson_layer_kernel_comp, ← kepPoisson_restart_joint hf n x htau hfin,
    Measure.map_map (measurable_kepPoissonLayerGap hf eps n j)
      ((measurable_kepPoissonStoppedAnchor hf n x htau).prodMk (measurable_shiftBy htau))]
  rfl

end

end PGM
