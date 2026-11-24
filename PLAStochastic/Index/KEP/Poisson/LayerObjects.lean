import PLAStochastic.Index.KEP.Poisson.BaseHellinger
import PLAStochastic.Index.KEP.ReferenceScale.MeanSpan
import PLAStochastic.Index.KEP.PrefixStability
import Mathlib.Probability.Kernel.Composition.Prod

/-!
# Actual nonhomogeneous Poisson layer laws and measurable state kernels

Every layer is the original endpoint hierarchy applied to the physical arrival
sequence. Its state kernel samples the same fresh exponential innovation law.
The base layer agrees with the proved Poisson base gap, and the physical output
is exactly the key at the original layer pivot.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

def kepPoissonLayerGap {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (j : ℕ) (g : ℕ → ℝ) : ℝ :=
  (n * f x / kepReferenceSpan eps j) * (pairLayer eps j (kepPoissonPairs hf n x g) 0).1

theorem measurable_kepPoissonLayerGap {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n : ℝ) (j : ℕ) :
    Measurable (fun p : ℝ × (ℕ → ℝ) => kepPoissonLayerGap hf eps n p.1 j p.2) := by
  have hl : Measurable (fun p : ℝ × (ℕ → ℝ) => pairLayer eps j (kepPoissonPairs hf n p.1 p.2)) :=
    (measurable_pairLayer eps j).comp (measurable_kepPoissonPairs hf n)
  have hfirst : Measurable (fun p : ℝ × (ℕ → ℝ) =>
      (pairLayer eps j (kepPoissonPairs hf n p.1 p.2) 0).1) :=
    measurable_fst.comp ((measurable_pi_apply 0).comp hl)
  exact ((measurable_const.mul (hf.continuous.measurable.comp measurable_fst)).div_const
    (kepReferenceSpan eps j)).mul hfirst

theorem measurable_kepPoissonLayerGap_anchor {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (j : ℕ) :
    Measurable (kepPoissonLayerGap hf eps n x j) :=
  (measurable_kepPoissonLayerGap hf eps n j).comp (measurable_const.prodMk measurable_id)

def kepPoissonLayerMeasure {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (j : ℕ) : Measure ℝ :=
  expSeqMeasure.map (kepPoissonLayerGap hf eps n x j)

instance isProbabilityMeasure_kepPoissonLayerMeasure {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (j : ℕ) :
    IsProbabilityMeasure (kepPoissonLayerMeasure hf eps n x j) :=
  Measure.isProbabilityMeasure_map (measurable_kepPoissonLayerGap_anchor hf eps n x j).aemeasurable

def kepPoissonLayerKernel {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n : ℝ) (j : ℕ) : Kernel ℝ ℝ :=
  ((Kernel.id : Kernel ℝ ℝ) ×ₖ Kernel.const ℝ expSeqMeasure).map
    (fun p : ℝ × (ℕ → ℝ) => kepPoissonLayerGap hf eps n p.1 j p.2)

instance isMarkovKernel_kepPoissonLayerKernel {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n : ℝ) (j : ℕ) :
    IsMarkovKernel (kepPoissonLayerKernel hf eps n j) :=
  Kernel.IsMarkovKernel.map _ (measurable_kepPoissonLayerGap hf eps n j)

theorem kepPoissonLayerKernel_apply {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (j : ℕ) :
    kepPoissonLayerKernel hf eps n j x = kepPoissonLayerMeasure hf eps n x j := by
  ext s hs
  rw [kepPoissonLayerKernel, Kernel.map_apply' _ (measurable_kepPoissonLayerGap hf eps n j) x hs,
    Kernel.id_prod_apply' _ x ((measurable_kepPoissonLayerGap hf eps n j) hs),
    Kernel.const_apply, kepPoissonLayerMeasure,
    Measure.map_apply (measurable_kepPoissonLayerGap_anchor hf eps n x j) hs]
  rfl

theorem kepPoissonLayerGap_zero {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (g : ℕ → ℝ) :
    kepPoissonLayerGap hf eps n x 0 g = kepPoissonNormalizedGap hf n x (g 0) := by
  unfold kepPoissonLayerGap kepReferenceSpan
  rw [meanSpan_zero]
  simp only [pairLayer, Function.iterate_zero_apply, div_one]
  change n * f x * (kepPoissonKeys hf n x g 1 - kepPoissonKeys hf n x g 0) = _
  simp only [kepPoissonKeys, gapKeys, Finset.sum_range_one, Finset.sum_range_zero,
    kepPoissonArrival_zero, kepPoissonNormalizedGap]

theorem kepPoissonLayerMeasure_zero {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) :
    kepPoissonLayerMeasure hf eps n x 0 = kepPoissonBaseMeasure hf n x := by
  have he : kepPoissonLayerGap hf eps n x 0 = kepPoissonNormalizedGap hf n x ∘ expCoord 0 :=
    funext (kepPoissonLayerGap_zero hf eps n x)
  rw [kepPoissonLayerMeasure, he,
    ← Measure.map_map (measurable_kepPoissonNormalizedGap hf n x) (measurable_expCoord 0),
    (hasLaw_expCoord 0).map_eq]
  rfl

theorem kepPoissonLayerGap_eq_pivot {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (j : ℕ) (g : ℕ → ℝ) :
    kepPoissonLayerGap hf eps n x j g =
      (n * f x / kepReferenceSpan eps j) *
        (kepPoissonKeys hf n x g (layerPivot eps (kepPoissonPairs hf n x g) j 1) - x) := by
  have h := pairKeys_pairLayer (eps := eps) (z := kepPoissonPairs hf n x g) (fun _ => rfl) j 1
  rw [pairKeys_kepPoissonPairs] at h
  have hone : pairKeys (pairLayer eps j (kepPoissonPairs hf n x g)) 1 =
      (pairLayer eps j (kepPoissonPairs hf n x g) 0).1 := by
    simp only [pairKeys, Finset.sum_range_one]
  rw [hone] at h
  unfold kepPoissonLayerGap
  rw [h]

end

end PGM
