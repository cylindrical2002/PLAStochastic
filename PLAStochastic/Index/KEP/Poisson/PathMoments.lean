import PLAStochastic.Index.KEP.Poisson.LayerSequence
import PLAStochastic.ForMathlib.Probability.Kernel.UniformIntegral

/-!
# Actual Poisson child path moments from conditional exponential budgets

Every increment has the original state-dependent gap kernel. A bound at all
physical anchors therefore bounds every actual increment marginal. Integer
power-sum estimates give cumulative moments without independence.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory

theorem kepPoissonPrefixKernel_map_coordinate {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (j i : ℕ) :
    (kepPoissonPrefixKernel hf eps n x j i).map (fun g => g i) =
      kepPoissonPrefixGapKernel hf eps n x j i := by
  ext g : 1
  have hU : Measurable (fun z : ℝ => Function.update g i z) :=
    (measurable_sequenceUpdate i).comp (measurable_const.prodMk measurable_id)
  rw [Kernel.map_apply _ (measurable_pi_apply i), kepPoissonPrefixKernel,
    sequenceUpdateKernel_apply, Measure.map_map (measurable_pi_apply i) hU]
  have he : (fun g : ℕ → ℝ => g i) ∘ (fun z => Function.update g i z) = id := by
    funext z
    exact Function.update_self i z g
  rw [he, Measure.map_id]

theorem kepPoissonLayerSequence_coordinate_law {f : ℝ → ℝ} {flo fhi L eps n : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hn : n ≠ 0) (x : ℝ) (j i : ℕ)
    (hm : kepReferenceSpan eps j ≠ 0)
    (hfin : ∀ y : ℝ, ∀ᵐ g ∂expSeqMeasure, kepPoissonPivot hf eps n y j 1 g ≠ ⊤) :
    expSeqMeasure.map (fun g => kepPoissonLayerSequence hf eps n x j g i) =
      kepPoissonPrefixGapKernel hf eps n x j i ∘ₘ
        expSeqMeasure.map (kepPoissonPrefixState hf eps n x j i) := by
  have hfall := kepPoissonPivot_all_finite_of_leading hf eps n j hfin x
  have he : (fun g => kepPoissonLayerSequence hf eps n x j g i) =ᵐ[expSeqMeasure]
      fun g => kepPoissonPrefixState hf eps n x j (i + 1) g i := by
    filter_upwards [hfall (i + 1)] with g hg
    exact (kepPoissonPrefixState_agree_layerSequence hf hg i (Nat.lt_succ_self i)).symm
  rw [Measure.map_congr he]
  calc
    _ = (expSeqMeasure.map (kepPoissonPrefixState hf eps n x j (i + 1))).map
        (fun g => g i) :=
      (Measure.map_map (measurable_pi_apply i)
        (measurable_kepPoissonPrefixState hf eps n x j (i + 1))).symm
    _ = _ := by
      rw [kepPoissonPrefixState_succ_law hf hn j i hm hfall,
        Measure.map_comp _ _ (measurable_pi_apply i), kepPoissonPrefixKernel_map_coordinate]

theorem kepPoissonLayerSequence_exp_moment {f : ℝ → ℝ} {flo fhi L eps n theta B : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hn : 0 < n) (htheta : 0 ≤ theta)
    (hB : 0 ≤ B) (x : ℝ) (j i : ℕ) (hm : 0 < kepReferenceSpan eps j)
    (hfin : ∀ y : ℝ, ∀ᵐ g ∂expSeqMeasure, kepPoissonPivot hf eps n y j 1 g ≠ ⊤)
    (hchild : ∀ y, Integrable (fun z => Real.exp (theta * z)) (kepPoissonLayerMeasure hf eps n y j) ∧
      ∫ z, Real.exp (theta * z) ∂kepPoissonLayerMeasure hf eps n y j ≤ B) :
    Integrable (fun g => Real.exp ((theta / (fhi / flo)) *
      kepPoissonLayerSequence hf eps n x j g i)) expSeqMeasure ∧
    ∫ g, Real.exp ((theta / (fhi / flo)) *
      kepPoissonLayerSequence hf eps n x j g i) ∂expSeqMeasure ≤ B := by
  let mu := expSeqMeasure.map (kepPoissonPrefixState hf eps n x j i)
  let : IsProbabilityMeasure mu :=
    Measure.isProbabilityMeasure_map (measurable_kepPoissonPrefixState hf eps n x j i).aemeasurable
  have hcond (g : ℕ → ℝ) :
      Integrable (fun z => Real.exp ((theta / (fhi / flo)) * z))
        (kepPoissonPrefixGapKernel hf eps n x j i g) ∧
      ∫ z, Real.exp ((theta / (fhi / flo)) * z)
        ∂kepPoissonPrefixGapKernel hf eps n x j i g ≤ B := by
    simpa only [kepPoissonPrefixGapKernel, Kernel.comap_apply, kepPoissonParentStepKernel_apply] using
      kepPoisson_fixed_scale_exp_moment hf hn htheta j hm.le hchild x
        (kepPoissonParentAnchor hf eps n x j (gapKeys g i))
  have hbudget := integrable_comp_of_uniform_nonnegative mu
    (kepPoissonPrefixGapKernel hf eps n x j i) (F := fun z => Real.exp ((theta / (fhi / flo)) * z))
    (by fun_prop) hB (fun _ => Filter.Eventually.of_forall fun z => (Real.exp_pos _).le)
    (fun g => (hcond g).1) (fun g => (hcond g).2)
  have hmap := kepPoissonLayerSequence_coordinate_law hf hn.ne' x j i hm.ne' hfin
  change _ = _ ∘ₘ mu at hmap
  rw [← hmap] at hbudget
  have hcoord : Measurable (fun g => kepPoissonLayerSequence hf eps n x j g i) :=
    (measurable_pi_apply i).comp (measurable_kepPoissonLayerSequence_anchor hf eps n x j)
  refine ⟨?_, ?_⟩
  · exact (integrable_map_measure (by fun_prop) hcoord.aemeasurable).mp hbudget.1
  · have hExp : Measurable (fun z : ℝ => Real.exp ((theta / (fhi / flo)) * z)) := by fun_prop
    rw [integral_map hcoord.aemeasurable hExp.aestronglyMeasurable] at hbudget
    exact hbudget.2

theorem kepPoissonLayerSequence_power_budget {f : ℝ → ℝ} {flo fhi L eps n theta B : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hn : 0 < n) (htheta : 0 < theta)
    (hB : 0 ≤ B) (x : ℝ) (j N k : ℕ) (hm : 0 < kepReferenceSpan eps j)
    (hfin : ∀ y : ℝ, ∀ᵐ g ∂expSeqMeasure, kepPoissonPivot hf eps n y j 1 g ≠ ⊤)
    (hchild : ∀ y, Integrable (fun z => Real.exp (theta * z)) (kepPoissonLayerMeasure hf eps n y j) ∧
      ∫ z, Real.exp (theta * z) ∂kepPoissonLayerMeasure hf eps n y j ≤ B) :
    Integrable (fun g => gapKeys (kepPoissonLayerSequence hf eps n x j g) N ^ (k + 1))
      expSeqMeasure ∧
    ∫ g, gapKeys (kepPoissonLayerSequence hf eps n x j g) N ^ (k + 1) ∂expSeqMeasure ≤
      (N : ℝ) ^ (k + 1) * ((k + 1).factorial / (theta / (fhi / flo)) ^ (k + 1) * B) := by
  have ht : 0 < theta / (fhi / flo) := div_pos htheta (div_pos hf.fhi_pos hf.pos)
  have hcoord (i : ℕ) : Measurable (fun g => kepPoissonLayerSequence hf eps n x j g i) :=
    (measurable_pi_apply i).comp (measurable_kepPoissonLayerSequence_anchor hf eps n x j)
  have hpos (i : ℕ) : ∀ᵐ g ∂expSeqMeasure, 0 ≤ kepPoissonLayerSequence hf eps n x j g i := by
    filter_upwards [ae_all_iff.mpr fun a =>
      iidSeq_expCoord.ae_pos_of_expMeasure_one (hasLaw_expCoord 0) a] with g hg
    exact kepPoissonLayerSequence_nonneg hf hn x j hm.le (fun a => (hg a).le) i
  have hmoment (i : ℕ) := polynomial_moment_of_exponential (hcoord i) ht (hpos i)
    (kepPoissonLayerSequence_exp_moment hf hn htheta.le hB x j i hm hfin hchild).1
    (kepPoissonLayerSequence_exp_moment hf hn htheta.le hB x j i hm hfin hchild).2 (k + 1)
  exact ⟨integrable_finite_sum_pow N k (fun i _ => hcoord i)
      (fun i _ => hpos i) (fun i _ => (hmoment i).1),
    integral_finite_sum_pow_le N k (fun i _ => hcoord i)
      (fun i _ => hpos i) (fun i _ => (hmoment i).1) (fun i _ => (hmoment i).2)⟩

end

end PGM
