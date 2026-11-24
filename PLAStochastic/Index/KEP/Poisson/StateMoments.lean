import PLAStochastic.Index.KEP.Poisson.PathMoments

/-!
# Moment budgets for the actual observed Poisson state law

Finite completed pivots identify the cumulative state with the original
physical child gap sum. Its conditional exponential budget therefore pays
the integer moments used by the Hellinger kernel chain.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory

theorem kepPoisson_prefix_state_power_budget {f : ℝ → ℝ}
    {flo fhi L eps n theta B : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hn : 0 < n) (htheta : 0 < theta)
    (hB : 0 ≤ B) (x : ℝ) (j N k : ℕ) (hm : 0 < kepReferenceSpan eps j)
    (hfin : ∀ y : ℝ, ∀ᵐ g ∂expSeqMeasure, kepPoissonPivot hf eps n y j 1 g ≠ ⊤)
    (hchild : ∀ y, Integrable (fun z => Real.exp (theta * z)) (kepPoissonLayerMeasure hf eps n y j) ∧
      ∫ z, Real.exp (theta * z) ∂kepPoissonLayerMeasure hf eps n y j ≤ B) :
    Integrable (fun g => gapKeys g N ^ (k + 1))
      (kernelIterateLaw (kepPoissonPrefixKernel hf eps n x j)
        (Measure.dirac (fun _ => 0)) N) ∧
      ∫ g, gapKeys g N ^ (k + 1)
        ∂kernelIterateLaw (kepPoissonPrefixKernel hf eps n x j)
          (Measure.dirac (fun _ => 0)) N ≤
        (N : ℝ) ^ (k + 1) * ((k + 1).factorial / (theta / (fhi / flo)) ^ (k + 1) * B) := by
  have h := kepPoissonLayerSequence_power_budget hf hn htheta hB x j N k hm hfin hchild
  have he : (fun g => gapKeys (kepPoissonPrefixState hf eps n x j N g) N ^ (k + 1)) =ᵐ[expSeqMeasure]
      fun g => gapKeys (kepPoissonLayerSequence hf eps n x j g) N ^ (k + 1) := by
    filter_upwards [kepPoissonPivot_all_finite_of_leading hf eps n j hfin x N] with g hg
    rw [gapKeys_congr (kepPoissonPrefixState_agree_layerSequence hf hg) N le_rfl]
  rw [← kepPoissonPrefixState_law hf hn.ne' j hm.ne' hfin x N]
  have hF : Measurable (fun g : ℕ → ℝ => gapKeys g N ^ (k + 1)) :=
    ((measurable_pi_apply N).comp measurable_gapKeys).pow_const _
  refine ⟨?_, ?_⟩
  · apply (integrable_map_measure hF.aestronglyMeasurable
      (measurable_kepPoissonPrefixState hf eps n x j N).aemeasurable).mpr
    exact h.1.congr he.symm
  · rw [integral_map (measurable_kepPoissonPrefixState hf eps n x j N).aemeasurable
      hF.aestronglyMeasurable, integral_congr_ae he]
    exact h.2

end

end PGM
