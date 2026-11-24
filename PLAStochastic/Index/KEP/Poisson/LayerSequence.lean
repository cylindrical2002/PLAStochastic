import PLAStochastic.Index.KEP.Poisson.StoppedPrefixLaw
import PLAStochastic.Index.KEP.Poisson.PositiveMoments

/-!
# The original Poisson child gap sequence and parent output

Finite completed ranks identify the observed prefix with the original
physical hierarchy. Its greedy stopping rule is unchanged by normalization.
The parent output is exactly the stopped sum in the reference parent units.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory

def kepPoissonLayerSequence {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (j : ℕ) (g : ℕ → ℝ) : ℕ → ℝ :=
  fun k => (n * f x / kepReferenceSpan eps j) *
    (pairLayer eps j (kepPoissonPairs hf n x g) k).1

theorem measurable_kepPoissonLayerSequence {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n : ℝ) (j : ℕ) :
    Measurable (fun p : ℝ × (ℕ → ℝ) => kepPoissonLayerSequence hf eps n p.1 j p.2) := by
  have hl : Measurable (fun p : ℝ × (ℕ → ℝ) =>
      pairLayer eps j (kepPoissonPairs hf n p.1 p.2)) :=
    (measurable_pairLayer eps j).comp (measurable_kepPoissonPairs hf n)
  refine measurable_pi_lambda _ fun k => ?_
  exact ((measurable_const.mul (hf.continuous.measurable.comp measurable_fst)).div_const
    (kepReferenceSpan eps j)).mul
      (measurable_fst.comp ((measurable_pi_apply k).comp hl))

theorem measurable_kepPoissonLayerSequence_anchor {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (j : ℕ) :
    Measurable (kepPoissonLayerSequence hf eps n x j) :=
  (measurable_kepPoissonLayerSequence hf eps n j).comp
    (measurable_const.prodMk measurable_id)

theorem kepPoissonPrefixState_agree_layerSequence {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) {eps n x : ℝ} {j i : ℕ} {g : ℕ → ℝ}
    (hfin : kepPoissonPivot hf eps n x j i g ≠ ⊤) :
    ∀ k < i, kepPoissonPrefixState hf eps n x j i g k =
      kepPoissonLayerSequence hf eps n x j g k := by
  intro k hk
  have hfk : kepPoissonPivot hf eps n x j (k + 1) g ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (completedPivot_mono_key j (Nat.succ_le_of_lt hk))
  simp only [kepPoissonPrefixState, if_pos hk, kepPoissonLayerSequence]
  rw [kepPoissonPivotAnchor_difference hf hfk]

theorem kepPoissonStoppedPrefixState_eq_layerSequence {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) {eps n x : ℝ} {j i : ℕ} {g : ℕ → ℝ}
    (hfin : kepPoissonPivot hf eps n x j i g ≠ ⊤) :
    kepPoissonStoppedPrefixState hf eps n x j i g =
      kepStoppedPrefix eps i (kepPoissonLayerSequence hf eps n x j g) :=
  kepStoppedPrefix_causal eps i (kepPoissonPrefixState_agree_layerSequence hf hfin)

theorem kepPoissonLayerSequence_nonneg {f : ℝ → ℝ} {flo fhi L eps n : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hn : 0 < n) (x : ℝ) (j : ℕ)
    (hm : 0 ≤ kepReferenceSpan eps j) {g : ℕ → ℝ} (hg : ∀ k, 0 ≤ g k) (k : ℕ) :
    0 ≤ kepPoissonLayerSequence hf eps n x j g k :=
  mul_nonneg (div_nonneg (mul_nonneg hn.le (hf.f_pos x).le) hm)
    (pairLayer_fst_nonneg (kepPoissonPairs_fst_nonneg hf hn x hg) eps j k)

theorem kepPoissonLayerSequence_gapKeys {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (j : ℕ)
    (g : ℕ → ℝ) (i : ℕ) :
    gapKeys (kepPoissonLayerSequence hf eps n x j g) i =
      (n * f x / kepReferenceSpan eps j) *
        pairKeys (pairLayer eps j (kepPoissonPairs hf n x g)) i := by
  simp only [gapKeys, kepPoissonLayerSequence, pairKeys, Finset.mul_sum]

theorem kepPoissonLayerSequence_stop_eq {f : ℝ → ℝ} {flo fhi L eps n : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hn : 0 < n) (x : ℝ) (j : ℕ)
    (hm : 0 < kepReferenceSpan eps j) (g : ℕ → ℝ) :
    gapSegLen eps (kepPoissonLayerSequence hf eps n x j g) =
      pairSegLen eps (pairLayer eps j (kepPoissonPairs hf n x g)) := by
  have hc : n * f x / kepReferenceSpan eps j ≠ 0 :=
    (div_pos (mul_pos hn (hf.f_pos x)) hm).ne'
  have hkey : gapKeys (kepPoissonLayerSequence hf eps n x j g) =
      fun i => (n * f x / kepReferenceSpan eps j) *
        pairKeys (pairLayer eps j (kepPoissonPairs hf n x g)) i + 0 := by
    funext i
    rw [kepPoissonLayerSequence_gapKeys, add_zero]
  rw [gapSegLen, hkey, segLen_affine hc]
  rfl

theorem kepPoissonLayerGap_succ_stopSum {f : ℝ → ℝ} {flo fhi L eps n : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hn : 0 < n) (x : ℝ) (j : ℕ)
    (hm : 0 < kepReferenceSpan eps j) (g : ℕ → ℝ) :
    kepPoissonLayerGap hf eps n x (j + 1) g =
      (kepReferenceSpan eps j / kepReferenceSpan eps (j + 1)) *
        gapKeys (kepPoissonLayerSequence hf eps n x j g)
          (gapSegLen eps (kepPoissonLayerSequence hf eps n x j g)).toNat := by
  rw [kepPoissonLayerSequence_stop_eq hf hn x j hm, kepPoissonLayerSequence_gapKeys]
  unfold kepPoissonLayerGap
  rw [pairLayer, Function.iterate_succ_apply']
  simp only [layerMap, Function.iterate_zero_apply, firstBlock, Prod.fst_sum]
  change (n * f x / kepReferenceSpan eps (j + 1)) *
      pairKeys (pairLayer eps j (kepPoissonPairs hf n x g))
        (pairSegLen eps (pairLayer eps j (kepPoissonPairs hf n x g))).toNat = _
  field_simp [hm.ne']

end

end PGM
