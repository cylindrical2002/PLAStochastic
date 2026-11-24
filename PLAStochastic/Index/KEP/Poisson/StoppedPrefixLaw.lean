import PLAStochastic.Index.KEP.Poisson.PrefixLaw
import PLAStochastic.Index.KEP.StoppedPrefixes

/-!
# The actual stopped Poisson prefix law as an absorbing kernel iteration

The common greedy decision is made on the observed state. Fresh innovations
are charged only while active; after stopping the state is absorbed. The law
is identified with the original physical prefix stopped by that decision.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

def kepPoissonStoppedPrefixKernel {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (j i : ℕ) :
    Kernel (ℕ → ℝ) (ℕ → ℝ) :=
  absorbingSequenceKernel {g | (i : ℕ∞) < gapSegLen eps g}
    ((isStoppingRule_gapSegLen eps).measurableSet_lt i)
    (kepPoissonPrefixGapKernel hf eps n x j i) i

instance isMarkovKernel_kepPoissonStoppedPrefixKernel {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (j i : ℕ) :
    IsMarkovKernel (kepPoissonStoppedPrefixKernel hf eps n x j i) :=
  inferInstanceAs (IsMarkovKernel
    (absorbingSequenceKernel {g | (i : ℕ∞) < gapSegLen eps g}
      ((isStoppingRule_gapSegLen eps).measurableSet_lt i)
      (kepPoissonPrefixGapKernel hf eps n x j i) i))

def kepPoissonStoppedPrefixUpdate {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (j i : ℕ)
    (p : (ℕ → ℝ) × (ℕ → ℝ)) : ℕ → ℝ :=
  if (i : ℕ∞) < gapSegLen eps p.1 then kepPoissonPrefixUpdate hf eps n x j i p else p.1

theorem measurable_kepPoissonStoppedPrefixUpdate {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (j i : ℕ) :
    Measurable (kepPoissonStoppedPrefixUpdate hf eps n x j i) :=
  Measurable.ite (measurable_fst ((isStoppingRule_gapSegLen eps).measurableSet_lt i))
    (measurable_kepPoissonPrefixUpdate hf eps n x j i) measurable_fst

theorem kepPoissonStoppedPrefixKernel_apply {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (j i : ℕ) (g : ℕ → ℝ) :
    kepPoissonStoppedPrefixKernel hf eps n x j i g =
      expSeqMeasure.map (fun z => kepPoissonStoppedPrefixUpdate hf eps n x j i (g, z)) := by
  rw [kepPoissonStoppedPrefixKernel, absorbingSequenceKernel_apply]
  simp only [Set.mem_ofPred_eq]
  by_cases hi : (i : ℕ∞) < gapSegLen eps g
  · rw [if_pos hi]
    have hfull := kepPoissonPrefixKernel_apply hf eps n x j i g
    rw [kepPoissonPrefixKernel, sequenceUpdateKernel_apply] at hfull
    rw [hfull]
    congr 1
    funext z
    simp only [kepPoissonStoppedPrefixUpdate, if_pos hi]
  · rw [if_neg hi]
    have he : (fun z => kepPoissonStoppedPrefixUpdate hf eps n x j i (g, z)) =
        fun _ => g := by funext z; simp only [kepPoissonStoppedPrefixUpdate, if_neg hi]
    rw [he, Measure.map_const, measure_univ, one_smul]

theorem kepPoissonStoppedPrefixKernel_comp {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (j i : ℕ)
    (mu : Measure (ℕ → ℝ)) [IsProbabilityMeasure mu] :
    kepPoissonStoppedPrefixKernel hf eps n x j i ∘ₘ mu =
      (mu.prod expSeqMeasure).map (kepPoissonStoppedPrefixUpdate hf eps n x j i) := by
  have hk : kepPoissonStoppedPrefixKernel hf eps n x j i =
      kernelFromNoise expSeqMeasure (kepPoissonStoppedPrefixUpdate hf eps n x j i) := by
    ext g : 1
    rw [kepPoissonStoppedPrefixKernel_apply,
      kernelFromNoise_apply expSeqMeasure (measurable_kepPoissonStoppedPrefixUpdate hf eps n x j i)]
  rw [hk, kernelFromNoise_comp expSeqMeasure (measurable_kepPoissonStoppedPrefixUpdate hf eps n x j i)]

theorem kepPoissonStoppedPrefixUpdate_congr {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (j i : ℕ)
    (g z : ℕ → ℝ) :
    kepStoppedPrefix eps (i + 1) (kepPoissonPrefixUpdate hf eps n x j i (g, z)) =
      kepPoissonStoppedPrefixUpdate hf eps n x j i (kepStoppedPrefix eps i g, z) := by
  dsimp only [kepPoissonPrefixUpdate]
  rw [kepStoppedPrefix_succ_update]
  unfold kepPoissonStoppedPrefixUpdate
  by_cases hi : (i : ℕ∞) < gapSegLen eps g
  · rw [if_pos hi, if_pos ((kepStoppedPrefix_active eps i g).mpr hi)]
    dsimp only [kepPoissonPrefixUpdate]
    rw [kepStoppedPrefix_gapKeys_of_active hi]
  · rw [if_neg hi, if_neg (fun h => hi ((kepStoppedPrefix_active eps i g).mp h))]

def kepPoissonStoppedPrefixState {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (j i : ℕ) (g : ℕ → ℝ) : ℕ → ℝ :=
  kepStoppedPrefix eps i (kepPoissonPrefixState hf eps n x j i g)

theorem measurable_kepPoissonStoppedPrefixState {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (j i : ℕ) :
    Measurable (kepPoissonStoppedPrefixState hf eps n x j i) :=
  (measurable_kepStoppedPrefix eps i).comp (measurable_kepPoissonPrefixState hf eps n x j i)

theorem kepPoissonStoppedPrefixState_succ_law {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) {eps n x : ℝ} (hn : n ≠ 0) (j i : ℕ)
    (hm : kepReferenceSpan eps j ≠ 0)
    (hfin : ∀ a : ℕ, ∀ᵐ g ∂expSeqMeasure, kepPoissonPivot hf eps n x j a g ≠ ⊤) :
    expSeqMeasure.map (kepPoissonStoppedPrefixState hf eps n x j (i + 1)) =
      kepPoissonStoppedPrefixKernel hf eps n x j i ∘ₘ
        (expSeqMeasure.map (kepPoissonStoppedPrefixState hf eps n x j i)) := by
  let : IsProbabilityMeasure (expSeqMeasure.map (kepPoissonStoppedPrefixState hf eps n x j i)) :=
    Measure.isProbabilityMeasure_map (measurable_kepPoissonStoppedPrefixState hf eps n x j i).aemeasurable
  have hnext : kepPoissonStoppedPrefixState hf eps n x j (i + 1) =ᵐ[expSeqMeasure]
      fun g => kepPoissonStoppedPrefixUpdate hf eps n x j i
        (kepPoissonStoppedPrefixState hf eps n x j i g,
          shiftBy (kepPoissonPivot hf eps n x j i) g) := by
    filter_upwards [hfin (i + 1)] with g hg
    unfold kepPoissonStoppedPrefixState
    rw [kepPoissonPrefixState_succ hf hg]
    have he := kepPoissonPrefixState_parentAnchor hf (x := x) hn j i hm g
    have hfull : kepPoissonPrefixUpdate hf eps n x j i
        (kepPoissonPrefixState hf eps n x j i g, shiftBy (kepPoissonPivot hf eps n x j i) g) =
      Function.update (kepPoissonPrefixState hf eps n x j i g) i
        ((f x / f (kepPoissonPivotAnchor hf eps n x j i g)) *
          kepPoissonLayerGap hf eps n (kepPoissonPivotAnchor hf eps n x j i g) j
            (shiftBy (kepPoissonPivot hf eps n x j i) g)) := by
      dsimp only [kepPoissonPrefixUpdate]
      rw [he]
    rw [← hfull, kepPoissonStoppedPrefixUpdate_congr]
  have hi := (kepPoissonPrefixState_restart_independent hf eps n x j i (hfin i)).comp
    (measurable_kepStoppedPrefix eps i) measurable_id
  have hjoint := hi.map_prod_eq_prod_map_map
    (measurable_kepPoissonStoppedPrefixState hf eps n x j i).aemeasurable
    (measurable_shiftBy (isStoppingRule_kepPoissonPivot hf eps n x j i)).aemeasurable
  rw [(kepPoisson_restart_innovations
    (isStoppingRule_kepPoissonPivot hf eps n x j i) (hfin i)).map_eq, Measure.map_id] at hjoint
  calc
    _ = (expSeqMeasure.map (fun g => (kepPoissonStoppedPrefixState hf eps n x j i g,
        shiftBy (kepPoissonPivot hf eps n x j i) g))).map
          (kepPoissonStoppedPrefixUpdate hf eps n x j i) := by
      rw [Measure.map_congr hnext]
      exact (Measure.map_map (measurable_kepPoissonStoppedPrefixUpdate hf eps n x j i)
        ((measurable_kepPoissonStoppedPrefixState hf eps n x j i).prodMk
          (measurable_shiftBy (isStoppingRule_kepPoissonPivot hf eps n x j i)))).symm
    _ = _ := by rw [hjoint, ← kepPoissonStoppedPrefixKernel_comp]

theorem kepPoissonStoppedPrefixState_law {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) {eps n : ℝ} (hn : n ≠ 0) (j : ℕ)
    (hm : kepReferenceSpan eps j ≠ 0)
    (hfin : ∀ x : ℝ, ∀ᵐ g ∂expSeqMeasure, kepPoissonPivot hf eps n x j 1 g ≠ ⊤)
    (x : ℝ) (i : ℕ) :
    expSeqMeasure.map (kepPoissonStoppedPrefixState hf eps n x j i) =
      kernelIterateLaw (kepPoissonStoppedPrefixKernel hf eps n x j)
        (Measure.dirac (fun _ => 0)) i := by
  induction i with
  | zero =>
    have he : kepPoissonStoppedPrefixState hf eps n x j 0 = fun _ => (fun _ => (0 : ℝ)) := by
      funext g k
      simp only [kepPoissonStoppedPrefixState, kepStoppedPrefix, Nat.not_lt_zero, false_and, if_false]
    rw [he, Measure.map_const, measure_univ, one_smul]
    rfl
  | succ i hi =>
    rw [kepPoissonStoppedPrefixState_succ_law hf hn j i hm
      (kepPoissonPivot_all_finite_of_leading hf eps n j hfin x), hi]
    rfl

end

end PGM
