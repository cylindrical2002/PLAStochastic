import PLAStochastic.Index.KEP.Poisson.PrefixState
import PLAStochastic.ForMathlib.Probability.Hellinger.SequenceKernel

/-!
# Pointwise physical transitions of the actual Poisson prefix state

Finite completed pivots identify each observed increment with the original
endpoint hierarchy. Its next increment is the fresh child output at the
actual physical anchor, dilated into the original parent units.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory

theorem kepPoissonPrefixState_parentAnchor {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) {eps n x : ℝ} (hn : n ≠ 0)
    (j i : ℕ) (hm : kepReferenceSpan eps j ≠ 0) (g : ℕ → ℝ) :
    kepPoissonParentAnchor hf eps n x j
      (gapKeys (kepPoissonPrefixState hf eps n x j i g) i) =
        kepPoissonPivotAnchor hf eps n x j i g := by
  rw [kepPoissonPrefixState_gapKeys]
  unfold kepPoissonParentAnchor
  field_simp [hn, hm, (hf.f_pos x).ne']
  ring

theorem kepPoissonPivotAnchor_difference {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) {eps n x : ℝ} {j i : ℕ} {g : ℕ → ℝ}
    (hfin : kepPoissonPivot hf eps n x j (i + 1) g ≠ ⊤) :
    kepPoissonPivotAnchor hf eps n x j (i + 1) g -
      kepPoissonPivotAnchor hf eps n x j i g =
        (pairLayer eps j (kepPoissonPairs hf n x g) i).1 := by
  have hfin0 : kepPoissonPivot hf eps n x j i g ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (completedPivot_mono_key j (Nat.le_succ i))
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hfin0
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hfin
  have hr' : kepPoissonPivot hf eps n x j i g = (r : ℕ∞) := hr.symm
  have hs' : kepPoissonPivot hf eps n x j (i + 1) g = (s : ℕ∞) := hs.symm
  have h0 := pairKeys_pairLayer (eps := eps) (z := kepPoissonPairs hf n x g)
    (fun _ => rfl) j i
  have h1 := pairKeys_pairLayer (eps := eps) (z := kepPoissonPairs hf n x g)
    (fun _ => rfl) j (i + 1)
  rw [pairKeys_kepPoissonPairs, kepPoissonPivot_eq_original_of_finite hf hr'] at h0
  rw [pairKeys_kepPoissonPairs, kepPoissonPivot_eq_original_of_finite hf hs'] at h1
  have hd : pairKeys (pairLayer eps j (kepPoissonPairs hf n x g)) (i + 1) -
      pairKeys (pairLayer eps j (kepPoissonPairs hf n x g)) i =
        (pairLayer eps j (kepPoissonPairs hf n x g) i).1 := by
    simp only [pairKeys, Finset.sum_range_succ, add_sub_cancel_left]
  rw [h0, h1] at hd
  simpa only [kepPoissonPivotAnchor, kepPoissonStoppedAnchor, hr', hs',
    ENat.toNat_natCast, sub_sub_sub_cancel_right] using hd

theorem kepPoissonPrefixState_succ {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) {eps n x : ℝ} {j i : ℕ} {g : ℕ → ℝ}
    (hfin : kepPoissonPivot hf eps n x j (i + 1) g ≠ ⊤) :
    kepPoissonPrefixState hf eps n x j (i + 1) g =
      Function.update (kepPoissonPrefixState hf eps n x j i g) i
        ((f x / f (kepPoissonPivotAnchor hf eps n x j i g)) *
          kepPoissonLayerGap hf eps n (kepPoissonPivotAnchor hf eps n x j i g) j
            (shiftBy (kepPoissonPivot hf eps n x j i) g)) := by
  classical
  have hfin0 : kepPoissonPivot hf eps n x j i g ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (completedPivot_mono_key j (Nat.le_succ i))
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hfin0
  have hr' : kepPoissonPivot hf eps n x j i g = (r : ℕ∞) := hr.symm
  have horig := kepPoissonPivot_eq_original_of_finite hf hr'
  have hshift : shiftBy (kepPoissonPivot hf eps n x j i) g = fun k => g (r + k) := by
    funext k
    change g ((kepPoissonPivot hf eps n x j i g).toNat + k) = g (r + k)
    rw [hr', ENat.toNat_natCast]
  have hgap := kepPoisson_layer_gap_restart hf eps n x g j i
  dsimp only at hgap
  rw [horig] at hgap
  have hgap' : (f x / f (kepPoissonPivotAnchor hf eps n x j i g)) *
      kepPoissonLayerGap hf eps n (kepPoissonPivotAnchor hf eps n x j i g) j
        (shiftBy (kepPoissonPivot hf eps n x j i) g) =
      (n * f x / kepReferenceSpan eps j) *
        (pairLayer eps j (kepPoissonPairs hf n x g) i).1 := by
    simpa only [kepPoissonPivotAnchor, kepPoissonStoppedAnchor, hshift, hr',
      ENat.toNat_natCast] using hgap
  funext k
  by_cases hki : k = i
  · subst k
    rw [Function.update_self, hgap']
    simp only [kepPoissonPrefixState, if_pos (Nat.lt_succ_self i)]
    rw [kepPoissonPivotAnchor_difference hf hfin]
  · rw [Function.update_of_ne hki]
    by_cases hk : k < i
    · simp only [kepPoissonPrefixState, if_pos hk, if_pos (hk.trans (Nat.lt_succ_self i))]
    · have hk' : ¬ k < i + 1 := by omega
      simp only [kepPoissonPrefixState, if_neg hk, if_neg hk']

def kepPoissonPrefixGapKernel {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (j i : ℕ) :
    Kernel (ℕ → ℝ) ℝ :=
  (kepPoissonParentStepKernel hf eps n x j).comap (fun g => gapKeys g i)
    ((measurable_pi_apply i).comp measurable_gapKeys)

instance isMarkovKernel_kepPoissonPrefixGapKernel {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (j i : ℕ) :
    IsMarkovKernel (kepPoissonPrefixGapKernel hf eps n x j i) := by
  unfold kepPoissonPrefixGapKernel
  infer_instance

def kepPoissonPrefixKernel {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (j i : ℕ) :
    Kernel (ℕ → ℝ) (ℕ → ℝ) :=
  sequenceUpdateKernel (kepPoissonPrefixGapKernel hf eps n x j i) i

instance isMarkovKernel_kepPoissonPrefixKernel {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (j i : ℕ) :
    IsMarkovKernel (kepPoissonPrefixKernel hf eps n x j i) :=
  inferInstanceAs (IsMarkovKernel
    (sequenceUpdateKernel (kepPoissonPrefixGapKernel hf eps n x j i) i))

end

end PGM
