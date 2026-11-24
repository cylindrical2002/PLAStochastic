import PLAStochastic.Index.KEP.Poisson.SuccessiveRestarts
import PLAStochastic.Index.KEP.Poisson.ParentState

/-!
# Actual observed Poisson layer prefixes at natural completed ranks

The state consists of the observed physical child gaps in fixed parent units.
It reads only the exponential innovations before the current completed pivot.
At every almost surely finite pivot, this entire state is independent of the
fresh exponential sequence. Completed ranks retain their infinite value.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

def kepPoissonPivotAnchor {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (j i : ℕ) (g : ℕ → ℝ) : ℝ :=
  kepPoissonStoppedAnchor hf n x (kepPoissonPivot hf eps n x j i) g

theorem measurable_kepPoissonPivotAnchor {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (j i : ℕ) :
    Measurable (kepPoissonPivotAnchor hf eps n x j i) :=
  measurable_kepPoissonStoppedAnchor hf n x (isStoppingRule_kepPoissonPivot hf eps n x j i)

theorem kepPoissonPivotAnchor_zero {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (j : ℕ) (g : ℕ → ℝ) :
    kepPoissonPivotAnchor hf eps n x j 0 g = x := by
  simp only [kepPoissonPivotAnchor, kepPoissonStoppedAnchor, kepPoissonPivot,
    completedPivot_zero, ENat.toNat_zero, kepPoissonKeys, gapKeys,
    Finset.sum_range_zero, kepPoissonArrival_zero]

theorem kepPoissonPivotAnchor_prefix {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) {eps n x : ℝ} {j i k r : ℕ}
    {g g' : ℕ → ℝ} (hk : k ≤ i) (hr : kepPoissonPivot hf eps n x j i g = r)
    (hp : ∀ a < r, g a = g' a) :
    kepPoissonPivotAnchor hf eps n x j k g = kepPoissonPivotAnchor hf eps n x j k g' := by
  have hle : kepPoissonPivot hf eps n x j k g ≤ r :=
    (completedPivot_mono_key j hk).trans hr.le
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp
    (ne_top_of_le_ne_top (ENat.natCast_ne_top r) hle)
  have hs' : kepPoissonPivot hf eps n x j k g = (s : ℕ∞) := hs.symm
  have hsr : s ≤ r := by rw [hs'] at hle; exact ENat.natCast_le_natCast.mp hle
  have ht : kepPoissonPivot hf eps n x j k g' = (s : ℕ∞) :=
    completedPivot_eq_of_prefix
      (kepPoissonPairs_prefix hf n x (fun a ha => hp a (ha.trans_le hsr))) hs'
  simp only [kepPoissonPivotAnchor, kepPoissonStoppedAnchor, hs', ht, ENat.toNat_natCast]
  exact kepPoissonKeys_prefix hf n x hsr hp

def kepPoissonPrefixState {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (j i : ℕ) (g : ℕ → ℝ) : ℕ → ℝ :=
  fun k => if k < i then (n * f x / kepReferenceSpan eps j) *
    (kepPoissonPivotAnchor hf eps n x j (k + 1) g -
      kepPoissonPivotAnchor hf eps n x j k g) else 0

theorem measurable_kepPoissonPrefixState {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (j i : ℕ) :
    Measurable (kepPoissonPrefixState hf eps n x j i) := by
  refine measurable_pi_lambda _ fun k => ?_
  by_cases hk : k < i
  · simp only [kepPoissonPrefixState, if_pos hk]
    exact measurable_const.mul
      ((measurable_kepPoissonPivotAnchor hf eps n x j (k + 1)).sub
        (measurable_kepPoissonPivotAnchor hf eps n x j k))
  · simp only [kepPoissonPrefixState, if_neg hk]
    exact measurable_const

theorem kepPoissonPrefixState_stopped {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (j i : ℕ)
    (g g' : ℕ → ℝ)
    (_ht : kepPoissonPivot hf eps n x j i g = kepPoissonPivot hf eps n x j i g')
    (hp : ∀ a : ℕ, (a : ℕ∞) < kepPoissonPivot hf eps n x j i g → g a = g' a) :
    kepPoissonPrefixState hf eps n x j i g = kepPoissonPrefixState hf eps n x j i g' := by
  by_cases htop : kepPoissonPivot hf eps n x j i g = ⊤
  · have he : g = g' := funext fun a => hp a (htop ▸ ENat.natCast_lt_top a)
    rw [he]
  · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp htop
    have hr' : kepPoissonPivot hf eps n x j i g = (r : ℕ∞) := hr.symm
    have hprefix : ∀ a < r, g a = g' a := fun a ha =>
      hp a (hr' ▸ ENat.natCast_lt_natCast.mpr ha)
    funext k
    by_cases hk : k < i
    · simp only [kepPoissonPrefixState, if_pos hk]
      rw [kepPoissonPivotAnchor_prefix hf (Nat.succ_le_of_lt hk) hr' hprefix,
        kepPoissonPivotAnchor_prefix hf hk.le hr' hprefix]
    · simp only [kepPoissonPrefixState, if_neg hk]

theorem kepPoissonPrefixState_gapKeys {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (j i : ℕ) (g : ℕ → ℝ) :
    gapKeys (kepPoissonPrefixState hf eps n x j i g) i =
      (n * f x / kepReferenceSpan eps j) *
        (kepPoissonPivotAnchor hf eps n x j i g - x) := by
  have htel (k : ℕ) : (∑ a ∈ Finset.range k,
      (kepPoissonPivotAnchor hf eps n x j (a + 1) g -
        kepPoissonPivotAnchor hf eps n x j a g)) =
      kepPoissonPivotAnchor hf eps n x j k g - x := by
    induction k with
    | zero => simp [kepPoissonPivotAnchor_zero]
    | succ k ih => rw [Finset.sum_range_succ, ih]; ring
  unfold gapKeys
  simp only [kepPoissonPrefixState]
  calc
    _ = (n * f x / kepReferenceSpan eps j) *
        (∑ a ∈ Finset.range i, (kepPoissonPivotAnchor hf eps n x j (a + 1) g -
          kepPoissonPivotAnchor hf eps n x j a g)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a ha => if_pos (Finset.mem_range.mp ha)
    _ = _ := by rw [htel]

theorem kepPoissonPrefixState_restart_joint {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (j i : ℕ)
    (hfin : ∀ᵐ g ∂expSeqMeasure, kepPoissonPivot hf eps n x j i g ≠ ⊤) :
    expSeqMeasure.map (fun g => (kepPoissonPrefixState hf eps n x j i g,
      shiftBy (kepPoissonPivot hf eps n x j i) g)) =
      (expSeqMeasure.map (kepPoissonPrefixState hf eps n x j i)).prod expSeqMeasure := by
  have hs : seq expCoord = id := rfl
  have hi := indepFun_block_shiftBy
    iidSeq_expCoord.measurable iidSeq_expCoord.indep iidSeq_expCoord.ident
    (isStoppingRule_kepPoissonPivot hf eps n x j i) hfin
    (measurable_kepPoissonPrefixState hf eps n x j i)
    (kepPoissonPrefixState_stopped hf eps n x j i)
  have hi' : IndepFun (kepPoissonPrefixState hf eps n x j i)
      (shiftBy (kepPoissonPivot hf eps n x j i)) expSeqMeasure := by
    simpa only [hs, id_eq] using hi
  have he := hi'.map_prod_eq_prod_map_map
    (measurable_kepPoissonPrefixState hf eps n x j i).aemeasurable
    (measurable_shiftBy (isStoppingRule_kepPoissonPivot hf eps n x j i)).aemeasurable
  rw [(kepPoisson_restart_innovations
    (isStoppingRule_kepPoissonPivot hf eps n x j i) hfin).map_eq, Measure.map_id] at he
  exact he

theorem kepPoissonPrefixState_restart_independent {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (j i : ℕ)
    (hfin : ∀ᵐ g ∂expSeqMeasure, kepPoissonPivot hf eps n x j i g ≠ ⊤) :
    IndepFun (kepPoissonPrefixState hf eps n x j i)
      (shiftBy (kepPoissonPivot hf eps n x j i)) expSeqMeasure := by
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (measurable_kepPoissonPrefixState hf eps n x j i).aemeasurable
    (measurable_shiftBy (isStoppingRule_kepPoissonPivot hf eps n x j i)).aemeasurable).mpr
  rw [(kepPoisson_restart_innovations
    (isStoppingRule_kepPoissonPivot hf eps n x j i) hfin).map_eq, Measure.map_id]
  exact kepPoissonPrefixState_restart_joint hf eps n x j i hfin

end

end PGM
