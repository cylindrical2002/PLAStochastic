import PLAStochastic.Index.GEP.LayerLaw.ActualLayers
import PLAStochastic.Index.KEP.StoppedPrefixes
import PLAStochastic.ForMathlib.Probability.Kernel.FromNoise

/-!
# The actual iid reference prefix law as a coordinate-kernel iteration

The canonical independent gap law is sampled one coordinate at a time.
The entire previously observed finite prefix is independent of its next gap.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

def kepGapPrefix (i : ℕ) (g : ℕ → ℝ) : ℕ → ℝ :=
  fun k => if k < i then g k else 0

theorem measurable_kepGapPrefix (i : ℕ) : Measurable (kepGapPrefix i) := by
  refine measurable_pi_lambda _ fun k => ?_
  by_cases hk : k < i
  · simp only [kepGapPrefix, if_pos hk]; exact measurable_pi_apply k
  · simp only [kepGapPrefix, if_neg hk]; exact measurable_const

theorem kepGapPrefix_succ (i : ℕ) (g : ℕ → ℝ) :
    kepGapPrefix (i + 1) g = Function.update (kepGapPrefix i g) i (g i) := by
  classical
  funext k
  by_cases hki : k = i
  · subst k
    simp only [kepGapPrefix, if_pos (Nat.lt_succ_self i), Function.update_self]
  · rw [Function.update_of_ne hki]
    have hk : k < i + 1 ↔ k < i := by omega
    simp only [kepGapPrefix, hk]

theorem iid_kepGapPrefix_next_independent (nu : ProbabilityMeasure ℝ) (i : ℕ) :
    IndepFun (kepGapPrefix i) (fun g : ℕ → ℝ => g i) (iidLaw nu) := by
  let tau : (ℕ → ℝ) → ℕ∞ := fun _ => i
  have htau : IsStoppingRule tau := by
    intro k
    by_cases hk : (k : ℕ∞) < (i : ℕ∞)
    · have he : {g : ℕ → ℝ | (k : ℕ∞) < tau g} = univ := by
        ext g; simp only [tau, mem_ofPred_eq, mem_univ, iff_true]; exact hk
      rw [he]
      exact @MeasurableSet.univ (ℕ → ℝ) (MeasurableSpace.comap (seqPrefix k) inferInstance)
    · have he : {g : ℕ → ℝ | (k : ℕ∞) < tau g} = ∅ := by
        ext g; simp only [tau, mem_ofPred_eq, mem_empty_iff_false, iff_false]; exact hk
      rw [he]; exact MeasurableSpace.measurableSet_empty _
  have hfin : ∀ᵐ g ∂iidLaw nu, tau g ≠ ⊤ :=
    Filter.Eventually.of_forall fun _ => ENat.natCast_ne_top i
  have hseq : seq gapCoord = id := rfl
  have hi := indepFun_block_shiftBy
    (iidSeq_gapCoord nu).measurable (iidSeq_gapCoord nu).indep (iidSeq_gapCoord nu).ident
    htau hfin (measurable_kepGapPrefix i) (fun g g' _ hp => by
      funext k
      by_cases hk : k < i
      · simp only [kepGapPrefix, if_pos hk]
        exact hp k (ENat.natCast_lt_natCast.mpr hk)
      · simp only [kepGapPrefix, if_neg hk])
  have hi' : IndepFun (kepGapPrefix i) (shiftBy tau) (iidLaw nu) := by
    simpa only [hseq, id_eq] using hi
  simpa only [Function.comp_def, id_eq, shiftBy, tau, ENat.toNat_natCast, Nat.add_zero] using
    hi'.comp measurable_id (measurable_pi_apply 0)

theorem iid_kepGapPrefix_next_joint (nu : ProbabilityMeasure ℝ) (i : ℕ) :
    (iidLaw nu).map (fun g => (kepGapPrefix i g, g i)) =
      ((iidLaw nu).map (kepGapPrefix i)).prod (nu : Measure ℝ) := by
  have h := (iid_kepGapPrefix_next_independent nu i).map_prod_eq_prod_map_map
    (measurable_kepGapPrefix i).aemeasurable (measurable_pi_apply i).aemeasurable
  have hmap : (iidLaw nu).map (fun g : ℕ → ℝ => g i) = (nu : Measure ℝ) :=
    (measurePreserving_eval_infinitePi (fun _ : ℕ => (nu : Measure ℝ)) i).map_eq
  rw [hmap] at h
  exact h

def kepReferencePrefixKernel (nu : ProbabilityMeasure ℝ) (i : ℕ) :
    Kernel (ℕ → ℝ) (ℕ → ℝ) :=
  sequenceUpdateKernel (Kernel.const (ℕ → ℝ) (nu : Measure ℝ)) i

instance isMarkovKernel_kepReferencePrefixKernel (nu : ProbabilityMeasure ℝ) (i : ℕ) :
    IsMarkovKernel (kepReferencePrefixKernel nu i) :=
  inferInstanceAs (IsMarkovKernel
    (sequenceUpdateKernel (Kernel.const (ℕ → ℝ) (nu : Measure ℝ)) i))

theorem kepReferencePrefixKernel_comp (nu : ProbabilityMeasure ℝ) (i : ℕ)
    (mu : Measure (ℕ → ℝ)) [IsProbabilityMeasure mu] :
    kepReferencePrefixKernel nu i ∘ₘ mu =
      (mu.prod (nu : Measure ℝ)).map (fun p => Function.update p.1 i p.2) := by
  unfold kepReferencePrefixKernel sequenceUpdateKernel
  exact kernelFromNoise_comp (nu : Measure ℝ) (measurable_sequenceUpdate i) mu

theorem iid_kepGapPrefix_law (nu : ProbabilityMeasure ℝ) (i : ℕ) :
    (iidLaw nu).map (kepGapPrefix i) =
      kernelIterateLaw (kepReferencePrefixKernel nu) (Measure.dirac (fun _ => 0)) i := by
  induction i with
  | zero =>
    have he : kepGapPrefix 0 = fun _ => (fun _ => (0 : ℝ)) := by
      funext g k
      simp only [kepGapPrefix, Nat.not_lt_zero, if_false]
    rw [he, Measure.map_const, measure_univ, one_smul]
    rfl
  | succ i hi =>
    let : IsProbabilityMeasure ((iidLaw nu).map (kepGapPrefix i)) :=
      Measure.isProbabilityMeasure_map (measurable_kepGapPrefix i).aemeasurable
    have he : kepGapPrefix (i + 1) =
        (fun p => Function.update p.1 i p.2) ∘ (fun g => (kepGapPrefix i g, g i)) :=
      funext fun g => kepGapPrefix_succ i g
    rw [he, ← Measure.map_map (measurable_sequenceUpdate i)
      ((measurable_kepGapPrefix i).prodMk (measurable_pi_apply i)),
      iid_kepGapPrefix_next_joint, ← kepReferencePrefixKernel_comp, hi]
    rfl

end

end PGM
