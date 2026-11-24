import PLAStochastic.Index.KEP.IIDPrefixLaws

/-!
# The actual iid stopped prefix law as an absorbing kernel iteration

The greedy stopping decision is made from the observed prefix. The next iid
coordinate remains independent of that prefix, so the stopped path has the
same absorbing transition rule as the physical Poisson path.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

open Classical

theorem kepStoppedPrefix_gapPrefix (eps : ℝ) (i : ℕ) (g : ℕ → ℝ) :
    kepStoppedPrefix eps i (kepGapPrefix i g) = kepStoppedPrefix eps i g :=
  kepStoppedPrefix_causal eps i (fun _k hk => if_pos hk)

theorem iid_kepStoppedPrefix_next_independent (nu : ProbabilityMeasure ℝ)
    (eps : ℝ) (i : ℕ) :
    IndepFun (kepStoppedPrefix eps i) (fun g : ℕ → ℝ => g i) (iidLaw nu) := by
  have hi := (iid_kepGapPrefix_next_independent nu i).comp
    (measurable_kepStoppedPrefix eps i) measurable_id
  simpa only [Function.comp_def, kepStoppedPrefix_gapPrefix, id_eq] using hi

theorem iid_kepStoppedPrefix_next_joint (nu : ProbabilityMeasure ℝ) (eps : ℝ) (i : ℕ) :
    (iidLaw nu).map (fun g => (kepStoppedPrefix eps i g, g i)) =
      ((iidLaw nu).map (kepStoppedPrefix eps i)).prod (nu : Measure ℝ) := by
  have h := (iid_kepStoppedPrefix_next_independent nu eps i).map_prod_eq_prod_map_map
    (measurable_kepStoppedPrefix eps i).aemeasurable (measurable_pi_apply i).aemeasurable
  have hmap : (iidLaw nu).map (fun g : ℕ → ℝ => g i) = (nu : Measure ℝ) :=
    (measurePreserving_eval_infinitePi (fun _ : ℕ => (nu : Measure ℝ)) i).map_eq
  rw [hmap] at h
  exact h

def kepReferenceStoppedPrefixKernel (nu : ProbabilityMeasure ℝ) (eps : ℝ) (i : ℕ) :
    Kernel (ℕ → ℝ) (ℕ → ℝ) :=
  absorbingSequenceKernel {g | (i : ℕ∞) < gapSegLen eps g}
    ((isStoppingRule_gapSegLen eps).measurableSet_lt i)
    (Kernel.const (ℕ → ℝ) (nu : Measure ℝ)) i

instance isMarkovKernel_kepReferenceStoppedPrefixKernel
    (nu : ProbabilityMeasure ℝ) (eps : ℝ) (i : ℕ) :
    IsMarkovKernel (kepReferenceStoppedPrefixKernel nu eps i) :=
  inferInstanceAs (IsMarkovKernel
    (absorbingSequenceKernel {g | (i : ℕ∞) < gapSegLen eps g}
      ((isStoppingRule_gapSegLen eps).measurableSet_lt i)
      (Kernel.const (ℕ → ℝ) (nu : Measure ℝ)) i))

def kepReferenceStoppedPrefixUpdate (eps : ℝ) (i : ℕ)
    (p : (ℕ → ℝ) × ℝ) : ℕ → ℝ :=
  if (i : ℕ∞) < gapSegLen eps p.1 then Function.update p.1 i p.2 else p.1

theorem measurable_kepReferenceStoppedPrefixUpdate (eps : ℝ) (i : ℕ) :
    Measurable (kepReferenceStoppedPrefixUpdate eps i) :=
  Measurable.ite (measurable_fst ((isStoppingRule_gapSegLen eps).measurableSet_lt i))
    (measurable_sequenceUpdate i) measurable_fst

theorem kepReferenceStoppedPrefixKernel_apply (nu : ProbabilityMeasure ℝ)
    (eps : ℝ) (i : ℕ) (g : ℕ → ℝ) :
    kepReferenceStoppedPrefixKernel nu eps i g =
      (nu : Measure ℝ).map (fun z => kepReferenceStoppedPrefixUpdate eps i (g, z)) := by
  rw [kepReferenceStoppedPrefixKernel, absorbingSequenceKernel_apply]
  simp only [Set.mem_ofPred_eq, Kernel.const_apply]
  by_cases hi : (i : ℕ∞) < gapSegLen eps g
  · rw [if_pos hi]
    congr 1
    funext z
    simp only [kepReferenceStoppedPrefixUpdate, if_pos hi]
  · rw [if_neg hi]
    have he : (fun z => kepReferenceStoppedPrefixUpdate eps i (g, z)) = fun _ => g := by
      funext z
      simp only [kepReferenceStoppedPrefixUpdate, if_neg hi]
    rw [he, Measure.map_const, measure_univ, one_smul]

theorem kepReferenceStoppedPrefixKernel_comp (nu : ProbabilityMeasure ℝ)
    (eps : ℝ) (i : ℕ) (mu : Measure (ℕ → ℝ)) [IsProbabilityMeasure mu] :
    kepReferenceStoppedPrefixKernel nu eps i ∘ₘ mu =
      (mu.prod (nu : Measure ℝ)).map (kepReferenceStoppedPrefixUpdate eps i) := by
  have hk : kepReferenceStoppedPrefixKernel nu eps i =
      kernelFromNoise (nu : Measure ℝ) (kepReferenceStoppedPrefixUpdate eps i) := by
    ext g : 1
    rw [kepReferenceStoppedPrefixKernel_apply,
      kernelFromNoise_apply (nu : Measure ℝ) (measurable_kepReferenceStoppedPrefixUpdate eps i)]
  rw [hk, kernelFromNoise_comp (nu : Measure ℝ)
    (measurable_kepReferenceStoppedPrefixUpdate eps i)]

theorem iid_kepStoppedPrefix_law (nu : ProbabilityMeasure ℝ) (eps : ℝ) (i : ℕ) :
    (iidLaw nu).map (kepStoppedPrefix eps i) =
      kernelIterateLaw (kepReferenceStoppedPrefixKernel nu eps)
        (Measure.dirac (fun _ => 0)) i := by
  induction i with
  | zero =>
    have he : kepStoppedPrefix eps 0 = fun _ => (fun _ => (0 : ℝ)) := by
      funext g k
      simp only [kepStoppedPrefix, Nat.not_lt_zero, false_and, if_false]
    rw [he, Measure.map_const, measure_univ, one_smul]
    rfl
  | succ i hi =>
    let : IsProbabilityMeasure ((iidLaw nu).map (kepStoppedPrefix eps i)) :=
      Measure.isProbabilityMeasure_map (measurable_kepStoppedPrefix eps i).aemeasurable
    have he : kepStoppedPrefix eps (i + 1) =
        kepReferenceStoppedPrefixUpdate eps i ∘ (fun g => (kepStoppedPrefix eps i g, g i)) := by
      funext g
      dsimp only [Function.comp_def, kepReferenceStoppedPrefixUpdate]
      simpa only [kepStoppedPrefix_active] using kepStoppedPrefix_succ eps i g
    rw [he, ← Measure.map_map (measurable_kepReferenceStoppedPrefixUpdate eps i)
      ((measurable_kepStoppedPrefix eps i).prodMk (measurable_pi_apply i)),
      iid_kepStoppedPrefix_next_joint, ← kepReferenceStoppedPrefixKernel_comp, hi]
    rfl

end

end PGM
