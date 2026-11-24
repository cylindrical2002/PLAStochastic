import PLAStochastic.Index.KEP.CompletedPivotStopping
import PLAStochastic.Index.KEP.Poisson.NaturalRestart

/-!
# Actual nonhomogeneous Poisson pivots as extended natural stopping ranks

The physical arrival transform reads exactly its exponential prefix. The
completed endpoint rank therefore is a natural stopping rule, jointly
measurable in the physical anchor. Finite ranks coincide with the original
hierarchy and admit the proved fresh-innovation restart law.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem kepPoissonKeys_prefix {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (n x : ℝ)
    {g g' : ℕ → ℝ} {r k : ℕ} (hk : k ≤ r) (hp : ∀ i < r, g i = g' i) :
    kepPoissonKeys hf n x g k = kepPoissonKeys hf n x g' k := by
  unfold kepPoissonKeys
  congr 1
  unfold gapKeys
  exact Finset.sum_congr rfl fun i hi => hp i ((Finset.mem_range.mp hi).trans_le hk)

theorem kepPoissonPairs_prefix {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (n x : ℝ)
    {g g' : ℕ → ℝ} {r : ℕ} (hp : ∀ i < r, g i = g' i) :
    ∀ i < r, (kepPoissonPairs hf n x g i).1 = (kepPoissonPairs hf n x g' i).1 := by
  intro i hi
  change kepPoissonKeys hf n x g (i + 1) - kepPoissonKeys hf n x g i =
    kepPoissonKeys hf n x g' (i + 1) - kepPoissonKeys hf n x g' i
  rw [kepPoissonKeys_prefix hf n x (Nat.succ_le_of_lt hi) hp,
    kepPoissonKeys_prefix hf n x hi.le hp]

def kepPoissonPivot {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (ell j : ℕ)
    (g : ℕ → ℝ) : ℕ∞ :=
  completedPivot eps (kepPoissonPairs hf n x g) ell j

theorem isStoppingRule_kepPoissonPivot {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (ell j : ℕ) :
    IsStoppingRule (kepPoissonPivot hf eps n x ell j) := by
  have hk (k : ℕ) : Measurable (fun g : ℕ → ℝ => kepPoissonKeys hf n x g k) := by
    change Measurable (fun g : ℕ → ℝ => (kepIntensityOrderIso hf).symm
      (kepIntensityPrimitive f x + gapKeys g k / n))
    exact (kepIntensityOrderIso hf).symm.continuous.measurable.comp
      (measurable_const.add (((measurable_pi_apply k).comp measurable_gapKeys).div_const n))
  have hm : Measurable (fun g : ℕ → ℝ => kepPoissonPairs hf n x g) := by
    refine measurable_pi_lambda _ fun i => ?_
    exact ((hk (i + 1)).sub (hk i)).prodMk measurable_const
  exact isStoppingRule_completedPivot_of_prefix hm eps ell j
    (fun _ _ _ hp => kepPoissonPairs_prefix hf n x hp)

theorem measurable_kepPoissonPivot {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n : ℝ) (ell j : ℕ) :
    Measurable (fun p : ℝ × (ℕ → ℝ) => kepPoissonPivot hf eps n p.1 ell j p.2) := by
  have hs : IsStoppingRule (fun z : ℕ → ℝ × ℕ => completedPivot eps z ell j) :=
    isStoppingRule_completedPivot_of_prefix measurable_id eps ell j
      (fun _ _ _ hp i hi => congrArg Prod.fst (hp i hi))
  exact hs.measurable.comp (measurable_kepPoissonPairs hf n)

theorem kepPoissonPivot_eq_original_of_finite {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) {eps n x : ℝ} {ell j r : ℕ}
    {g : ℕ → ℝ} (hr : kepPoissonPivot hf eps n x ell j g = r) :
    layerPivot eps (kepPoissonPairs hf n x g) ell j = r :=
  completedPivot_eq_original_of_finite (fun _ => rfl) hr

theorem kepPoissonPivot_restart_joint {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (ell j : ℕ)
    (hfin : ∀ᵐ g ∂expSeqMeasure, kepPoissonPivot hf eps n x ell j g ≠ ⊤) :
    expSeqMeasure.map (fun g =>
      (kepPoissonStoppedAnchor hf n x (kepPoissonPivot hf eps n x ell j) g,
        shiftBy (kepPoissonPivot hf eps n x ell j) g)) =
      (expSeqMeasure.map
        (kepPoissonStoppedAnchor hf n x (kepPoissonPivot hf eps n x ell j))).prod
          expSeqMeasure :=
  kepPoisson_restart_joint hf n x (isStoppingRule_kepPoissonPivot hf eps n x ell j) hfin

theorem kepPoissonPivot_restart_layer_law {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (ell j : ℕ)
    (hfin : ∀ᵐ g ∂expSeqMeasure, kepPoissonPivot hf eps n x ell j g ≠ ⊤) :
    expSeqMeasure.map (fun g =>
      kepPoissonLayerGap hf eps n
        (kepPoissonStoppedAnchor hf n x (kepPoissonPivot hf eps n x ell j) g) ell
        (shiftBy (kepPoissonPivot hf eps n x ell j) g)) =
      kepPoissonLayerKernel hf eps n ell ∘ₘ
        (expSeqMeasure.map
          (kepPoissonStoppedAnchor hf n x (kepPoissonPivot hf eps n x ell j))) :=
  kepPoisson_restart_layer_law hf eps n x ell
    (isStoppingRule_kepPoissonPivot hf eps n x ell j) hfin

end

end PGM
