import PLAStochastic.ForMathlib.Probability.Hellinger.KernelIterations
import Mathlib.MeasureTheory.MeasurableSpace.Pi

/-!
# Sequence update kernels and common absorbing stopping decisions

A coordinate is sampled from a measurable state-dependent probability kernel.
Updating the observed sequence is a common measurable output on both sides.
An absorbing decision on the same measurable state set therefore charges
exactly the active conditional Hellinger budget.
-/

set_option autoImplicit false

namespace ProbabilityTheory

noncomputable section

open Classical MeasureTheory Set

variable {E : Type*} [MeasurableSpace E]

theorem measurable_sequenceUpdate (i : ℕ) :
    Measurable (fun p : (ℕ → E) × E => Function.update p.1 i p.2) := by
  classical
  exact measurable_update'

def sequenceUpdateKernel (kappa : Kernel (ℕ → E) E) (i : ℕ) :
    Kernel (ℕ → E) (ℕ → E) :=
  ((Kernel.id : Kernel (ℕ → E) (ℕ → E)) ×ₖ kappa).map
    (fun p => Function.update p.1 i p.2)

instance isMarkovKernel_sequenceUpdateKernel
    (kappa : Kernel (ℕ → E) E) [IsMarkovKernel kappa] (i : ℕ) :
    IsMarkovKernel (sequenceUpdateKernel kappa i) :=
  Kernel.IsMarkovKernel.map _ (measurable_sequenceUpdate i)

theorem sequenceUpdateKernel_apply (kappa : Kernel (ℕ → E) E) [IsSFiniteKernel kappa]
    (i : ℕ) (g : ℕ → E) :
    sequenceUpdateKernel kappa i g = (kappa g).map (fun z => Function.update g i z) := by
  have hF : Measurable (fun z => Function.update g i z) :=
    (measurable_sequenceUpdate i).comp (measurable_const.prodMk measurable_id)
  ext s hs
  rw [sequenceUpdateKernel, Kernel.map_apply' _ (measurable_sequenceUpdate i) g hs,
    Kernel.id_prod_apply' _ g ((measurable_sequenceUpdate i) hs), Measure.map_apply hF hs]
  rfl

theorem measureHellinger_sequenceUpdateKernel
    (kappa lam : Kernel (ℕ → E) E) [IsMarkovKernel kappa] [IsMarkovKernel lam]
    (i : ℕ) (g : ℕ → E) :
    measureHellinger (sequenceUpdateKernel kappa i g) (sequenceUpdateKernel lam i g) ≤
      measureHellinger (kappa g) (lam g) := by
  have hF : Measurable (fun z => Function.update g i z) :=
    (measurable_sequenceUpdate i).comp (measurable_const.prodMk measurable_id)
  simpa only [sequenceUpdateKernel_apply] using measureHellinger_map (kappa g) (lam g) hF

theorem measureHellinger_refl {α : Type*} [MeasurableSpace α]
    (P : Measure α) [IsProbabilityMeasure P] : measureHellinger P P = 0 := by
  have hs : measureHellinger P P ^ 2 = 0 := by rw [measureHellinger_sq]; simp
  nlinarith [measureHellinger_nonneg P P]

def absorbingSequenceKernel (s : Set (ℕ → E)) (hs : MeasurableSet s)
    (kappa : Kernel (ℕ → E) E) (i : ℕ) : Kernel (ℕ → E) (ℕ → E) := by
  classical
  exact Kernel.piecewise hs (sequenceUpdateKernel kappa i) Kernel.id

instance isMarkovKernel_absorbingSequenceKernel
    (s : Set (ℕ → E)) (hs : MeasurableSet s)
    (kappa : Kernel (ℕ → E) E) [IsMarkovKernel kappa] (i : ℕ) :
    IsMarkovKernel (absorbingSequenceKernel s hs kappa i) := by
  unfold absorbingSequenceKernel
  infer_instance

theorem absorbingSequenceKernel_apply (s : Set (ℕ → E)) (hs : MeasurableSet s)
    (kappa : Kernel (ℕ → E) E) [IsSFiniteKernel kappa] (i : ℕ) (g : ℕ → E) :
    absorbingSequenceKernel s hs kappa i g =
      if g ∈ s then (kappa g).map (fun z => Function.update g i z) else Measure.dirac g := by
  classical
  simp only [absorbingSequenceKernel, Kernel.piecewise_apply,
    sequenceUpdateKernel_apply, Kernel.id_apply]

theorem measureHellinger_absorbingSequenceKernel
    (s : Set (ℕ → E)) (hs : MeasurableSet s)
    (kappa lam : Kernel (ℕ → E) E) [IsMarkovKernel kappa] [IsMarkovKernel lam]
    (i : ℕ) (g : ℕ → E) :
    measureHellinger (absorbingSequenceKernel s hs kappa i g)
      (absorbingSequenceKernel s hs lam i g) ≤
        s.indicator (fun g => measureHellinger (kappa g) (lam g)) g := by
  classical
  by_cases hg : g ∈ s
  · simpa only [absorbingSequenceKernel, Kernel.piecewise_apply, if_pos hg,
      indicator_of_mem hg] using measureHellinger_sequenceUpdateKernel kappa lam i g
  · simp only [absorbingSequenceKernel, Kernel.piecewise_apply, if_neg hg,
      indicator_of_notMem hg, measureHellinger_refl, le_refl]

end

end ProbabilityTheory
