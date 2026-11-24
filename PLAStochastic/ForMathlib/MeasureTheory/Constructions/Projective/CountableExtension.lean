import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.Lemmas

/-!
# Countable projective extension for real probability laws

The construction uses conditional distributions and the Ionescu--Tulcea theorem.
No projective-limit existence assumption enters the realization theorem.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Preorder
open scoped NNReal ENNReal Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- Splitting off the last real coordinate of a finite prefix. -/
def realPrefixSplit (n : ℕ) :
    (Finset.Iic (n + 1) → ℝ) ≃ᵐ (Finset.Iic n → ℝ) × ℝ :=
  (MeasurableEquiv.IicProdIoc (X := fun _ : ℕ => ℝ) n.le_succ).symm.trans
    ((MeasurableEquiv.refl _).prodCongr (MeasurableEquiv.piSingleton (X := fun _ : ℕ => ℝ) n).symm)

variable (P : (n : ℕ) → Measure (Finset.Iic n → ℝ))
variable [∀ n, IsProbabilityMeasure (P n)]

/-- The actual joint measure of the old prefix and the next coordinate. -/
def realPrefixJoint (n : ℕ) : Measure ((Finset.Iic n → ℝ) × ℝ) :=
  (P (n + 1)).map (realPrefixSplit n)

instance (n : ℕ) : IsProbabilityMeasure (realPrefixJoint P n) := by
  unfold realPrefixJoint
  exact Measure.isProbabilityMeasure_map (realPrefixSplit n).measurable.aemeasurable

/-- The conditional law of the next coordinate, obtained by genuine disintegration. -/
def realPrefixKernel (n : ℕ) : Kernel (Finset.Iic n → ℝ) ℝ :=
  (realPrefixJoint P n).condKernel

instance (n : ℕ) : IsMarkovKernel (realPrefixKernel P n) := by
  unfold realPrefixKernel
  infer_instance

omit [∀ n, IsProbabilityMeasure (P n)] in
theorem realPrefixJoint_fst
    (hP : ∀ n, (P (n + 1)).map (frestrictLe₂ (π := fun _ : ℕ => ℝ) n.le_succ) = P n) (n : ℕ) :
    (realPrefixJoint P n).fst = P n := by
  rw [Measure.fst, realPrefixJoint, Measure.map_map measurable_fst (realPrefixSplit n).measurable]
  exact hP n

theorem realPrefixJoint_compProd
    (hP : ∀ n, (P (n + 1)).map (frestrictLe₂ (π := fun _ : ℕ => ℝ) n.le_succ) = P n) (n : ℕ) :
    P n ⊗ₘ realPrefixKernel P n = realPrefixJoint P n := by
  rw [← realPrefixJoint_fst P hP n]
  exact (realPrefixJoint P n).disintegrate (realPrefixJoint P n).condKernel

private theorem realPrefixGlue_comp (n : ℕ) :
    (_root_.IicProdIoc (X := fun _ : ℕ => ℝ) n (n + 1)) ∘
      Prod.map id (MeasurableEquiv.piSingleton (X := fun _ : ℕ => ℝ) n) = (realPrefixSplit n).symm := by
  rfl

theorem realPrefixKernel_step
    (hP : ∀ n, (P (n + 1)).map (frestrictLe₂ (π := fun _ : ℕ => ℝ) n.le_succ) = P n) (n : ℕ) :
    (Kernel.partialTraj (X := fun _ : ℕ => ℝ) (realPrefixKernel P) n (n + 1)) ∘ₘ P n = P (n + 1) := by
  rw [Kernel.partialTraj_succ_self, ← Measure.map_comp _ _ (show Measurable (_root_.IicProdIoc (X := fun _ : ℕ => ℝ) n (n + 1)) from measurable_IicProdIoc),
    ← Measure.compProd_eq_comp_prod]
  rw [Measure.compProd_map (MeasurableEquiv.piSingleton (X := fun _ : ℕ => ℝ) n).measurable]
  rw [Measure.map_map (show Measurable (_root_.IicProdIoc (X := fun _ : ℕ => ℝ) n (n + 1)) from measurable_IicProdIoc) (by fun_prop), realPrefixGlue_comp,
    realPrefixJoint_compProd P hP, realPrefixJoint]
  exact (realPrefixSplit n).map_symm_map

/-- The Ionescu--Tulcea probability measure realizing a consistent sequence of finite laws. -/
def realPrefixMeasure : Measure (ℕ → ℝ) := Kernel.traj (X := fun _ : ℕ => ℝ) (realPrefixKernel P) 0 ∘ₘ P 0

instance : IsProbabilityMeasure (realPrefixMeasure P) := by
  unfold realPrefixMeasure
  infer_instance

theorem realPrefixMeasure_map_prefix
    (hP : ∀ n, (P (n + 1)).map (frestrictLe₂ (π := fun _ : ℕ => ℝ) n.le_succ) = P n) (n : ℕ) :
    (realPrefixMeasure P).map (frestrictLe (π := fun _ : ℕ => ℝ) n) = P n := by
  have hfin : ∀ n, Kernel.partialTraj (X := fun _ : ℕ => ℝ) (realPrefixKernel P) 0 n ∘ₘ P 0 = P n := by
    intro n
    induction n with
    | zero => rw [Kernel.partialTraj_self, Measure.id_comp]
    | succ n ih =>
      rw [← Kernel.partialTraj_comp_partialTraj' _ (Nat.zero_le n), ← Measure.comp_assoc, ih]
      exact realPrefixKernel_step P hP n
  rw [realPrefixMeasure, Measure.map_comp _ _ (measurable_frestrictLe (X := fun _ : ℕ => ℝ) n),
    Kernel.traj_map_frestrictLe, hfin]

/-- Every projective family of real probability laws over finite subsets of ℕ
has an actual probability measure as its projective limit. -/
theorem exists_real_nat_projectiveLimit
    (Q : (I : Finset ℕ) → Measure (I → ℝ)) [∀ I, IsProbabilityMeasure (Q I)]
    (hQ : IsProjectiveMeasureFamily (α := fun _ : ℕ => ℝ) Q) :
    ∃ ν : Measure (ℕ → ℝ), IsProbabilityMeasure ν ∧ IsProjectiveLimit (α := fun _ : ℕ => ℝ) ν Q := by
  refine ⟨realPrefixMeasure (fun n => Q (Finset.Iic n)), inferInstance, ?_⟩
  apply (isProjectiveLimit_nat_iff hQ _).mpr
  apply realPrefixMeasure_map_prefix
  intro n
  exact (hQ (Finset.Iic (n + 1)) (Finset.Iic n)
    (Finset.Iic_subset_Iic.mpr n.le_succ)).symm

end BrownianAffine
