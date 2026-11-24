import PLAStochastic.ForMathlib.Probability.Process.IIDRestart.FiniteStoppingIndex
import Mathlib.Data.Finset.Max

/-!
# Iterating a measurable regenerative split

The hypotheses describe one measurable split of a state into a reward and a fresh
state. Independence and identical distribution of the full sequence of rewards
are conclusions, proved by induction on the least member of each finite index set.
The repair-specific split hypotheses are proved separately from actual stopping.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace SwingRepair

def regenerativeState {S Ω : Type*} (R : S → S) (Z : Ω → S) (n : ℕ) (ω : Ω) : S :=
  R^[n] (Z ω)

def regenerativeFactor {S Ω T : Type*} (D : S → T) (R : S → S) (Z : Ω → S)
    (n : ℕ) (ω : Ω) : T := D (regenerativeState R Z n ω)

variable {S Ω T : Type*} [MeasurableSpace S] [MeasurableSpace Ω] [MeasurableSpace T]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {D : S → T} {R : S → S} {Z : Ω → S}

theorem regenerativeState_measurable (hR : Measurable R) (hZ : Measurable Z) (n : ℕ) :
    Measurable (regenerativeState R Z n) := (hR.iterate n).comp hZ

theorem regenerativeFactor_measurable (hD : Measurable D) (hR : Measurable R)
    (hZ : Measurable Z) (n : ℕ) : Measurable (regenerativeFactor D R Z n) :=
  hD.comp (regenerativeState_measurable hR hZ n)

omit [IsProbabilityMeasure μ] in
/-- Each iterated remainder state has the original state law. -/
theorem regenerativeState_identDistrib (hR : Measurable R) (hZ : Measurable Z)
    (hLaw : IdentDistrib (fun ω => R (Z ω)) Z μ μ) (n : ℕ) :
    IdentDistrib (regenerativeState R Z n) Z μ μ := by
  induction n with
  | zero => exact IdentDistrib.refl hZ.aemeasurable
  | succ n ih =>
    have heq : regenerativeState R Z (n + 1) = fun ω => R (regenerativeState R Z n ω) :=
      funext fun ω => Function.iterate_succ_apply' R n (Z ω)
    rw [heq]
    exact (ih.comp hR).trans hLaw

omit [IsProbabilityMeasure μ] in
/-- Every extracted reward has the same distribution as the first one. -/
theorem regenerativeFactor_identDistrib (hD : Measurable D) (hR : Measurable R)
    (hZ : Measurable Z) (hLaw : IdentDistrib (fun ω => R (Z ω)) Z μ μ) (n : ℕ) :
    IdentDistrib (regenerativeFactor D R Z n) (regenerativeFactor D R Z 0) μ μ :=
  (regenerativeState_identDistrib hR hZ hLaw n).comp hD

/-- The same independent reward/future split holds at every iterated state. -/
theorem regenerativeSplit_indep (hD : Measurable D) (hR : Measurable R)
    (hZ : Measurable Z) (hLaw : IdentDistrib (fun ω => R (Z ω)) Z μ μ)
    (hSplit : IndepFun (fun ω => D (Z ω)) (fun ω => R (Z ω)) μ) (n : ℕ) :
    IndepFun (regenerativeFactor D R Z n) (fun ω => R (regenerativeState R Z n ω)) μ := by
  exact indepFun_of_identDistrib_pair hSplit
    ((regenerativeState_identDistrib hR hZ hLaw n).symm.comp (hD.prodMk hR))

/-- A reward is independent of every finite tuple of strictly later rewards. -/
theorem regenerativeFactor_indep_later (hD : Measurable D) (hR : Measurable R)
    (hZ : Measurable Z) (hLaw : IdentDistrib (fun ω => R (Z ω)) Z μ μ)
    (hSplit : IndepFun (fun ω => D (Z ω)) (fun ω => R (Z ω)) μ)
    (a : ℕ) (s : Finset ℕ) (hord : ∀ i ∈ s, a < i) :
    IndepFun (regenerativeFactor D R Z a)
      (fun ω (i : s) => regenerativeFactor D R Z i.val ω) μ := by
  let G : S → (s → T) := fun x i => D (R^[i.val - (a + 1)] x)
  have hG : Measurable G := measurable_pi_lambda _ fun i =>
    hD.comp (hR.iterate (i.val - (a + 1)))
  have heq : (fun ω (i : s) => regenerativeFactor D R Z i.val ω) =
      G ∘ (fun ω => R (regenerativeState R Z a ω)) := by
    funext ω i
    dsimp [G, regenerativeFactor, regenerativeState]
    rw [← Function.iterate_succ_apply' R a,
      ← Function.iterate_add_apply R (i.val - (a + 1)) (a + 1)]
    rw [Nat.sub_add_cancel (Nat.succ_le_of_lt (hord i.val i.property))]
  rw [heq]
  exact (regenerativeSplit_indep hD hR hZ hLaw hSplit a).comp measurable_id hG

/-- The iterated rewards are genuinely mutually independent, not just pairwise independent. -/
theorem regenerativeFactors_iIndepFun (hD : Measurable D) (hR : Measurable R)
    (hZ : Measurable Z) (hLaw : IdentDistrib (fun ω => R (Z ω)) Z μ μ)
    (hSplit : IndepFun (fun ω => D (Z ω)) (fun ω => R (Z ω)) μ) :
    iIndepFun (regenerativeFactor D R Z) μ := by
  apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro s
  induction s using Finset.induction_on_min with
  | empty => intro sets hsets; simp
  | insert a s hord ih =>
    intro sets hsets
    have ha : a ∉ s := fun ha => (lt_irrefl a) (hord a ha)
    have hs (i : ℕ) (hi : i ∈ s) : MeasurableSet (sets i) :=
      hsets i (Finset.mem_insert_of_mem hi)
    let B : Set (s → T) := {v | ∀ i : s, v i ∈ sets i.val}
    have hB : MeasurableSet B := by
      have heqB : B = ⋂ i : s, (fun v : s → T => v i) ⁻¹' sets i.val := by ext v; simp [B]
      rw [heqB]
      exact MeasurableSet.iInter fun i => (measurable_pi_apply i) (hs i.val i.property)
    have hpre : (fun ω (i : s) => regenerativeFactor D R Z i.val ω) ⁻¹' B =
        ⋂ i ∈ s, regenerativeFactor D R Z i ⁻¹' sets i := by
      ext ω
      simp [B]
    have hpair := (regenerativeFactor_indep_later hD hR hZ hLaw hSplit a s hord).measure_inter_preimage_eq_mul
      _ _ (hsets a (Finset.mem_insert_self _ _)) hB
    rw [hpre] at hpair
    have heq : (⋂ i ∈ insert a s, regenerativeFactor D R Z i ⁻¹' sets i) =
        regenerativeFactor D R Z a ⁻¹' sets a ∩
          ⋂ i ∈ s, regenerativeFactor D R Z i ⁻¹' sets i := by ext ω; simp
    rw [heq, hpair, ih hs, Finset.prod_insert ha]

end SwingRepair
