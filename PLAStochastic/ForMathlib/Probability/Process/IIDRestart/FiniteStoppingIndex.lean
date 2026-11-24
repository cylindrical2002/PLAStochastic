import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Process.Stopping
import Mathlib.Tactic

/-!
# IID increments after a finite integer stopping index

Indices are zero based: the natural filtration at n contains X 0 through X n.
A Nat-valued stopping index K is the last observed increment, and the first
fresh increment is X (K + 1). Finiteness is encoded by K : Ω → ℕ; this module
does not assume or assert that the repair's first rejection is finite.

The restart identity is proved by the countable partition K = n, rather than
assumed as a strong Markov property.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SwingRepair

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
variable {X : ℕ → Ω → ℝ}

/-- The information in all increments up to and including index n. -/
def incrementFiltration (X : ℕ → Ω → ℝ) (hX : ∀ n, Measurable (X n)) :
    Filtration ℕ mΩ := Filtration.natural X (fun n => (hX n).stronglyMeasurable)

omit mΩ in
/-- Nat-valued stopping indices are everywhere finite when viewed in WithTop. -/
theorem stoppingIndex_isFinite (K : Ω → ℕ) :
    ∀ ω, (K ω : WithTop ℕ) ≠ ⊤ := fun _ => WithTop.coe_ne_top

/-- Mutual independence separates the next increment from the entire past sigma-algebra. -/
theorem next_indep_incrementFiltration (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (n : ℕ) :
    Indep (MeasurableSpace.comap (X (n + 1)) inferInstance)
      (incrementFiltration X hX n) μ := by
  have hd : Disjoint ({n + 1} : Set ℕ) (Set.Iic n) := by simp
  have h := indep_iSup_of_disjoint (fun k => (hX k).comap_le) hi.iIndep hd
  simpa [incrementFiltration, Filtration.natural] using h

/-- A finite stopping index is a measurable natural-valued random variable. -/
theorem stoppingIndex_measurable (hX : ∀ n, Measurable (X n)) {K : Ω → ℕ}
    (hK : IsStoppingTime (incrementFiltration X hX) (fun ω => (K ω : WithTop ℕ))) :
    Measurable K := by
  apply measurable_to_countable'
  intro n
  apply (incrementFiltration X hX).le n
  change MeasurableSet[incrementFiltration X hX n] {ω | K ω = n}
  simpa using hK.measurableSet_eq n

/-- The first increment strictly after a finite stopping index is measurable. -/
theorem nextIncrement_measurable (hX : ∀ n, Measurable (X n)) {K : Ω → ℕ}
    (hK : IsStoppingTime (incrementFiltration X hX) (fun ω => (K ω : WithTop ℕ))) :
    Measurable (fun ω => X (K ω + 1) ω) := by
  have hm : Measurable (fun p : Ω × ℕ => X (p.2 + 1) p.1) :=
    measurable_from_prod_countable_left fun n => hX (n + 1)
  exact hm.comp (measurable_id.prodMk (stoppingIndex_measurable hX hK))

/-- A stopped event, restricted to K = n, only uses increments through n. -/
theorem stoppedEvent_slice_measurable (hX : ∀ n, Measurable (X n)) {K : Ω → ℕ}
    (hK : IsStoppingTime (incrementFiltration X hX) (fun ω => (K ω : WithTop ℕ)))
    {A : Set Ω} (hA : MeasurableSet[hK.measurableSpace] A) (n : ℕ) :
    MeasurableSet[incrementFiltration X hX n] (A ∩ {ω | K ω = n}) := by
  simpa using (hK.measurableSet_inter_eq_iff A n).mp (hA.inter (hK.measurableSet_eq' n))

/-- Countable additivity over the values of an everywhere finite integer index. -/
theorem measure_eq_tsum_stoppingIndex {K : Ω → ℕ} (hK : Measurable K)
    {A : Set Ω} (hA : MeasurableSet A) :
    μ A = ∑' n : ℕ, μ (A ∩ {ω | K ω = n}) := by
  have hu : (⋃ n : ℕ, A ∩ {ω | K ω = n}) = A := by
    ext ω
    simp
  calc
    μ A = μ (⋃ n : ℕ, A ∩ {ω | K ω = n}) := congrArg μ hu.symm
    _ = ∑' n : ℕ, μ (A ∩ {ω | K ω = n}) := ?_
  apply measure_iUnion
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro ω ⟨_, hi⟩ ⟨_, hj⟩
    exact hij (hi.symm.trans hj)
  · intro n
    exact hA.inter (hK (measurableSet_singleton n))

/-- Measurability of selecting from a countable family at a measurable index. -/
theorem countableSelection_measurable {β : Type*} [MeasurableSpace β]
    {Y : ℕ → Ω → β} (hY : ∀ n, Measurable (Y n)) {K : Ω → ℕ} (hK : Measurable K) :
    Measurable (fun ω => Y (K ω) ω) := by
  have hm : Measurable (fun p : Ω × ℕ => Y p.2 p.1) :=
    measurable_from_prod_countable_left hY
  exact hm.comp (measurable_id.prodMk hK)

/--
Countable stopping-index decomposition. All independence hypotheses concern fixed
deterministic indices; independence at the random index is the conclusion.
-/
theorem stoppedSelection_inter_measure {β : Type*} [MeasurableSpace β]
    (hX : ∀ n, Measurable (X n)) {Y : ℕ → Ω → β} {Z : Ω → β}
    (hYm : ∀ n, Measurable (Y n))
    (hiY : ∀ n, Indep (MeasurableSpace.comap (Y n) inferInstance)
      (incrementFiltration X hX n) μ)
    (hidY : ∀ n, IdentDistrib (Y n) Z μ μ)
    {K : Ω → ℕ}
    (hK : IsStoppingTime (incrementFiltration X hX) (fun ω => (K ω : WithTop ℕ)))
    {A : Set Ω} (hA : MeasurableSet[hK.measurableSpace] A)
    {B : Set β} (hB : MeasurableSet B) :
    μ (A ∩ (fun ω => Y (K ω) ω) ⁻¹' B) = μ A * μ (Z ⁻¹' B) := by
  have hKm := stoppingIndex_measurable hX hK
  have hAm : MeasurableSet A := hK.measurableSpace_le _ hA
  have hY := countableSelection_measurable hYm hKm
  rw [measure_eq_tsum_stoppingIndex hKm (hAm.inter (hY hB))]
  calc
    (∑' n : ℕ, μ ((A ∩ (fun ω => Y (K ω) ω) ⁻¹' B) ∩ {ω | K ω = n})) =
        ∑' n : ℕ, μ (A ∩ {ω | K ω = n}) * μ (Z ⁻¹' B) := by
      apply tsum_congr
      intro n
      have heq : (A ∩ (fun ω => Y (K ω) ω) ⁻¹' B) ∩ {ω | K ω = n} =
          Y n ⁻¹' B ∩ (A ∩ {ω | K ω = n}) := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨⟨ha, hb⟩, hn⟩
          exact ⟨by simpa [hn] using hb, ha, hn⟩
        · rintro ⟨hb, ha, hn⟩
          exact ⟨⟨ha, by simpa [hn] using hb⟩, hn⟩
      rw [heq]
      have hmB : MeasurableSet[MeasurableSpace.comap (Y n) inferInstance]
          (Y n ⁻¹' B) := ⟨B, hB, rfl⟩
      rw [(Indep_iff _ _ μ).mp (hiY n)
        _ _ hmB (stoppedEvent_slice_measurable hX hK hA n)]
      rw [(hidY n).measure_mem_eq hB, mul_comm]
    _ = μ A * μ (Z ⁻¹' B) := by
      rw [ENNReal.tsum_mul_right, ← measure_eq_tsum_stoppingIndex hKm hAm]

/--
The restart factorization for the first fresh increment. The only distributional
assumptions are the original sequence's mutual independence and identical laws.
-/
theorem nextIncrement_inter_measure (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ)
    {K : Ω → ℕ}
    (hK : IsStoppingTime (incrementFiltration X hX) (fun ω => (K ω : WithTop ℕ)))
    {A : Set Ω} (hA : MeasurableSet[hK.measurableSpace] A)
    {B : Set ℝ} (hB : MeasurableSet B) :
    μ (A ∩ (fun ω => X (K ω + 1) ω) ⁻¹' B) = μ A * μ (X 0 ⁻¹' B) :=
  stoppedSelection_inter_measure hX (fun n => hX (n + 1))
    (next_indep_incrementFiltration hX hi) (fun n => hid (n + 1)) hK hA hB

/-- The next increment has the original increment law. -/
theorem nextIncrement_identDistrib [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ) {K : Ω → ℕ}
    (hK : IsStoppingTime (incrementFiltration X hX) (fun ω => (K ω : WithTop ℕ))) :
    IdentDistrib (fun ω => X (K ω + 1) ω) (X 0) μ μ := by
  refine ⟨(nextIncrement_measurable hX hK).aemeasurable, (hX 0).aemeasurable, ?_⟩
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply (nextIncrement_measurable hX hK) hB,
    Measure.map_apply (hX 0) hB]
  simpa using nextIncrement_inter_measure hX hi hid hK MeasurableSet.univ hB

/-- The next increment is independent of the entire stopped sigma-algebra. -/
theorem nextIncrement_indep_stopped [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ) {K : Ω → ℕ}
    (hK : IsStoppingTime (incrementFiltration X hX) (fun ω => (K ω : WithTop ℕ))) :
    Indep (MeasurableSpace.comap (fun ω => X (K ω + 1) ω) inferInstance)
      hK.measurableSpace μ := by
  apply (Indep_iff _ _ μ).mpr
  intro C A hC hA
  rcases hC with ⟨B, hB, rfl⟩
  rw [Set.inter_comm, nextIncrement_inter_measure hX hi hid hK hA hB,
    (nextIncrement_identDistrib hX hi hid hK).measure_mem_eq hB, mul_comm]

/-- Any fixed finite block strictly after n is independent of the information through n. -/
theorem futureBlock_indep_incrementFiltration (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (n r : ℕ) :
    Indep (MeasurableSpace.comap (fun ω (j : Fin r) => X (n + 1 + j.val) ω) inferInstance)
      (incrementFiltration X hX n) μ := by
  have hd : Disjoint (Set.Ioi n) (Set.Iic n) := by
    apply Set.disjoint_left.mpr
    intro i hi₁ hi₂
    change n < i at hi₁
    change i ≤ n at hi₂
    omega
  have h := indep_iSup_of_disjoint (fun k => (hX k).comap_le) hi.iIndep hd
  have hcomap :
      MeasurableSpace.comap (fun ω (j : Fin r) => X (n + 1 + j.val) ω) inferInstance ≤
        ⨆ i ∈ Set.Ioi n, MeasurableSpace.comap (X i) inferInstance := by
    rw [MeasurableSpace.comap_process_pi]
    refine iSup_le fun j => ?_
    exact le_iSup_of_le (n + 1 + j.val) (le_iSup_of_le (by simp; omega) le_rfl)
  simpa [incrementFiltration, Filtration.natural] using indep_of_indep_of_le_left h hcomap

/-- Identical marginals and mutual independence give identical laws of finite blocks. -/
theorem futureBlock_identDistrib (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ) (n r : ℕ) :
    IdentDistrib (fun ω (j : Fin r) => X (n + 1 + j.val) ω)
      (fun ω (j : Fin r) => X j.val ω) μ μ := by
  have hshift : iIndepFun (fun j : Fin r => X (n + 1 + j.val)) μ :=
    hi.precomp (g := fun j : Fin r => n + 1 + j.val)
      (by intro i j hij; apply Fin.ext; dsimp at hij; omega)
  have hprefix : iIndepFun (fun j : Fin r => X j.val) μ :=
    hi.precomp Fin.val_injective
  refine ⟨(measurable_pi_lambda _ fun j : Fin r => hX (n + 1 + j.val)).aemeasurable,
    (measurable_pi_lambda _ fun j : Fin r => hX j.val).aemeasurable, ?_⟩
  rw [hshift.map_fun_eq_pi_map (fun j : Fin r => (hX (n + 1 + j.val)).aemeasurable),
    hprefix.map_fun_eq_pi_map (fun j : Fin r => (hX j.val).aemeasurable)]
  congr 1
  funext j
  exact (hid (n + 1 + j.val)).map_eq.trans (hid j.val).map_eq.symm

/-- The entire finite block after a stopping index is a measurable random vector. -/
theorem stoppedBlock_measurable (hX : ∀ n, Measurable (X n)) {K : Ω → ℕ}
    (hK : IsStoppingTime (incrementFiltration X hX) (fun ω => (K ω : WithTop ℕ)))
    (r : ℕ) : Measurable (fun ω (j : Fin r) => X (K ω + 1 + j.val) ω) :=
  countableSelection_measurable
    (fun n => measurable_pi_lambda _ fun j : Fin r => hX (n + 1 + j.val))
    (stoppingIndex_measurable hX hK)

/-- The finite future block has its original joint law on every stopped event. -/
theorem stoppedBlock_inter_measure (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ)
    {K : Ω → ℕ}
    (hK : IsStoppingTime (incrementFiltration X hX) (fun ω => (K ω : WithTop ℕ)))
    (r : ℕ) {A : Set Ω} (hA : MeasurableSet[hK.measurableSpace] A)
    {B : Set (Fin r → ℝ)} (hB : MeasurableSet B) :
    μ (A ∩ (fun ω (j : Fin r) => X (K ω + 1 + j.val) ω) ⁻¹' B) =
      μ A * μ ((fun ω (j : Fin r) => X j.val ω) ⁻¹' B) :=
  stoppedSelection_inter_measure hX
    (fun n => measurable_pi_lambda _ fun j : Fin r => hX (n + 1 + j.val))
    (fun n => futureBlock_indep_incrementFiltration hX hi n r)
    (fun n => futureBlock_identDistrib hX hi hid n r) hK hA hB

/-- Every finite future block has the same joint distribution as the original prefix. -/
theorem stoppedBlock_identDistrib [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ) {K : Ω → ℕ}
    (hK : IsStoppingTime (incrementFiltration X hX) (fun ω => (K ω : WithTop ℕ)))
    (r : ℕ) :
    IdentDistrib (fun ω (j : Fin r) => X (K ω + 1 + j.val) ω)
      (fun ω (j : Fin r) => X j.val ω) μ μ := by
  refine ⟨(stoppedBlock_measurable hX hK r).aemeasurable,
    (measurable_pi_lambda _ fun j : Fin r => hX j.val).aemeasurable, ?_⟩
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply (stoppedBlock_measurable hX hK r) hB,
    Measure.map_apply (measurable_pi_lambda _ fun j : Fin r => hX j.val) hB]
  simpa using stoppedBlock_inter_measure hX hi hid hK r MeasurableSet.univ hB

/-- Every finite future block is independent of the entire stopped sigma-algebra. -/
theorem stoppedBlock_indep_stopped [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ) {K : Ω → ℕ}
    (hK : IsStoppingTime (incrementFiltration X hX) (fun ω => (K ω : WithTop ℕ)))
    (r : ℕ) :
    Indep (MeasurableSpace.comap
      (fun ω (j : Fin r) => X (K ω + 1 + j.val) ω) inferInstance) hK.measurableSpace μ := by
  apply (Indep_iff _ _ μ).mpr
  intro C A hC hA
  rcases hC with ⟨B, hB, rfl⟩
  rw [Set.inter_comm, stoppedBlock_inter_measure hX hi hid hK r hA hB,
    (stoppedBlock_identDistrib hX hi hid hK r).measure_mem_eq hB, mul_comm]

end SwingRepair
