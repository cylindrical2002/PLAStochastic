import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Rényi representation: the ordered simplex and the sorting map

`simplex n` is the open ordered simplex `{0 < u₀ < ⋯ < u_{n-1} < 1}` in `Fin n → ℝ`
(for `n = 0` it is the whole one-point space), and `closedSimplex n` its closure
`{0 ≤ u₀ ≤ ⋯ ≤ u_{n-1} ≤ 1}`.  `sortVec u = u ∘ Tuple.sort u` is the monotone
rearrangement of `u`.

This file collects the measure-theoretic facts shared by the two halves of the Rényi
representation:

* the exceptional set (a tie, or a coordinate equal to `0` or `1`) is Lebesgue-null,
  so `simplex n` and `closedSimplex n` agree almost everywhere;
* `sortVec` is measurable, and coordinate permutations preserve Lebesgue measure;
* the Lebesgue integral of a product `∏ i, g i (e i)` factorizes, so a product of
  absolutely continuous laws has the product density.
-/

noncomputable section

namespace PGM.Renyi

open MeasureTheory Set Function
open scoped ENNReal

variable {n : ℕ}

/-- The open ordered simplex `{0 < u₀ < u₁ < ⋯ < u_{n-1} < 1}`. -/
def simplex (n : ℕ) : Set (Fin n → ℝ) :=
  {u | StrictMono u ∧ (∀ i, 0 < u i) ∧ ∀ i, u i < 1}

/-- The closed ordered simplex `{0 ≤ u₀ ≤ u₁ ≤ ⋯ ≤ u_{n-1} ≤ 1}`. -/
def closedSimplex (n : ℕ) : Set (Fin n → ℝ) :=
  {u | Monotone u ∧ (∀ i, 0 ≤ u i) ∧ ∀ i, u i ≤ 1}

/-- The monotone rearrangement of a tuple. -/
def sortVec (u : Fin n → ℝ) : Fin n → ℝ :=
  u ∘ Tuple.sort u

/-- The chain form of the open simplex: `0 < u 0`, `u i < u (i + 1)`, `u (last) < 1`. -/
theorem mem_simplex_succ_iff {u : Fin (n + 1) → ℝ} :
    u ∈ simplex (n + 1) ↔
      0 < u 0 ∧ (∀ i : Fin n, u i.castSucc < u i.succ) ∧ u (Fin.last n) < 1 := by
  simp only [simplex, mem_ofPred_eq, Fin.strictMono_iff_lt_succ]
  constructor
  · rintro ⟨hmono, hpos, hlt⟩
    exact ⟨hpos 0, hmono, hlt _⟩
  · rintro ⟨hpos, hmono, hlt⟩
    have hsm : StrictMono u := Fin.strictMono_iff_lt_succ.2 hmono
    refine ⟨hmono, fun i => ?_, fun i => ?_⟩
    · exact lt_of_lt_of_le hpos (hsm.monotone (Fin.zero_le i))
    · exact lt_of_le_of_lt (hsm.monotone (Fin.le_last i)) hlt

@[simp]
theorem simplex_zero : simplex 0 = univ := by
  ext u
  simp only [simplex, mem_ofPred_eq, mem_univ, iff_true]
  exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩

theorem simplex_subset_closedSimplex : simplex n ⊆ closedSimplex n :=
  fun _ hu => ⟨hu.1.monotone, fun i => (hu.2.1 i).le, fun i => (hu.2.2 i).le⟩

/-- Ties and boundary coordinates. -/
def exceptional (n : ℕ) : Set (Fin n → ℝ) :=
  {u | ∃ i j, i ≠ j ∧ u i = u j} ∪ {u | ∃ i, u i = 0} ∪ {u | ∃ i, u i = 1}

theorem volume_tie {i j : Fin n} (hij : i ≠ j) :
    volume {u : Fin n → ℝ | u i = u j} = 0 := by
  let f : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    (LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ) - LinearMap.proj j
  have hs : {u : Fin n → ℝ | u i = u j} = (LinearMap.ker f : Set (Fin n → ℝ)) := by
    ext u
    simp [f, sub_eq_zero]
  rw [hs]
  refine Measure.addHaar_submodule _ _ fun htop => ?_
  have hmem : (Pi.single i (1 : ℝ) : Fin n → ℝ) ∈ LinearMap.ker f := htop ▸ Submodule.mem_top
  simp [f, hij.symm] at hmem

theorem volume_coord_eq (i : Fin n) (c : ℝ) :
    volume {u : Fin n → ℝ | u i = c} = 0 := by
  rw [volume_pi]
  exact Measure.pi_hyperplane (fun _ : Fin n => (volume : Measure ℝ)) i c

theorem volume_exceptional : volume (exceptional n) = 0 := by
  have h1 : {u : Fin n → ℝ | ∃ i j, i ≠ j ∧ u i = u j} =
      ⋃ i, ⋃ j, ⋃ (_ : i ≠ j), {u | u i = u j} := by
    ext u
    simp
  have h2 : {u : Fin n → ℝ | ∃ i, u i = 0} = ⋃ i, {u | u i = 0} := by
    ext u
    simp
  have h3 : {u : Fin n → ℝ | ∃ i, u i = 1} = ⋃ i, {u | u i = 1} := by
    ext u
    simp
  rw [exceptional, h1, h2, h3]
  refine measure_union_null (measure_union_null ?_ ?_) ?_
  · exact measure_iUnion_null fun i => measure_iUnion_null fun j =>
      measure_iUnion_null fun hij => volume_tie hij
  · exact measure_iUnion_null fun i => volume_coord_eq i 0
  · exact measure_iUnion_null fun i => volume_coord_eq i 1

theorem closedSimplex_diff_subset : closedSimplex n \ simplex n ⊆ exceptional n := by
  rintro u ⟨⟨hmono, hnn, hle⟩, hns⟩
  by_contra hex
  simp only [exceptional, mem_union, mem_ofPred_eq, not_or, not_exists, not_and] at hex
  obtain ⟨⟨hinj, h0⟩, h1⟩ := hex
  refine hns ⟨hmono.strictMono_of_injective fun i j hij => ?_, fun i => ?_, fun i => ?_⟩
  · by_contra hne
    exact hinj i j hne hij
  · exact lt_of_le_of_ne (hnn i) fun h => h0 i h.symm
  · exact lt_of_le_of_ne (hle i) (h1 i)

theorem simplex_ae_eq_closedSimplex : simplex n =ᵐ[volume] closedSimplex n := by
  refine ae_eq_set.2 ⟨?_, measure_mono_null closedSimplex_diff_subset volume_exceptional⟩
  rw [sdiff_eq_empty.2 simplex_subset_closedSimplex, measure_empty]

theorem restrict_simplex_eq_closedSimplex :
    (volume : Measure (Fin n → ℝ)).restrict (simplex n) = volume.restrict (closedSimplex n) :=
  Measure.restrict_congr_set simplex_ae_eq_closedSimplex

theorem measurableSet_simplex : MeasurableSet (simplex n) := by
  have : simplex n = (⋂ i, ⋂ j, ⋂ (_ : i < j), {u : Fin n → ℝ | u i < u j}) ∩
      (⋂ i, {u | 0 < u i}) ∩ ⋂ i, {u | u i < 1} := by
    ext u
    simp [simplex, StrictMono, and_assoc]
  rw [this]
  refine ((MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.iInter
    fun _ => measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j)).inter
    (MeasurableSet.iInter fun i => measurableSet_lt measurable_const (measurable_pi_apply i))).inter
    (MeasurableSet.iInter fun i => measurableSet_lt (measurable_pi_apply i) measurable_const)

theorem measurableSet_closedSimplex : MeasurableSet (closedSimplex n) := by
  have : closedSimplex n = (⋂ i, ⋂ j, ⋂ (_ : i ≤ j), {u : Fin n → ℝ | u i ≤ u j}) ∩
      (⋂ i, {u | 0 ≤ u i}) ∩ ⋂ i, {u | u i ≤ 1} := by
    ext u
    simp [closedSimplex, Monotone, and_assoc]
  rw [this]
  refine ((MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.iInter
    fun _ => measurableSet_le (measurable_pi_apply i) (measurable_pi_apply j)).inter
    (MeasurableSet.iInter fun i => measurableSet_le measurable_const (measurable_pi_apply i))).inter
    (MeasurableSet.iInter fun i => measurableSet_le (measurable_pi_apply i) measurable_const)

/-! ### The sorting map -/

theorem sortVec_eq_of_monotone {u : Fin n → ℝ} {σ : Equiv.Perm (Fin n)}
    (h : Monotone (u ∘ σ)) : sortVec u = u ∘ σ :=
  (Tuple.comp_sort_eq_comp_iff_monotone.2 h).symm

theorem monotone_sortVec (u : Fin n → ℝ) : Monotone (sortVec u) :=
  Tuple.monotone_sort u

theorem measurable_comp_perm (σ : Equiv.Perm (Fin n)) :
    Measurable fun u : Fin n → ℝ => u ∘ σ :=
  measurable_pi_lambda _ fun i => measurable_pi_apply (σ i)

theorem measurableSet_monotone_comp (σ : Equiv.Perm (Fin n)) :
    MeasurableSet {u : Fin n → ℝ | Monotone (u ∘ σ)} := by
  have : {u : Fin n → ℝ | Monotone (u ∘ σ)} =
      ⋂ i, ⋂ j, ⋂ (_ : i ≤ j), {u | u (σ i) ≤ u (σ j)} := by
    ext u
    simp [Monotone]
  rw [this]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.iInter
    fun _ => measurableSet_le (measurable_pi_apply _) (measurable_pi_apply _)

theorem measurable_sortVec : Measurable (sortVec : (Fin n → ℝ) → Fin n → ℝ) := by
  intro A hA
  have : sortVec ⁻¹' A =
      ⋃ σ : Equiv.Perm (Fin n), {u | Monotone (u ∘ σ)} ∩ (fun u => u ∘ σ) ⁻¹' A := by
    ext u
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    constructor
    · intro hu
      exact ⟨Tuple.sort u, Tuple.monotone_sort u, hu⟩
    · rintro ⟨σ, hσ, hu⟩
      rwa [sortVec_eq_of_monotone hσ]
  rw [this]
  exact MeasurableSet.iUnion fun σ =>
    (measurableSet_monotone_comp σ).inter (measurable_comp_perm σ hA)

/-- Permuting coordinates preserves Lebesgue measure on `Fin n → ℝ`. -/
theorem measurePreserving_comp_perm (σ : Equiv.Perm (Fin n)) :
    MeasurePreserving (fun u : Fin n → ℝ => u ∘ σ) volume volume := by
  have h := volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℝ) σ.symm
  have heq : (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) σ.symm :
      (Fin n → ℝ) → Fin n → ℝ) = fun u => u ∘ σ := by
    funext u i
    simp only [MeasurableEquiv.coe_piCongrLeft]
    have := Equiv.piCongrLeft_apply_apply (fun _ : Fin n => ℝ) σ.symm u (σ i)
    simpa using this
  rwa [heq] at h

/-! ### Products of densities -/

/-- Tonelli for a product of one-variable functions on `Fin m → ℝ`. -/
theorem lintegral_pi_prod : ∀ {m : ℕ} (g : Fin m → ℝ → ℝ≥0∞), (∀ i, Measurable (g i)) →
    ∫⁻ e : Fin m → ℝ, ∏ i, g i (e i) = ∏ i, ∫⁻ x, g i x
  | 0, g, _ => by
    simp [volume_pi]
  | m + 1, g, hg => by
    have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm
    rw [← h.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
    have hfun : (fun p : ℝ × (Fin m → ℝ) =>
        ∏ i, g i ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm p i)) =
        fun p => g 0 p.1 * ∏ j : Fin m, g j.succ (p.2 j) := by
      funext p
      rw [Fin.prod_univ_succ]
      simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero']
    rw [Measure.volume_eq_prod, hfun,
      lintegral_prod_mul (f := g 0) (g := fun y : Fin m → ℝ => ∏ j, g j.succ (y j))
        (hg 0).aemeasurable
        (Finset.measurable_prod _ fun j _ => (hg j.succ).comp (measurable_pi_apply j)).aemeasurable,
      lintegral_pi_prod (fun j => g j.succ) fun j => hg j.succ, Fin.prod_univ_succ]

/-- The product of `m` copies of the law `volume.withDensity ρ` has density `∏ i, ρ (e i)`. -/
theorem pi_withDensity {m : ℕ} (ρ : ℝ → ℝ≥0∞) (hρ : Measurable ρ)
    [SigmaFinite (volume.withDensity ρ)] :
    Measure.pi (fun _ : Fin m => volume.withDensity ρ) =
      volume.withDensity (fun e : Fin m → ℝ => ∏ i, ρ (e i)) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have : (univ.pi s).indicator (fun e : Fin m → ℝ => ∏ i, ρ (e i)) =
      fun e => ∏ i, (s i).indicator ρ (e i) := by
    funext e
    by_cases he : e ∈ univ.pi s
    · rw [indicator_of_mem he]
      exact Finset.prod_congr rfl fun i _ => (indicator_of_mem (he i (mem_univ i)) _).symm
    · rw [indicator_of_notMem he]
      simp only [mem_pi, mem_univ, true_implies, not_forall] at he
      obtain ⟨i, hi⟩ := he
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_notMem hi _)).symm
  rw [this, lintegral_pi_prod _ fun i => hρ.indicator (hs i)]
  exact Finset.prod_congr rfl fun i _ => by
    rw [withDensity_apply _ (hs i), lintegral_indicator (hs i)]

end PGM.Renyi
