import PLAStochastic.ForMathlib.Probability.OrderStatistics.OrderedSimplex
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic

/-!
# Uniform order statistics

If `U 0, …, U (n-1)` are independent and uniform on `[0, 1]`, the monotone rearrangement
`sortVec U` has law `n! • volume.restrict (simplex n)` (`map_sortVec_uniform`).

Up to the null set of ties and boundary points, the cube `[0, 1]ⁿ` is the disjoint union
over permutations `σ` of the regions `{u | u ∘ σ ∈ simplex n}`; on each region
`sortVec u = u ∘ σ`, a measure-preserving coordinate permutation onto the simplex.
-/

noncomputable section

namespace PGM.Renyi

open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal Nat

variable {n : ℕ}

/-- The unit cube `[0, 1]ⁿ`. -/
def cube (n : ℕ) : Set (Fin n → ℝ) :=
  univ.pi fun _ => Icc (0 : ℝ) 1

/-- The region on which `σ` sorts `u` strictly into the open simplex. -/
def sortRegion (σ : Equiv.Perm (Fin n)) : Set (Fin n → ℝ) :=
  (fun u => u ∘ σ) ⁻¹' simplex n

theorem measurableSet_sortRegion (σ : Equiv.Perm (Fin n)) : MeasurableSet (sortRegion σ) :=
  measurable_comp_perm σ measurableSet_simplex

theorem sortVec_eq_of_mem_sortRegion {σ : Equiv.Perm (Fin n)} {u : Fin n → ℝ}
    (hu : u ∈ sortRegion σ) : sortVec u = u ∘ σ :=
  sortVec_eq_of_monotone hu.1.monotone

theorem pairwise_disjoint_sortRegion :
    Pairwise (Disjoint on (sortRegion : Equiv.Perm (Fin n) → Set (Fin n → ℝ))) := by
  intro σ τ hστ
  rw [Function.onFun, Set.disjoint_left]
  intro u hσ hτ
  apply hστ
  have heq : u ∘ σ = u ∘ τ :=
    (sortVec_eq_of_mem_sortRegion hσ).symm.trans (sortVec_eq_of_mem_sortRegion hτ)
  have hinj : Injective u := by
    have hu : u = (u ∘ σ) ∘ σ.symm := by
      funext i
      simp
    rw [hu]
    exact hσ.1.injective.comp σ.symm.injective
  exact Equiv.ext fun i => hinj (congrFun heq i)

theorem iUnion_sortRegion_subset_cube : (⋃ σ : Equiv.Perm (Fin n), sortRegion σ) ⊆ cube n := by
  intro u hu
  obtain ⟨σ, hσ⟩ := mem_iUnion.1 hu
  intro i _
  have h0 := hσ.2.1 (σ.symm i)
  have h1 := hσ.2.2 (σ.symm i)
  simp only [comp_apply, Equiv.apply_symm_apply] at h0 h1
  exact ⟨h0.le, h1.le⟩

theorem cube_diff_iUnion_sortRegion_subset :
    cube n \ (⋃ σ : Equiv.Perm (Fin n), sortRegion σ) ⊆ exceptional n := by
  rintro u ⟨hcube, hnot⟩
  by_contra hex
  simp only [exceptional, mem_union, mem_ofPred_eq, not_or, not_exists, not_and] at hex
  obtain ⟨⟨hinj, h0⟩, h1⟩ := hex
  have hinj' : Injective u := fun i j hij => by
    by_contra hne
    exact hinj i j hne hij
  refine hnot (mem_iUnion.2 ⟨Tuple.sort u, ?_, fun i => ?_, fun i => ?_⟩)
  · exact (Tuple.monotone_sort u).strictMono_of_injective (hinj'.comp (Tuple.sort u).injective)
  · exact lt_of_le_of_ne (hcube _ (mem_univ _)).1 fun h => h0 _ h.symm
  · exact lt_of_le_of_ne (hcube _ (mem_univ _)).2 (h1 _)

theorem iUnion_sortRegion_ae_eq_cube :
    (⋃ σ : Equiv.Perm (Fin n), sortRegion σ) =ᵐ[volume] cube n := by
  refine ae_eq_set.2 ⟨?_, measure_mono_null cube_diff_iUnion_sortRegion_subset volume_exceptional⟩
  rw [sdiff_eq_empty.2 iUnion_sortRegion_subset_cube, measure_empty]

theorem map_sortVec_restrict_sortRegion (σ : Equiv.Perm (Fin n)) :
    (volume.restrict (sortRegion σ)).map sortVec = volume.restrict (simplex n) := by
  have hae : sortVec =ᵐ[volume.restrict (sortRegion σ)] fun u => u ∘ σ :=
    ae_restrict_of_forall_mem (measurableSet_sortRegion σ) fun u hu =>
      sortVec_eq_of_mem_sortRegion hu
  rw [Measure.map_congr hae]
  exact ((measurePreserving_comp_perm σ).restrict_preimage measurableSet_simplex).map_eq

/-- Sorting Lebesgue measure on the unit cube gives `n!` times Lebesgue measure on the simplex. -/
theorem map_sortVec_cube :
    (volume.restrict (cube n)).map sortVec = (n ! : ℝ≥0∞) • volume.restrict (simplex n) := by
  rw [← Measure.restrict_congr_set iUnion_sortRegion_ae_eq_cube,
    Measure.restrict_iUnion pairwise_disjoint_sortRegion measurableSet_sortRegion,
    Measure.map_sum measurable_sortVec.aemeasurable]
  simp_rw [map_sortVec_restrict_sortRegion]
  rw [Measure.sum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ≥0∞]

/-- **Uniform order statistics.**  The sorted vector of `n` independent uniform `[0, 1]`
variables has density `n!` on the open simplex `{0 < u₀ < ⋯ < u_{n-1} < 1}`. -/
theorem map_sortVec_uniform {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {U : Fin n → Ω → ℝ} (hU : ∀ i, HasLaw (U i) (volume.restrict (Icc (0 : ℝ) 1)) P)
    (hind : iIndepFun U P) :
    P.map (fun ω => sortVec fun i => U i ω) = (n ! : ℝ≥0∞) • volume.restrict (simplex n) := by
  have hX := hind.hasLaw_pi hU
  have hmap : P.map (fun ω => sortVec fun i => U i ω) = (P.map fun ω i => U i ω).map sortVec :=
    (AEMeasurable.map_map_of_aemeasurable measurable_sortVec.aemeasurable hX.aemeasurable).symm
  rw [hmap, hX.map_eq, ← Measure.restrict_pi_pi, ← volume_pi]
  exact map_sortVec_cube

end PGM.Renyi
