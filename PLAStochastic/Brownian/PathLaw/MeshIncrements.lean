import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Tactic

/-! # The actual normalized Brownian mesh increments and their full iid Gaussian law -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

namespace BrownianAffine

def brownianMeshIncrement {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (h : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  B ((n + 1 : ℕ) * h) ω - B ((n : ℝ≥0) * h) ω

def normalizedMeshIncrement {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (h : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  brownianMeshIncrement B h n ω / Real.sqrt (h : ℝ)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem brownianMeshIncrement_iIndepFun (hB : IsPreBrownianReal B μ) (h : ℝ≥0) :
    iIndepFun (brownianMeshIncrement B h) μ := by
  apply hB.hasIndepIncrements.nat (t := fun n : ℕ => (n : ℝ≥0) * h)
  intro i j hij
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) h.coe_nonneg

theorem brownianMeshIncrement_hasLaw (hB : IsPreBrownianReal B μ) (h : ℝ≥0) (n : ℕ) :
    HasLaw (brownianMeshIncrement B h n) (gaussianReal 0 h) μ := by
  have hvar : nndist (((n + 1 : ℕ) * h : ℝ≥0) : ℝ) (((n : ℝ≥0) * h : ℝ≥0) : ℝ) = h := by
    apply NNReal.coe_injective
    change dist (((n + 1 : ℕ) * h : ℝ≥0) : ℝ) (((n : ℝ≥0) * h : ℝ≥0) : ℝ) = (h : ℝ)
    rw [Real.dist_eq]
    push_cast
    rw [show ((n : ℝ) + 1) * h - n * h = h by ring, abs_of_nonneg h.coe_nonneg]
  have hL := hB.hasLaw_sub ((n + 1 : ℕ) * h) ((n : ℝ≥0) * h)
  exact ⟨hL.aemeasurable, hL.map_eq.trans (congrArg (gaussianReal 0) hvar)⟩

theorem normalizedMeshIncrement_iIndepFun (hB : IsPreBrownianReal B μ) (h : ℝ≥0) :
    iIndepFun (normalizedMeshIncrement B h) μ :=
  (brownianMeshIncrement_iIndepFun hB h).comp
    (fun _ => fun x : ℝ => x / Real.sqrt (h : ℝ)) (fun _ => by fun_prop)

theorem normalizedMeshIncrement_hasLaw (hB : IsPreBrownianReal B μ)
    (h : ℝ≥0) (hh : h ≠ 0) (n : ℕ) :
    HasLaw (normalizedMeshIncrement B h n) (gaussianReal 0 1) μ := by
  have hsq : NNReal.mk (Real.sqrt (h : ℝ) ^ 2) (sq_nonneg _) = h :=
    Subtype.ext (Real.sq_sqrt h.coe_nonneg)
  have hL := gaussianReal_div_const (brownianMeshIncrement_hasLaw hB h n) (Real.sqrt (h : ℝ))
  change HasLaw (fun ω => brownianMeshIncrement B h n ω / Real.sqrt (h : ℝ))
    (gaussianReal 0 1) μ
  simpa only [zero_div, hsq, div_self hh] using hL

omit [MeasurableSpace Ω] in
/-- The cumulative normalized increments telescope along the actual Brownian mesh. -/
theorem sum_normalizedMeshIncrement (B : ℝ≥0 → Ω → ℝ) (h : ℝ≥0) (n : ℕ) (ω : Ω) :
    ∑ k ∈ Finset.range n, normalizedMeshIncrement B h k ω =
      (B ((n : ℝ≥0) * h) ω - B 0 ω) / Real.sqrt (h : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    unfold normalizedMeshIncrement brownianMeshIncrement
    ring

/-- Any iid standard Gaussian sequence has the law of the entire normalized Brownian mesh sequence.
The two processes may live on different probability spaces. -/
theorem identDistrib_gaussian_mesh_sequence {Ξ : Type*} [MeasurableSpace Ξ] {ν : Measure Ξ}
    {X : ℕ → Ξ → ℝ} (hX : ∀ n, AEMeasurable (X n) ν) (hi : iIndepFun X ν)
    (hG : ∀ n, ν.map (X n) = gaussianReal 0 1)
    (hB : IsPreBrownianReal B μ) (h : ℝ≥0) (hh : h ≠ 0) :
    IdentDistrib (fun ξ (n : ℕ) => X n ξ)
      (fun ω (n : ℕ) => normalizedMeshIncrement B h n ω) ν μ := by
  have hN (n : ℕ) := normalizedMeshIncrement_hasLaw hB h hh n
  refine ⟨aemeasurable_pi_lambda _ hX,
    aemeasurable_pi_lambda _ (fun n => (hN n).aemeasurable), ?_⟩
  rw [hi.map_fun_eq_infinitePi_map₀' hX,
    (normalizedMeshIncrement_iIndepFun hB h).map_fun_eq_infinitePi_map₀'
      (fun n => (hN n).aemeasurable)]
  congr 1
  funext n
  exact (hG n).trans (hN n).map_eq.symm

end BrownianAffine
