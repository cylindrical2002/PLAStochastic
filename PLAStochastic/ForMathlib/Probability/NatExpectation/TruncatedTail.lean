import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite tail sums for an integrable natural-valued random variable

This gives lower bounds without extending a tail sum to infinity. For height,
the early-termination probabilities can be summed over the comparison levels,
and their sum is subtracted from the number of levels.
-/

set_option autoImplicit false

namespace ProbabilityTheory

open MeasureTheory Finset Set

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [MeasurableSpace Ω] in
theorem sum_indicator_nat_gt (H : Ω → ℕ) (L : ℕ) (ω : Ω) :
    ∑ l ∈ range L, ({ω | l < H ω}.indicator (fun _ => (1 : ℝ)) ω) =
      (min (H ω) L : ℕ) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [sum_range_succ, ih]
    by_cases h : L < H ω
    · rw [indicator_of_mem (show ω ∈ {ω | L < H ω} from h)]
      have hmin : min (H ω) L = L := min_eq_right (by omega)
      have hmin' : min (H ω) (L + 1) = L + 1 := min_eq_right (by omega)
      simp [hmin, hmin']
    · rw [indicator_of_notMem (show ω ∉ {ω | L < H ω} from h)]
      have hmin : min (H ω) L = H ω := min_eq_left (by omega)
      have hmin' : min (H ω) (L + 1) = H ω := min_eq_left (by omega)
      simp [hmin, hmin']

/-- The integral of the truncated variable is the finite sum of its tail probabilities. -/
theorem integral_min_nat_eq_sum_tail {H : Ω → ℕ} (hH : Measurable H) (L : ℕ) :
    (∫ ω, ((min (H ω) L : ℕ) : ℝ) ∂P) = ∑ l ∈ range L, P.real {ω | l < H ω} := by
  have hs (l : ℕ) : MeasurableSet {ω | l < H ω} := hH (measurableSet_lt measurable_const measurable_id)
  have hi (l : ℕ) : Integrable ({ω | l < H ω}.indicator (fun _ => (1 : ℝ))) P :=
    (integrable_const _).indicator (hs l)
  rw [show (fun ω => ((min (H ω) L : ℕ) : ℝ)) =
    (fun ω => ∑ l ∈ range L, ({ω | l < H ω}.indicator (fun _ => (1 : ℝ)) ω)) from
      funext (fun ω => (sum_indicator_nat_gt H L ω).symm)]
  rw [integral_finsetSum _ (fun l _ => hi l)]
  apply sum_congr rfl
  intro l _
  exact integral_indicator_one (hs l)

/-- A finite collection of early-termination probabilities gives an expectation lower bound. -/
theorem nat_sub_sum_early_le_integral {H : Ω → ℕ} (hH : Measurable H)
    (hInt : Integrable (fun ω => (H ω : ℝ)) P) (L : ℕ) :
    (L : ℝ) - ∑ l ∈ range L, P.real {ω | H ω ≤ l} ≤ ∫ ω, (H ω : ℝ) ∂P := by
  have hi : Integrable (fun ω => ((min (H ω) L : ℕ) : ℝ)) P :=
    Integrable.of_bound (measurable_from_nat.comp
      (hH.min measurable_const)).aestronglyMeasurable L
      (ae_of_all _ fun ω => by
        rw [Real.norm_natCast]
        exact_mod_cast min_le_right (H ω) L)
  have hle := integral_mono hi hInt (fun ω =>
    Nat.cast_le.mpr (min_le_left (H ω) L))
  rw [integral_min_nat_eq_sum_tail hH L] at hle
  have heq : ∑ l ∈ range L, P.real {ω | l < H ω} =
      (L : ℝ) - ∑ l ∈ range L, P.real {ω | H ω ≤ l} := by
    have hs (l : ℕ) : MeasurableSet {ω | H ω ≤ l} :=
      hH (measurableSet_le measurable_id measurable_const)
    have he (l : ℕ) : P.real {ω | l < H ω} = 1 - P.real {ω | H ω ≤ l} := by
      have hc : {ω | l < H ω} = {ω | H ω ≤ l}ᶜ := by ext ω; simp
      rw [hc, measureReal_compl (hs l)]
      simp
    simp_rw [he, sum_sub_distrib]
    simp
  rwa [heq] at hle

end ProbabilityTheory
