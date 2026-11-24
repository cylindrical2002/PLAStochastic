import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! # Integrability of natural-valued variables from geometric even-index tails -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace SwingRepair

/-- Counting even thresholds gives a pointwise upper bound for every natural number. -/
theorem nat_le_one_add_two_mul_tail_sum (m : ℕ) :
    (m : ℝ≥0∞) ≤ 1 + 2 * ∑' k : ℕ, if 2 * k < m then (1 : ℝ≥0∞) else 0 := by
  have hsum : ((m / 2 : ℕ) : ℝ≥0∞) ≤
      ∑' k : ℕ, if 2 * k < m then (1 : ℝ≥0∞) else 0 := by
    have heq : (∑ k ∈ Finset.range (m / 2), if 2 * k < m then (1 : ℝ≥0∞) else 0) =
        (m / 2 : ℕ) := by
      calc
        _ = ∑ _k ∈ Finset.range (m / 2), (1 : ℝ≥0∞) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [if_pos (by have := Finset.mem_range.mp hk; omega)]
        _ = (m / 2 : ℕ) := by simp
    rw [← heq]
    exact ENNReal.sum_le_tsum (Finset.range (m / 2))
  have hnat : (m : ℝ≥0∞) ≤ 1 + 2 * ((m / 2 : ℕ) : ℝ≥0∞) := by
    exact_mod_cast (show m ≤ 1 + 2 * (m / 2) by omega)
  exact hnat.trans (add_le_add_right (mul_le_mul_right hsum 2) 1)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The expectation of a natural-valued variable is bounded by its even-index tail sum. -/
theorem lintegral_natCast_le_even_tail_sum [IsProbabilityMeasure μ]
    {K : Ω → ℕ} (hK : Measurable K) :
    (∫⁻ ω, (K ω : ℝ≥0∞) ∂μ) ≤ 1 + 2 * ∑' k : ℕ, μ {ω | 2 * k < K ω} := by
  let S : ℕ → Set Ω := fun k => {ω | 2 * k < K ω}
  let F : ℕ → Ω → ℝ≥0∞ := fun k => (S k).indicator (fun _ => 1)
  have hS (k : ℕ) : MeasurableSet (S k) := measurableSet_lt measurable_const hK
  have hF (k : ℕ) : Measurable (F k) := measurable_const.indicator (hS k)
  have hpoint (ω : Ω) : (K ω : ℝ≥0∞) ≤ 1 + 2 * ∑' k : ℕ, F k ω := by
    simpa only [F, S, Set.indicator_apply, Set.mem_ofPred_eq] using
      nat_le_one_add_two_mul_tail_sum (K ω)
  calc
    (∫⁻ ω, (K ω : ℝ≥0∞) ∂μ) ≤ ∫⁻ ω, 1 + 2 * ∑' k : ℕ, F k ω ∂μ :=
      lintegral_mono hpoint
    _ = 1 + 2 * ∑' k : ℕ, μ {ω | 2 * k < K ω} := by
      rw [lintegral_add_left measurable_const,
        lintegral_const_mul' 2 _ (by norm_num), lintegral_tsum (fun k => (hF k).aemeasurable)]
      simp only [lintegral_const, measure_univ, mul_one]
      congr 2
      apply tsum_congr
      intro k
      exact lintegral_indicator_fun_one (hS k)

/-- A geometric bound on even-index tails proves finite mean without a real-tail interpolation. -/
theorem integrable_natCast_of_geometric_even_tail [IsProbabilityMeasure μ]
    {K : Ω → ℕ} (hK : Measurable K) {q : ℝ≥0∞} (hq : q < 1)
    (htail : ∀ k : ℕ, μ {ω | 2 * k < K ω} ≤ q ^ k) :
    Integrable (fun ω => (K ω : ℝ)) μ := by
  have hmeas : Measurable (fun ω => (K ω : ℝ)) := measurable_from_nat.comp hK
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simp only [Real.norm_eq_abs, Nat.abs_cast, ENNReal.ofReal_natCast]
  apply lt_of_le_of_lt (lintegral_natCast_le_even_tail_sum hK)
  apply lt_of_le_of_lt
    (add_le_add_right (mul_le_mul_right (ENNReal.tsum_le_tsum htail) 2) 1)
  exact ENNReal.add_lt_top.mpr ⟨by norm_num,
    ENNReal.mul_lt_top (by norm_num) (tsum_geometric_lt_top.mpr hq)⟩

end SwingRepair
