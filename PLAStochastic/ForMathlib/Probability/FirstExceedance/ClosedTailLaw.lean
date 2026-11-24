import PLAStochastic.ForMathlib.Probability.FirstExceedance.Time
import Mathlib.Probability.IdentDistrib

/-!
# Distributional tools for extended nonnegative lifetimes

Finite-threshold closed tails determine the entire law, including its possible
atom at infinity. The inverse-square comparison retains zero errors as infinite
inverse lifetimes.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace BrownianAffine

theorem measure_eq_of_nnreal_closed_tails (μ ν : Measure ℝ≥0∞)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ r : ℝ≥0, μ (Ici (r : ℝ≥0∞)) = ν (Ici (r : ℝ≥0∞))) : μ = ν := by
  apply Measure.ext_of_Ici
  intro a
  by_cases ha : a = ⊤
  · subst a
    rw [Ici_top, ← ENNReal.iInter_Ici_coe_nat]
    have hanti : Antitone (fun n : ℕ => Ici (n : ℝ≥0∞)) := by
      intro m n hmn
      exact Ici_subset_Ici.mpr (by exact_mod_cast hmn)
    rw [hanti.measure_iInter (μ := μ) (fun _ => measurableSet_Ici.nullMeasurableSet)
      ⟨0, measure_ne_top _ _⟩,
      hanti.measure_iInter (μ := ν) (fun _ => measurableSet_Ici.nullMeasurableSet)
      ⟨0, measure_ne_top _ _⟩]
    apply iInf_congr
    intro n
    simpa using h (n : ℝ≥0)
  · lift a to ℝ≥0 using ha
    exact h a

theorem identDistrib_of_nnreal_closed_tails {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {X : Ω → ℝ≥0∞} {Y : Ξ → ℝ≥0∞}
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y ν)
    (h : ∀ r : ℝ≥0, μ {ω | (r : ℝ≥0∞) ≤ X ω} = ν {ω | (r : ℝ≥0∞) ≤ Y ω}) :
    IdentDistrib X Y μ ν := by
  refine ⟨hX, hY, measure_eq_of_nnreal_closed_tails _ _ ?_⟩
  intro r
  rw [Measure.map_apply_of_aemeasurable hX measurableSet_Ici,
    Measure.map_apply_of_aemeasurable hY measurableSet_Ici]
  exact h r

/-- The inverse-square closed tail is the scaled-error sublevel event. -/
theorem le_inverse_square_iff (t : ℝ≥0) {d : ℝ} (hd : 0 ≤ d) :
    (t : ℝ≥0∞) ≤ ((ENNReal.ofReal d) ^ 2)⁻¹ ↔ Real.sqrt (t : ℝ) * d ≤ 1 := by
  have hm : ENNReal.ofReal ((t : ℝ) * d ^ 2) =
      ENNReal.ofReal (t : ℝ) * ENNReal.ofReal (d ^ 2) := ENNReal.ofReal_mul t.property
  have ht : (t : ℝ≥0∞) = ENNReal.ofReal (t : ℝ) := ENNReal.ofReal_coe_nnreal.symm
  rw [ENNReal.le_inv_iff_mul_le, ← ENNReal.ofReal_pow hd, ht, ← hm,
    ENNReal.ofReal_le_one]
  have hsquare : (Real.sqrt (t : ℝ) * d) ^ 2 = (t : ℝ) * d ^ 2 := by
    have htroot : Real.sqrt (t : ℝ) ^ 2 = (t : ℝ) := Real.sq_sqrt t.property
    rw [mul_pow, htroot]
  have hnonneg : 0 ≤ Real.sqrt (t : ℝ) * d := mul_nonneg (Real.sqrt_nonneg _) hd
  constructor <;> intro h <;> nlinarith

theorem le_scaled_inverse_square_iff (t : ℝ≥0) {d ε : ℝ} (hd : 0 ≤ d) (hε : 0 < ε) :
    (t : ℝ≥0∞) ≤ (ENNReal.ofReal ε) ^ 2 / (ENNReal.ofReal d) ^ 2 ↔
      Real.sqrt (t : ℝ) * d ≤ ε := by
  have hnum : (ENNReal.ofReal ε) ^ 2 ≠ 0 := pow_ne_zero _ (ne_of_gt (ENNReal.ofReal_pos.mpr hε))
  have hm : ENNReal.ofReal ((t : ℝ) * d ^ 2) =
      ENNReal.ofReal (t : ℝ) * ENNReal.ofReal (d ^ 2) := ENNReal.ofReal_mul t.property
  rw [ENNReal.le_div_iff_mul_le (Or.inr hnum) (Or.inr (by finiteness)),
    ← ENNReal.ofReal_pow hd, ← ENNReal.ofReal_pow hε.le]
  have ht : (t : ℝ≥0∞) = ENNReal.ofReal (t : ℝ) := ENNReal.ofReal_coe_nnreal.symm
  rw [ht, ← hm, ENNReal.ofReal_le_ofReal_iff (sq_nonneg ε)]
  have hsquare : (Real.sqrt (t : ℝ) * d) ^ 2 = (t : ℝ) * d ^ 2 := by
    have htroot : Real.sqrt (t : ℝ) ^ 2 = (t : ℝ) := Real.sq_sqrt t.property
    rw [mul_pow, htroot]
  have hnonneg : 0 ≤ Real.sqrt (t : ℝ) * d := mul_nonneg (Real.sqrt_nonneg _) hd
  constructor <;> intro h <;> nlinarith

end BrownianAffine
