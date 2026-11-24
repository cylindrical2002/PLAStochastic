import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Recovering a closed CDF from positive-part expectations

Right difference quotients converge to the closed CDF, including any atoms.
No density or atomlessness assumption is used.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace BrownianAffine

set_option backward.isDefEq.respectTransparency false

def positivePartMean (ν : Measure ℝ) (s : ℝ) : ℝ := ∫ x, max (s - x) 0 ∂ν

def positiveStep (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem positiveStep_pos (n : ℕ) : 0 < positiveStep n := by unfold positiveStep; positivity

theorem tendsto_positiveStep : Tendsto positiveStep atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem positivePart_secant_bounds (s x : ℝ) {h : ℝ} (hh : 0 < h) :
    0 ≤ (max (s + h - x) 0 - max (s - x) 0) / h ∧
      (max (s + h - x) 0 - max (s - x) 0) / h ≤ 1 := by
  constructor
  · apply div_nonneg _ hh.le
    exact sub_nonneg.mpr (max_le_max (by linarith) le_rfl)
  · rw [div_le_iff₀ hh, one_mul]
    rcases le_total (s - x) 0 with hx | hx
    · rw [max_eq_right hx]
      have hm : max (s + h - x) 0 ≤ h := max_le (by linarith) hh.le
      linarith
    · rw [max_eq_left hx, max_eq_left (by linarith)]
      linarith

theorem tendsto_positivePart_secant_pointwise (s x : ℝ) :
    Tendsto (fun n => (max (s + positiveStep n - x) 0 - max (s - x) 0) / positiveStep n)
      atTop (𝓝 (if x ≤ s then (1 : ℝ) else 0)) := by
  by_cases hx : x ≤ s
  · rw [if_pos hx]
    apply tendsto_const_nhds.congr'
    apply Eventually.of_forall
    intro n
    have hh := positiveStep_pos n
    dsimp only
    rw [max_eq_left (show 0 ≤ s + positiveStep n - x by linarith),
      max_eq_left (show 0 ≤ s - x by linarith)]
    have he : s + positiveStep n - x - (s - x) = positiveStep n := by ring
    rw [he, div_self hh.ne']
  · rw [if_neg hx]
    apply tendsto_const_nhds.congr'
    filter_upwards [tendsto_positiveStep.eventually (gt_mem_nhds (show 0 < x - s by linarith))]
      with n hn
    rw [max_eq_right (by linarith), max_eq_right (by linarith), sub_self, zero_div]

theorem integrable_positivePart (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hν : ∀ᵐ x ∂ν, 0 ≤ x) (s : ℝ) : Integrable (fun x => max (s - x) 0) ν := by
  apply (integrable_const (max s 0)).mono' (by fun_prop)
  filter_upwards [hν] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le_max (by linarith) le_rfl

theorem tendsto_positivePartMean_secant (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hν : ∀ᵐ x ∂ν, 0 ≤ x) (s : ℝ) :
    Tendsto (fun n => (positivePartMean ν (s + positiveStep n) - positivePartMean ν s) /
        positiveStep n) atTop (𝓝 (ν.real (Iic s))) := by
  have hc := tendsto_integral_of_dominated_convergence (μ := ν) (bound := fun _ => (1 : ℝ))
    (f := fun x => if x ≤ s then (1 : ℝ) else 0)
    (fun n => (by fun_prop : AEStronglyMeasurable
      (fun x => (max (s + positiveStep n - x) 0 - max (s - x) 0) / positiveStep n) ν))
    (integrable_const 1)
    (fun n => Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (positivePart_secant_bounds s x (positiveStep_pos n)).1]
      exact (positivePart_secant_bounds s x (positiveStep_pos n)).2))
    (Eventually.of_forall (fun x => tendsto_positivePart_secant_pointwise s x))
  have he : (∫ x : ℝ, (if x ≤ s then (1 : ℝ) else 0) ∂ν) = ν.real (Iic s) := by
    simpa only [indicator_apply, mem_Iic, Pi.one_apply] using
      (integral_indicator_one (μ := ν) measurableSet_Iic)
  rw [he] at hc
  simpa only [integral_div, integral_sub (integrable_positivePart ν hν _) (integrable_positivePart ν hν _),
    positivePartMean] using hc

/-- A proved ordinary derivative identifies the closed CDF, without presupposing no atoms. -/
theorem cdf_eq_of_hasDerivAt_positivePartMean (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hν : ∀ᵐ x ∂ν, 0 ≤ x) {s d : ℝ} (hd : HasDerivAt (positivePartMean ν) d s) :
    ν.real (Iic s) = d := by
  have ht : Tendsto positiveStep atTop (𝓝[≠] (0 : ℝ)) := by
    apply tendsto_inf.mpr
    refine ⟨tendsto_positiveStep, tendsto_principal.mpr ?_⟩
    exact Eventually.of_forall (fun n => (positiveStep_pos n).ne')
  have h := hd.tendsto_slope_zero.comp ht
  have h' : Tendsto (fun n => (positivePartMean ν (s + positiveStep n) - positivePartMean ν s) /
      positiveStep n) atTop (𝓝 d) := by
    simpa only [Function.comp_def, smul_eq_mul, div_eq_mul_inv, mul_comm] using h
  exact tendsto_nhds_unique (tendsto_positivePartMean_secant ν hν s) h'

end BrownianAffine
