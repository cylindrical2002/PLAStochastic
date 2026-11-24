import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Half-line traces of a square-integrable differentiable function

The estimates retain the exterior energy. Applied to a low-frequency projection
of an interval-supported function, they pay for both jumps of the interval cutoff.
-/

namespace PGM
noncomputable section
open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace

variable {v dv : ℝ → ℂ}

theorem kernelTrace_normSq_deriv_bound (x : ℝ) :
    ‖2 * inner ℝ (v x) (dv x)‖ ≤ ‖v x‖ ^ 2 + ‖dv x‖ ^ 2 := by
  calc
    ‖2 * inner ℝ (v x) (dv x)‖ = 2 * ‖inner ℝ (v x) (dv x)‖ := by
      rw [norm_mul]; norm_num
    _ ≤ 2 * (‖v x‖ * ‖dv x‖) := by
      gcongr
      exact norm_inner_le_norm _ _
    _ ≤ ‖v x‖ ^ 2 + ‖dv x‖ ^ 2 := by nlinarith [sq_nonneg (‖v x‖ - ‖dv x‖)]

theorem kernelTrace_integrable_normSq_deriv (hv : MemLp v 2) (hdv : MemLp dv 2) :
    Integrable (fun x => 2 * inner ℝ (v x) (dv x)) := by
  have hv2 := (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).1 hv
  have hd2 := (memLp_two_iff_integrable_sq_norm hdv.aestronglyMeasurable).1 hdv
  refine (hv2.add hd2).mono' ?_ (Eventually.of_forall kernelTrace_normSq_deriv_bound)
  exact (hv.aestronglyMeasurable.inner hdv.aestronglyMeasurable).const_mul 2

/-- The boundary trace is controlled by the energy on its left, including the
endpoint only to use the standard improper-integral convention. -/
theorem kernelTrace_left (hderiv : ∀ x, HasDerivAt v (dv x) x)
    (hv : MemLp v 2) (hdv : MemLp dv 2) (a : ℝ) :
    ‖v a‖ ^ 2 ≤ (∫ x in Iic a, ‖v x‖ ^ 2) + ∫ x in Iic a, ‖dv x‖ ^ 2 := by
  have hv2 := (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).1 hv
  have hd2 := (memLp_two_iff_integrable_sq_norm hdv.aestronglyMeasurable).1 hdv
  have hdi := kernelTrace_integrable_normSq_deriv hv hdv
  have ht := tendsto_zero_of_hasDerivAt_of_integrableOn_Iic
    (a := a) (fun x _ => (hderiv x).norm_sq) hdi.integrableOn hv2.integrableOn
  have heq := integral_Iic_of_hasDerivAt_of_tendsto'
    (a := a) (fun x _ => (hderiv x).norm_sq) hdi.integrableOn ht
  rw [sub_zero] at heq
  rw [← heq, ← integral_add hv2.integrableOn hd2.integrableOn]
  apply integral_mono_ae hdi.integrableOn (hv2.add hd2).integrableOn
  exact Eventually.of_forall fun x => (le_abs_self _).trans (kernelTrace_normSq_deriv_bound x)

/-- The same trace estimate uses only the exterior energy to the right. -/
theorem kernelTrace_right (hderiv : ∀ x, HasDerivAt v (dv x) x)
    (hv : MemLp v 2) (hdv : MemLp dv 2) (a : ℝ) :
    ‖v a‖ ^ 2 ≤ (∫ x in Ioi a, ‖v x‖ ^ 2) + ∫ x in Ioi a, ‖dv x‖ ^ 2 := by
  have hv2 := (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).1 hv
  have hd2 := (memLp_two_iff_integrable_sq_norm hdv.aestronglyMeasurable).1 hdv
  have hdi := kernelTrace_integrable_normSq_deriv hv hdv
  have ht := tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi
    (a := a) (fun x _ => (hderiv x).norm_sq) hdi.integrableOn hv2.integrableOn
  have heq := integral_Ioi_of_hasDerivAt_of_tendsto'
    (a := a) (fun x _ => (hderiv x).norm_sq) hdi.integrableOn ht
  have heq' : ‖v a‖ ^ 2 = ∫ x in Ioi a, -(2 * inner ℝ (v x) (dv x)) := by
    rw [integral_neg, heq]; ring
  rw [heq', ← integral_add hv2.integrableOn hd2.integrableOn]
  apply integral_mono_ae hdi.neg.integrableOn (hv2.add hd2).integrableOn
  exact Eventually.of_forall fun x => (neg_le_abs _).trans (kernelTrace_normSq_deriv_bound x)

end
end PGM
