import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real

/-!
# The logarithmic expectation bound with explicit integrability

This is Jensen's inequality for `log`, proved from its tangent inequality. It is
used for the uniform binomial--Poisson entropy bound on a finite support.
-/

set_option autoImplicit false

namespace ProbabilityTheory

open MeasureTheory

theorem log_le_tangent {x m : ℝ} (hx : 0 < x) (hm : 0 < m) :
    Real.log x ≤ Real.log m + (x - m) / m := by
  have h := Real.log_le_sub_one_of_pos (div_pos hx hm)
  rw [Real.log_div hx.ne' hm.ne'] at h
  have he : x / m - 1 = (x - m) / m := by field_simp
  rw [he] at h
  linarith only [h]

variable {α : Type*} [MeasurableSpace α] {P : Measure α} [IsProbabilityMeasure P]

theorem integral_log_le_log_integral {X : α → ℝ}
    (hpos : ∀ᵐ x ∂P, 0 < X x) (hInt : Integrable X P)
    (hlog : Integrable (fun x => Real.log (X x)) P)
    (hm : 0 < ∫ x, X x ∂P) :
    (∫ x, Real.log (X x) ∂P) ≤ Real.log (∫ x, X x ∂P) := by
  let m := ∫ x, X x ∂P
  have hi : Integrable (fun x => Real.log m + (X x - m) / m) P :=
    (integrable_const _).add ((hInt.sub (integrable_const _)).div_const m)
  have hle := integral_mono_ae hlog hi (hpos.mono fun x hx => log_le_tangent hx hm)
  have he : (∫ x, Real.log m + (X x - m) / m ∂P) = Real.log m := by
    have hsub : Integrable (fun x => X x - m) P := hInt.sub (integrable_const _)
    have hdiv : Integrable (fun x => (X x - m) / m) P := hsub.div_const m
    rw [integral_add (integrable_const _) hdiv, integral_div]
    have hsubeq := integral_sub hInt (integrable_const m)
    rw [hsubeq]
    simp only [integral_const, probReal_univ, one_smul, m, sub_self, zero_div, add_zero]
  rwa [he] at hle

end ProbabilityTheory
