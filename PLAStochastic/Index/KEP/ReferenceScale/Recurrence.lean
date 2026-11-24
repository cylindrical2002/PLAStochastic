import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The layer-independent second-derivative invariant

The analytic reference-scale theorem must provide the recurrence for the actual
weighted second-derivative norms. This module proves the numerical invariant
used after the exponentially small inheritance coefficient is at most `1/4`.
The polynomial budget is chosen once and does not depend on the layer index.
-/

set_option autoImplicit false

namespace PGM.KEPReferenceScale

theorem sqrt_recurrence_preserves_budget {A B J : ℝ}
    (hA : 0 ≤ A) (hJ : 0 ≤ J) (hJB : J ≤ B)
    (hB : 16 * (A + 1) ^ 2 ≤ B) :
    A * (1 + Real.sqrt J) + J / 4 ≤ B := by
  have hs := Real.sq_sqrt hJ
  have hs0 := Real.sqrt_nonneg J
  have hyoung : A * Real.sqrt J ≤ J / 4 + A ^ 2 := by
    nlinarith [sq_nonneg (Real.sqrt J / 2 - A)]
  nlinarith [sq_nonneg A]

/-- A fixed budget closes every layer once the analytic recurrence is known. -/
theorem uniform_bound_of_recurrence {J : ℕ → ℝ} {A B r : ℝ}
    (hA : 0 ≤ A) (hr : r ≤ 1 / 4)
    (hJ : ∀ j, 0 ≤ J j) (hinit : J 0 ≤ B)
    (hB : 16 * (A + 1) ^ 2 ≤ B)
    (hrec : ∀ j, J (j + 1) ≤ A * (1 + Real.sqrt (J j)) + r * J j) :
    ∀ j, J j ≤ B := by
  intro j
  induction j with
  | zero => exact hinit
  | succ j ih =>
    calc
      J (j + 1) ≤ A * (1 + Real.sqrt (J j)) + r * J j := hrec j
      _ ≤ A * (1 + Real.sqrt (J j)) + J j / 4 := by
        have := mul_le_mul_of_nonneg_right hr (hJ j)
        linarith
      _ ≤ B := sqrt_recurrence_preserves_budget hA (hJ j) ih hB

/-- The cutoff scale error closes after normalization by the growing reference scale. -/
theorem scale_error_bound_of_recurrence {e b : ℕ → ℝ} {a D : ℝ}
    (ha : 0 ≤ a) (hD : 2 * a ≤ D) (hb : ∀ j, 0 ≤ b j)
    (hinit : e 0 ≤ D * b 0)
    (hscale : ∀ j, a * b j ≤ b (j + 1) / 2)
    (hrec : ∀ j, e (j + 1) ≤ a * e j + a * b (j + 1)) :
    ∀ j, e j ≤ D * b j := by
  have hD0 : 0 ≤ D := by linarith
  intro j
  induction j with
  | zero => exact hinit
  | succ j ih =>
    have h1 := mul_le_mul_of_nonneg_left ih ha
    have h2 := mul_le_mul_of_nonneg_left (hscale j) hD0
    have h3 := mul_le_mul_of_nonneg_right hD (hb (j + 1))
    nlinarith [hrec j]

end PGM.KEPReferenceScale
