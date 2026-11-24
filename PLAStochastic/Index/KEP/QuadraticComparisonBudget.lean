import Mathlib.Tactic

/-!
# Reading a linear comparison budget from two quadratic costs

The constant perturbation has a linear horizon factor and the state drift a
cubic horizon factor. A common positive constant pays their square-root sum.
-/

set_option autoImplicit false

namespace PGM

theorem kep_comparison_of_quadratic_budget {H eps r b U V : ℝ}
    (heps : 0 ≤ eps) (hr : 0 ≤ r) (hb : 0 ≤ b) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hH : H ^ 2 ≤ U * eps ^ 2 * r ^ 2 + V * eps ^ 6 * b ^ 2) :
    H ≤ (U + V + 1) * (eps * r + eps ^ 3 * b) := by
  let K := U + V + 1
  have hK : 1 ≤ K := by dsimp [K]; linarith
  have hKU : U ≤ K := by dsimp [K]; linarith
  have hKV : V ≤ K := by dsimp [K]; linarith
  have hK2 : K ≤ K ^ 2 := by nlinarith
  have hu : U * (eps ^ 2 * r ^ 2) ≤ K ^ 2 * (eps ^ 2 * r ^ 2) :=
    mul_le_mul_of_nonneg_right (hKU.trans hK2) (by positivity)
  have hv : V * (eps ^ 6 * b ^ 2) ≤ K ^ 2 * (eps ^ 6 * b ^ 2) :=
    mul_le_mul_of_nonneg_right (hKV.trans hK2) (by positivity)
  have hc : 0 ≤ (eps * r) * (eps ^ 3 * b) := by positivity
  have hnn : 0 ≤ K * (eps * r + eps ^ 3 * b) := by positivity
  change H ≤ K * (eps * r + eps ^ 3 * b)
  nlinarith

end PGM
