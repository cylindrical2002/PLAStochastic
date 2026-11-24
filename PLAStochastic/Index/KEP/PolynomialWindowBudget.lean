import PLAStochastic.Index.KEP.QuadraticComparisonBudget

/-!
# Comparison costs at a quadratic stopping window

One window length and its cube give the epsilon and epsilon-cubed factors
after taking the square root of a path comparison budget.
-/

set_option autoImplicit false

namespace PGM

theorem kep_polynomial_window_budget {eps M A C r b u v : ℝ}
    (heps : 1 ≤ eps) (hM0 : 0 ≤ M) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hM : M ≤ A * eps ^ 2) :
    u * M * r ^ 2 + v * b ^ 2 * (M + C * M ^ 3) ≤
      (u * A) * eps ^ 2 * r ^ 2 + (v * (A + C * A ^ 3)) * eps ^ 6 * b ^ 2 := by
  have hpow : eps ^ 2 ≤ eps ^ 6 := by
    have h : eps ^ 2 ≤ eps ^ 2 * eps ^ 4 :=
      le_mul_of_one_le_right (sq_nonneg eps) (one_le_pow₀ heps)
    simpa only [← pow_add] using h
  have hM6 : M ≤ A * eps ^ 6 := hM.trans (mul_le_mul_of_nonneg_left hpow hA)
  have hM3 : M ^ 3 ≤ A ^ 3 * eps ^ 6 := by
    calc
      _ ≤ (A * eps ^ 2) ^ 3 := pow_le_pow_left₀ hM0 hM 3
      _ = _ := by ring
  have hsum : M + C * M ^ 3 ≤ (A + C * A ^ 3) * eps ^ 6 := by
    calc
      _ ≤ A * eps ^ 6 + C * (A ^ 3 * eps ^ 6) :=
        add_le_add hM6 (mul_le_mul_of_nonneg_left hM3 hC)
      _ = _ := by ring
  calc
    _ ≤ u * (A * eps ^ 2) * r ^ 2 + v * b ^ 2 * ((A + C * A ^ 3) * eps ^ 6) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM hu) (sq_nonneg r))
        (mul_le_mul_of_nonneg_left hsum (mul_nonneg hv (sq_nonneg b)))
    _ = _ := by ring

end PGM
