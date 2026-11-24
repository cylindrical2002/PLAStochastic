import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Quantitative polynomially weighted exponential series

The constants below depend on the polynomial degree, while the inverse decay
rate is explicit. In particular a rate of order `w⁻²` costs only a polynomial
in `w`, rather than an unspecified summability constant.
-/

set_option autoImplicit false

noncomputable section

namespace Real

/-- An exponential geometric series has an explicit inverse-rate budget. -/
theorem tsum_exp_neg_nat_mul_le {r : ℝ} (hr : 0 < r) :
    (∑' k : ℕ, exp (-r * k)) ≤ 1 + 1 / r := by
  have hq0 : 0 ≤ exp (-r) := (exp_pos _).le
  have hq1 : exp (-r) < 1 := exp_lt_one_iff.mpr (by linarith)
  have hseries : (∑' k : ℕ, exp (-r * k)) = (1 - exp (-r))⁻¹ := by
    simp_rw [mul_comm (-r), exp_nat_mul]
    exact tsum_geometric_of_norm_lt_one (by simpa [abs_of_nonneg hq0] using hq1)
  rw [hseries]
  have he : 1 + r ≤ exp r := by simpa only [add_comm] using add_one_le_exp r
  have hprod : r ≤ (1 + r) * (1 - exp (-r)) := by
    have h := mul_le_mul_of_nonneg_right he hq0
    rw [← exp_add] at h
    simp only [add_neg_cancel, exp_zero] at h
    nlinarith
  have hd : 0 < 1 - exp (-r) := by linarith
  rw [← one_div]
  apply (div_le_iff₀ hd).mpr
  have heq : (1 + 1 / r) * (1 - exp (-r)) =
      ((1 + r) * (1 - exp (-r))) / r := by field_simp; ring
  rw [heq]
  exact (le_div_iff₀ hr).mpr (by simpa using hprod)

/-- Pointwise payment of a polynomial by half of the exponential decay. -/
theorem polynomial_mul_exp_neg_le {r : ℝ} (hr : 0 < r) (p k : ℕ) :
    (k + 1 : ℝ) ^ p * exp (-r * k) ≤
      ((p.factorial : ℝ) * exp 1 * (1 + 2 / r) ^ p) * exp (-(r / 2) * k) := by
  let t : ℝ := r / 2 * k + 1
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hf : 0 < (p.factorial : ℝ) := by exact_mod_cast p.factorial_pos
  have hb : (k + 1 : ℝ) ≤ (1 + 2 / r) * t := by
    dsimp [t]
    have heq : (1 + 2 / r) * (r / 2 * (k : ℝ) + 1) =
        (k + 1 : ℝ) + r / 2 * k + 2 / r := by field_simp; ring
    rw [heq]
    have h1 : 0 ≤ r / 2 * (k : ℝ) := by positivity
    have h2 : 0 ≤ 2 / r := by positivity
    linarith
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ (k + 1 : ℝ)) hb p
  rw [mul_pow] at hp
  have htaylor : t ^ p ≤ (p.factorial : ℝ) * exp t := by
    have h := pow_div_factorial_le_exp t ht p
    simpa only [mul_comm] using (div_le_iff₀ hf).mp h
  calc
    _ ≤ ((1 + 2 / r) ^ p * t ^ p) * exp (-r * k) :=
      mul_le_mul_of_nonneg_right hp (exp_pos _).le
    _ ≤ ((1 + 2 / r) ^ p * ((p.factorial : ℝ) * exp t)) * exp (-r * k) := by
      gcongr
    _ = _ := by
      dsimp [t]
      rw [show r / 2 * (k : ℝ) + 1 = 1 + r / 2 * k by ring, exp_add]
      rw [show -(r / 2) * (k : ℝ) = r / 2 * k + (-r * k) by ring, exp_add]
      ring

/-- The full series costs at most one extra power of the inverse rate. -/
theorem tsum_polynomial_mul_exp_neg_le {r : ℝ} (hr : 0 < r) (p : ℕ) :
    (∑' k : ℕ, (k + 1 : ℝ) ^ p * exp (-r * k)) ≤
      (p.factorial : ℝ) * exp 1 * (1 + 2 / r) ^ (p + 1) := by
  let C := (p.factorial : ℝ) * exp 1 * (1 + 2 / r) ^ p
  have hs := (summable_nat_add_iff 1).2 (summable_pow_mul_exp_neg_nat_mul p hr)
  have hs' : Summable (fun k : ℕ => (k + 1 : ℝ) ^ p * exp (-r * k)) := by
    convert hs.mul_left (exp r) using 1 <;> first
    | rfl
    | (funext k
       rw [Nat.cast_add, Nat.cast_one, mul_left_comm, ← exp_add]
       congr 2
       ring)
  have hg : Summable (fun k : ℕ => exp (-(r / 2) * k)) := by
    simp_rw [mul_comm (-(r / 2)), exp_nat_mul]
    exact summable_geometric_of_norm_lt_one (by
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      exact exp_lt_one_iff.mpr (by linarith))
  calc
    _ ≤ ∑' k : ℕ, C * exp (-(r / 2) * k) :=
      hs'.tsum_le_tsum (polynomial_mul_exp_neg_le hr p) (hg.mul_left C)
    _ = C * ∑' k : ℕ, exp (-(r / 2) * k) := tsum_mul_left
    _ ≤ C * (1 + 1 / (r / 2)) :=
      mul_le_mul_of_nonneg_left (tsum_exp_neg_nat_mul_le (by linarith)) (by
        dsimp [C]; positivity)
    _ = _ := by dsimp [C]; rw [pow_succ]; ring

end Real
