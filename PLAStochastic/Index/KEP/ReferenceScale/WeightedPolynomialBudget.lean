import PLAStochastic.Index.KEP.ReferenceScale.SurvivingCoreBudget

/-!
# Polynomial factors consume a fixed part of an exponential weight

This pays the physical coordinate factors in the first two Mellin insertions.
The estimate is linear in the weighted input norm and does not require a
pointwise derivative envelope.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory Set

theorem kep_polynomial_weight_le {alpha beta x : ℝ} (hab : alpha < beta)
    (hx : 0 ≤ x) (p : ℕ) :
    Real.exp (alpha * x) * x ^ p ≤
      ((p.factorial : ℝ) / (beta - alpha) ^ p) * Real.exp (beta * x) := by
  have hd : 0 < beta - alpha := by linarith
  have hf : 0 < (p.factorial : ℝ) := by exact_mod_cast p.factorial_pos
  have ht := Real.pow_div_factorial_le_exp ((beta - alpha) * x) (by positivity) p
  have hb := (div_le_iff₀ hf).mp ht
  calc
    _ = ((beta - alpha) * x) ^ p * Real.exp (alpha * x) / (beta - alpha) ^ p := by
      rw [mul_pow]
      field_simp
    _ ≤ ((p.factorial : ℝ) * Real.exp ((beta - alpha) * x)) *
        Real.exp (alpha * x) / (beta - alpha) ^ p := by
      gcongr
      simpa only [mul_comm] using hb
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add, show (beta - alpha) * x + alpha * x = beta * x by ring]
      ring

theorem kep_weighted_polynomial_budget {F : ℝ → ℝ} (hF : Measurable F)
    (hz : ∀ x ≤ 0, F x = 0) {alpha beta : ℝ} (hab : alpha < beta) (p : ℕ)
    (hi : Integrable (fun x => Real.exp (beta * x) * F x) volume) :
    Integrable (fun x => Real.exp (alpha * x) * x ^ p * F x) volume ∧
      (∫ x, Real.exp (alpha * x) * |x ^ p * F x|) ≤
        ((p.factorial : ℝ) / (beta - alpha) ^ p) *
          ∫ x, Real.exp (beta * x) * |F x| := by
  let C := (p.factorial : ℝ) / (beta - alpha) ^ p
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb (x : ℝ) : |Real.exp (alpha * x) * x ^ p * F x| ≤
      C * |Real.exp (beta * x) * F x| := by
    by_cases hx : 0 ≤ x
    · simp only [abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg (pow_nonneg hx p)]
      exact (mul_le_mul_of_nonneg_right (kep_polynomial_weight_le hab hx p) (abs_nonneg _)).trans_eq
        (by dsimp [C]; ring)
    · rw [hz x (by linarith), mul_zero, mul_zero, abs_zero, mul_zero]
  have hs : AEStronglyMeasurable (fun x => Real.exp (alpha * x) * x ^ p * F x) volume := by
    exact ((Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
      (measurable_id.pow_const p) |>.mul hF).aestronglyMeasurable
  have hi' : Integrable (fun x => Real.exp (alpha * x) * x ^ p * F x) volume :=
    ((hi.norm).const_mul C).mono' hs (ae_of_all _ fun x => by
      simpa only [Real.norm_eq_abs] using hb x)
  refine ⟨hi', ?_⟩
  have hh := integral_mono hi'.norm ((hi.norm).const_mul C) (fun x => by
    simpa only [Real.norm_eq_abs] using hb x)
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), integral_const_mul,
    mul_assoc] using hh

end

end PGM
