import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Polynomial factors paid by a fixed exponential weight -/

set_option autoImplicit false

noncomputable section

namespace Real

theorem pow_mul_exp_le_exp_weight {theta eta x : ℝ} (hgap : eta < theta)
    (hx : 0 ≤ x) (k : ℕ) :
    x ^ k * exp (eta * x) ≤
      ((k.factorial : ℝ) / (theta - eta) ^ k) * exp (theta * x) := by
  have hr : 0 < theta - eta := by linarith
  have hf : 0 < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  have ht := pow_div_factorial_le_exp ((theta - eta) * x) (mul_nonneg hr.le hx) k
  have hp : x ^ k ≤ ((k.factorial : ℝ) / (theta - eta) ^ k) * exp ((theta - eta) * x) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (pow_pos hr k)).mpr
    calc
      _ = ((theta - eta) * x) ^ k := by rw [mul_pow]; ring
      _ ≤ exp ((theta - eta) * x) * (k.factorial : ℝ) := (div_le_iff₀ hf).mp ht
      _ = _ := by ring
  calc
    _ ≤ (((k.factorial : ℝ) / (theta - eta) ^ k) * exp ((theta - eta) * x)) * exp (eta * x) :=
      mul_le_mul_of_nonneg_right hp (exp_pos _).le
    _ = _ := by
      rw [mul_assoc, ← exp_add, show (theta - eta) * x + eta * x = theta * x by ring]

end Real

namespace MeasureTheory

open Set

theorem integrableOn_pow_exp_mul_of_exp_weight {g : ℝ → ℝ} {theta eta : ℝ}
    (hg : Measurable g) (hgap : eta < theta)
    (hi : Integrable (fun x => Real.exp (theta * x) * g x) volume) (k : ℕ) :
    IntegrableOn (fun x => x ^ k * Real.exp (eta * x) * g x) (Ioi (0 : ℝ)) volume ∧
    (∫ x in Ioi (0 : ℝ), |x ^ k * Real.exp (eta * x) * g x|) ≤
      ((k.factorial : ℝ) / (theta - eta) ^ k) *
        (∫ x, Real.exp (theta * x) * |g x|) := by
  let C := (k.factorial : ℝ) / (theta - eta) ^ k
  have hr : 0 < theta - eta := by linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hiabs : Integrable (fun x => Real.exp (theta * x) * |g x|) volume := by
    simpa only [abs_mul, abs_of_pos (Real.exp_pos _)] using hi.abs
  have hb (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) :
      |x ^ k * Real.exp (eta * x) * g x| ≤ C * (Real.exp (theta * x) * |g x|) := by
    rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_pow, abs_of_pos hx]
    exact (mul_le_mul_of_nonneg_right (Real.pow_mul_exp_le_exp_weight hgap hx.le k)
      (abs_nonneg _)).trans_eq (by dsimp [C]; ring)
  have hiF : IntegrableOn (fun x => x ^ k * Real.exp (eta * x) * g x) (Ioi (0 : ℝ)) volume := by
    apply (hiabs.const_mul C).integrableOn.mono' (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simpa only [Real.norm_eq_abs] using hb x hx
  refine ⟨hiF, ?_⟩
  calc
    _ ≤ ∫ x in Ioi (0 : ℝ), C * (Real.exp (theta * x) * |g x|) :=
      setIntegral_mono_on hiF.abs (hiabs.const_mul C).integrableOn measurableSet_Ioi hb
    _ ≤ ∫ x, C * (Real.exp (theta * x) * |g x|) :=
      setIntegral_le_integral (hiabs.const_mul C) (ae_of_all _ fun _ => by positivity)
    _ = _ := integral_const_mul _ _

end MeasureTheory
