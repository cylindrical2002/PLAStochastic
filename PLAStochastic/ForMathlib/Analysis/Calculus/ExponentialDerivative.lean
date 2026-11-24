import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Exponential derivative decay from a polynomial second-derivative bound -/

noncomputable section
open Set
open scoped ContDiff

namespace Real

theorem pow_le_factorial_inv_mul_exp (k : ℕ) {q t : ℝ} (hq : 0 < q) (ht : 0 ≤ t) :
    t ^ k ≤ (k.factorial : ℝ) / q ^ k * exp (q * t) := by
  have hfac : 0 < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have h := pow_div_factorial_le_exp (q * t) (mul_nonneg hq.le ht) k
  have h' := (div_le_iff₀ hfac).mp h
  rw [mul_pow] at h'
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (pow_pos hq k)).mpr
  convert! h' using 1 <;> field_simp

/-- A short secant and the mean value theorem control the derivative at its left endpoint. -/
theorem abs_deriv_le_secant_add_second_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    {B t δ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ)
    (hb : ∀ x ∈ Icc t (t + δ), |iteratedDeriv 2 f x| ≤ B) :
    |deriv f t| ≤ (|f (t + δ)| + |f t|) / δ + B * δ := by
  have hd := (contDiff_infty_iff_deriv.mp hf).1
  have hf' := (contDiff_infty_iff_deriv.mp hf).2
  have hd' := (contDiff_infty_iff_deriv.mp hf').1
  obtain ⟨y, hy, he⟩ := exists_deriv_eq_slope f (by linarith : t < t + δ)
    hf.continuous.continuousOn hd.differentiableOn
  have hlip : |deriv f y - deriv f t| ≤ B * (y - t) := by
    have h := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := deriv f) (f' := deriv (deriv f))
      (C := B)
      (fun x _ => (hd' x).hasDerivAt.hasDerivWithinAt)
      (fun x hx => ?_) y ⟨hy.1.le, hy.2.le⟩
    · simpa only [Real.norm_eq_abs] using h
    · simpa only [iteratedDeriv_succ, iteratedDeriv_zero, Real.norm_eq_abs] using hb x ⟨hx.1, hx.2.le⟩
  have hsec : |deriv f y| ≤ (|f (t + δ)| + |f t|) / δ := by
    rw [he, add_sub_cancel_left, abs_div, abs_of_pos hδ]
    exact div_le_div_of_nonneg_right (abs_sub _ _) hδ.le
  calc
    _ = |deriv f y - (deriv f y - deriv f t)| := by congr 1; ring
    _ ≤ |deriv f y| + |deriv f y - deriv f t| := abs_sub _ _
    _ ≤ (|f (t + δ)| + |f t|) / δ + B * (y - t) := add_le_add hsec hlip
    _ ≤ _ := by gcongr; linarith [hy.2]

/-- A polynomial growth estimate costs only a reduction of the exponential rate. -/
theorem exists_exponential_deriv_bound_of_polynomial_second_deriv
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {A B ρ : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hρ : 0 < ρ)
    (ha : ∀ t : ℝ, 1 ≤ t → |f t| ≤ A * exp (-ρ * t))
    (hb : ∀ t : ℝ, 1 ≤ t → |iteratedDeriv 2 f t| ≤ B * t ^ 3) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t : ℝ, 1 ≤ t → |deriv f t| ≤ D * exp (-(ρ / 4) * t) := by
  let P : ℝ := ((3 : ℕ).factorial : ℝ) / (ρ / 4) ^ 3
  refine ⟨2 * A + 8 * B * P, by dsimp [P]; positivity, fun t ht => ?_⟩
  let δ : ℝ := exp (-ρ * t / 2)
  have hδ : 0 < δ := exp_pos _
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hδ1 : δ ≤ 1 := exp_le_one_iff.mpr (by nlinarith)
  have hsecond : ∀ x ∈ Icc t (t + δ), |iteratedDeriv 2 f x| ≤ 8 * B * t ^ 3 := by
    intro x hx
    have hx1 : 1 ≤ x := ht.trans hx.1
    have hx2 : x ≤ 2 * t := by linarith [hx.2]
    calc
      _ ≤ B * x ^ 3 := hb x hx1
      _ ≤ B * (2 * t) ^ 3 := by gcongr
      _ = _ := by ring
  have hs := abs_deriv_le_secant_add_second_deriv hf (by positivity : 0 ≤ 8 * B * t ^ 3) hδ hsecond
  have he : exp (-ρ * (t + δ)) ≤ exp (-ρ * t) := by
    apply exp_le_exp.mpr
    nlinarith
  have hfδ : |f (t + δ)| ≤ A * exp (-ρ * t) :=
    (ha (t + δ) (by linarith)).trans (mul_le_mul_of_nonneg_left he hA)
  have hfirst : (|f (t + δ)| + |f t|) / δ ≤ 2 * A * exp (-(ρ / 4) * t) := by
    calc
      _ ≤ (2 * A * exp (-ρ * t)) / δ := by
        apply div_le_div_of_nonneg_right _ hδ.le
        linarith [ha t ht]
      _ = 2 * A * exp (-ρ * t / 2) := by
        dsimp only [δ]
        rw [mul_div_assoc, ← exp_sub]
        congr 2
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply exp_le_exp.mpr
        nlinarith
  have hp : t ^ 3 ≤ P * exp ((ρ / 4) * t) := pow_le_factorial_inv_mul_exp 3 (by positivity) ht0.le
  have hlast : 8 * B * t ^ 3 * δ ≤ 8 * B * P * exp (-(ρ / 4) * t) := by
    calc
      _ ≤ 8 * B * (P * exp ((ρ / 4) * t)) * δ := by gcongr
      _ = _ := by
        dsimp only [δ]
        have heq : exp ((ρ / 4) * t) * exp (-ρ * t / 2) = exp (-(ρ / 4) * t) := by
          rw [← exp_add]
          congr 1
          ring
        calc
          _ = 8 * B * P * (exp ((ρ / 4) * t) * exp (-ρ * t / 2)) := by ring
          _ = _ := by rw [heq]
  calc
    _ ≤ (|f (t + δ)| + |f t|) / δ + 8 * B * t ^ 3 * δ := hs
    _ ≤ 2 * A * exp (-(ρ / 4) * t) + 8 * B * P * exp (-(ρ / 4) * t) := add_le_add hfirst hlast
    _ = _ := by ring

end Real
