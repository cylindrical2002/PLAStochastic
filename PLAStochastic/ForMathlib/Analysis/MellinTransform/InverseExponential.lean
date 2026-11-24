import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Mellin transforms of the inverse exponential `exp (-c / t)`

For `c > 0` and `re q < 0`, the substitution `t = c / u` turns the Mellin
integral of `t ↦ exp (-c / t)` into Euler's Gamma integral:

  `∫ t in Ioi 0, t ^ (q - 1) * exp (-c / t) = c ^ q * Γ (-q)`.

We record integrability and the value, the shifted version with `t ^ q`,
and the real-exponent versions used for absolute bounds.
-/
noncomputable section
open MeasureTheory Set Complex
namespace BrownianAffine

private theorem mellinConvergent_exp_neg {q : ℂ} (hq : 0 < q.re) :
    MellinConvergent (fun x : ℝ => ((Real.exp (-x) : ℝ) : ℂ)) q := by
  refine (Complex.GammaIntegral_convergent hq).congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [smul_eq_mul]
  ring

private theorem exp_neg_div_eq (c t : ℝ) :
    ((Real.exp (-c / t) : ℝ) : ℂ) = ((Real.exp (-(c * t⁻¹)) : ℝ) : ℂ) := by
  rw [neg_div, div_eq_mul_inv]

theorem integrableOn_cpow_mul_exp_neg_div {q : ℂ} (hq : q.re < 0) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (q - 1) * ((Real.exp (-c / t) : ℝ) : ℂ)) (Ioi 0) := by
  have h0 : MellinConvergent (fun x : ℝ => ((Real.exp (-x) : ℝ) : ℂ)) (-q) :=
    mellinConvergent_exp_neg (by simpa using hq)
  have h1 : MellinConvergent (fun x : ℝ => ((Real.exp (-(c * x)) : ℝ) : ℂ)) (-q) :=
    (MellinConvergent.comp_mul_left (f := fun x : ℝ => ((Real.exp (-x) : ℝ) : ℂ)) hc).mpr h0
  have h2 := (MellinConvergent.comp_rpow
    (f := fun x : ℝ => ((Real.exp (-(c * x)) : ℝ) : ℂ)) (s := q) (a := -1)
    (by norm_num)).mpr (by rw [ofReal_neg, ofReal_one, div_neg, div_one]; exact h1)
  refine h2.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [smul_eq_mul, Real.rpow_neg_one, exp_neg_div_eq]

theorem integral_cpow_mul_exp_neg_div {q : ℂ} (hq : q.re < 0) {c : ℝ} (hc : 0 < c) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (q - 1) * ((Real.exp (-c / t) : ℝ) : ℂ) =
      (c : ℂ) ^ q * Gamma (-q) := by
  have h := mellin_comp_inv (fun x : ℝ => ((Real.exp (-(c * x)) : ℝ) : ℂ)) q
  have h' := mellin_comp_mul_left (fun x : ℝ => ((Real.exp (-x) : ℝ) : ℂ)) (-q) hc
  rw [← Complex.GammaIntegral_eq_mellin, ← Complex.Gamma_eq_integral (by simpa using hq),
    neg_neg, smul_eq_mul] at h'
  rw [h'] at h
  rw [← h, mellin]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  simp only [smul_eq_mul, exp_neg_div_eq]

/-- The shifted form `t ^ q = t ^ ((q + 1) - 1)`. -/
theorem integrableOn_cpow_mul_exp_neg_div_succ {q : ℂ} (hq : q.re < -1) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ q * ((Real.exp (-c / t) : ℝ) : ℂ)) (Ioi 0) := by
  have h := integrableOn_cpow_mul_exp_neg_div (q := q + 1) (by simp; linarith) hc
  simpa only [add_sub_cancel_right] using h

theorem integral_cpow_mul_exp_neg_div_succ {q : ℂ} (hq : q.re < -1) {c : ℝ} (hc : 0 < c) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ q * ((Real.exp (-c / t) : ℝ) : ℂ) =
      (c : ℂ) ^ (q + 1) * Gamma (-(q + 1)) := by
  have h := integral_cpow_mul_exp_neg_div (q := q + 1) (by simp; linarith) hc
  simpa only [add_sub_cancel_right] using h

theorem norm_cpow_mul_exp_neg_div {q : ℂ} {c t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ (q - 1) * ((Real.exp (-c / t) : ℝ) : ℂ)‖ =
      t ^ (q.re - 1) * Real.exp (-c / t) := by
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  simp

/-- Real-exponent integrability, used for absolute bounds. -/
theorem integrableOn_rpow_mul_exp_neg_div {σ : ℝ} (hσ : σ < 0) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t ^ (σ - 1) * Real.exp (-c / t)) (Ioi 0) := by
  have h := (integrableOn_cpow_mul_exp_neg_div (q := (σ : ℂ)) (by simpa using hσ) hc).norm
  refine IntegrableOn.congr_fun (μ := volume) h (fun t ht => ?_) measurableSet_Ioi
  simp only [norm_cpow_mul_exp_neg_div (q := (σ : ℂ)) (c := c) ht, ofReal_re]

theorem integral_rpow_mul_exp_neg_div {σ : ℝ} (hσ : σ < 0) {c : ℝ} (hc : 0 < c) :
    ∫ t in Ioi (0 : ℝ), t ^ (σ - 1) * Real.exp (-c / t) = c ^ σ * Real.Gamma (-σ) := by
  have h := integral_cpow_mul_exp_neg_div (q := (σ : ℂ)) (by simpa using hσ) hc
  have hl : ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ ((σ : ℂ) - 1) * ((Real.exp (-c / t) : ℝ) : ℂ) =
      ((∫ t in Ioi (0 : ℝ), t ^ (σ - 1) * Real.exp (-c / t) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    simp only [ofReal_mul, ofReal_cpow (le_of_lt ht), ofReal_sub, ofReal_one]
  have hr : (c : ℂ) ^ (σ : ℂ) * Gamma (-(σ : ℂ)) = ((c ^ σ * Real.Gamma (-σ) : ℝ) : ℂ) := by
    rw [ofReal_mul, ofReal_cpow hc.le, ← Complex.Gamma_ofReal, ofReal_neg]
  rw [hl, hr] at h
  exact_mod_cast h

theorem integrableOn_rpow_mul_exp_neg_div_succ {σ : ℝ} (hσ : σ < -1) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t ^ σ * Real.exp (-c / t)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_div (σ := σ + 1) (by linarith) hc
  simpa only [add_sub_cancel_right] using h

theorem integral_rpow_mul_exp_neg_div_succ {σ : ℝ} (hσ : σ < -1) {c : ℝ} (hc : 0 < c) :
    ∫ t in Ioi (0 : ℝ), t ^ σ * Real.exp (-c / t) = c ^ (σ + 1) * Real.Gamma (-(σ + 1)) := by
  have h := integral_rpow_mul_exp_neg_div (σ := σ + 1) (by linarith) hc
  simpa only [add_sub_cancel_right] using h

end BrownianAffine
