import PLAStochastic.ForMathlib.Probability.Distributions.GammaDerivative

/-! # Exponential moments of the actual integer Gamma density -/

set_option autoImplicit false

namespace ProbabilityTheory

noncomputable section

open MeasureTheory Set

theorem integrable_gammaPDFReal {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    Integrable (gammaPDFReal a r) volume := by
  refine ⟨(measurable_gammaPDFReal _ _).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (gammaPDFReal_nonneg ha hr))]
  change (∫⁻ x, gammaPDF a r x) < ⊤
  rw [lintegral_gammaPDF_eq_one ha hr]
  exact ENNReal.one_lt_top

theorem integral_gammaPDFReal {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    (∫ x, gammaPDFReal a r x) = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (gammaPDFReal_nonneg ha hr))
    (measurable_gammaPDFReal _ _).aestronglyMeasurable]
  change (∫⁻ x, gammaPDF a r x).toReal = 1
  rw [lintegral_gammaPDF_eq_one ha hr, ENNReal.toReal_one]

theorem exp_mul_gammaNatDensity_eq (n : ℕ) {lam : ℝ} (hlam : lam < 1) (x : ℝ) :
    Real.exp (lam * x) * gammaNatDensity n x =
      gammaPDFReal ((n + 1 : ℕ) : ℝ) (1 - lam) x / (1 - lam) ^ (n + 1) := by
  have hr : 0 < 1 - lam := by linarith
  rcases lt_or_ge x 0 with hx | hx
  · rw [gammaNatDensity_of_neg n hx]
    simp only [gammaPDFReal, if_neg (not_le.mpr hx), zero_div, mul_zero]
  · rw [gammaNatDensity_of_nonneg n hx]
    unfold gammaPDFReal
    rw [if_pos hx]
    push_cast
    rw [Real.Gamma_nat_eq_factorial, add_sub_cancel_right, Real.rpow_natCast]
    rw [show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by simp, Real.rpow_natCast]
    have he : Real.exp (lam * x) * Real.exp (-x) = Real.exp (-((1 - lam) * x)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← he]
    field_simp

theorem integrable_exp_mul_gammaNatDensity (n : ℕ) {lam : ℝ} (hlam : lam < 1) :
    Integrable (fun x => Real.exp (lam * x) * gammaNatDensity n x) volume := by
  simp_rw [exp_mul_gammaNatDensity_eq n hlam]
  exact (integrable_gammaPDFReal (by positivity) (by linarith : 0 < 1 - lam)).div_const _

theorem integral_exp_mul_gammaNatDensity (n : ℕ) {lam : ℝ} (hlam : lam < 1) :
    (∫ x, Real.exp (lam * x) * gammaNatDensity n x) = 1 / (1 - lam) ^ (n + 1) := by
  simp_rw [exp_mul_gammaNatDensity_eq n hlam]
  rw [integral_div, integral_gammaPDFReal (by positivity) (by linarith : 0 < 1 - lam)]

theorem lintegral_exp_mul_gammaNatDensity (n : ℕ) {lam : ℝ} (hlam : lam < 1) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (lam * x) * gammaNatDensity n x)) =
      ENNReal.ofReal (1 / (1 - lam) ^ (n + 1)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_mul_gammaNatDensity n hlam)
    (ae_of_all _ (fun x => mul_nonneg (Real.exp_pos _).le (gammaNatDensity_nonneg _ _))),
    integral_exp_mul_gammaNatDensity n hlam]

end

end ProbabilityTheory
