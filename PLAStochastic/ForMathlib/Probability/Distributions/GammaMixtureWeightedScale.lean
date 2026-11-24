import PLAStochastic.ForMathlib.Probability.Distributions.GammaMixtureWeighted
import PLAStochastic.ForMathlib.Probability.Distributions.GammaMixtureScale

/-! # Fixed exponential derivative budgets after physical Gamma normalisation -/

set_option autoImplicit false

namespace ProbabilityTheory

noncomputable section

open MeasureTheory

theorem exp_mul_scaled_eq (h : ℝ → ℝ) (C theta : ℝ) {m : ℝ} (hm : 0 < m) (x : ℝ) :
    Real.exp (theta * x) * (C * h (m * x)) =
      C * (Real.exp (theta / m * (m * x)) * h (m * x)) := by
  rw [show theta / m * (m * x) = theta * x by field_simp]
  ring

theorem integrable_exp_mul_scaled (h : ℝ → ℝ) (C theta : ℝ) {m : ℝ} (hm : 0 < m)
    (hi : Integrable (fun y => Real.exp (theta / m * y) * h y) volume) :
    Integrable (fun x => Real.exp (theta * x) * (C * h (m * x))) volume := by
  simp_rw [exp_mul_scaled_eq h C theta hm]
  exact (hi.comp_mul_left' hm.ne').const_mul C

theorem integral_exp_mul_scaled (h : ℝ → ℝ) (C theta : ℝ) {m : ℝ} (hm : 0 < m) :
    (∫ x, Real.exp (theta * x) * (C * h (m * x))) =
      C / m * (∫ y, Real.exp (theta / m * y) * h y) := by
  simp_rw [exp_mul_scaled_eq h C theta hm]
  rw [integral_const_mul, Measure.integral_comp_mul_left
    (fun y => Real.exp (theta / m * y) * h y) m, smul_eq_mul, abs_inv, abs_of_pos hm]
  ring

theorem gammaScaled_exponential_raw {p : ℕ → ℝ} {theta m : ℝ} (hm : 0 < m)
    (hi : Integrable (fun x => Real.exp (theta * x) * gammaScaledMixture p m x) volume) :
    Integrable (fun y => Real.exp (theta / m * y) * gammaMixtureDensity p 3 y) volume := by
  simp_rw [gammaScaledMixture, exp_mul_scaled_eq (gammaMixtureDensity p 3) m theta hm] at hi
  have h := hi.div_const m
  simp only [mul_div_cancel_left₀ _ hm.ne'] at h
  exact (integrable_comp_mul_left_iff _ hm.ne').mp h

theorem integral_exp_mul_gammaScaledMixture (p : ℕ → ℝ) (theta : ℝ) {m : ℝ} (hm : 0 < m) :
    (∫ x, Real.exp (theta * x) * gammaScaledMixture p m x) =
      ∫ y, Real.exp (theta / m * y) * gammaMixtureDensity p 3 y := by
  simp only [gammaScaledMixture]
  rw [integral_exp_mul_scaled _ m theta hm, div_self hm.ne', one_mul]

set_option backward.isDefEq.respectTransparency.types false in
theorem gammaScaled_weighted_derivatives {p : ℕ → ℝ} (hp0 : ∀ n, 0 ≤ p n) (hp : Summable p)
    {theta m : ℝ} (hm : 0 < m) (htheta : 0 ≤ theta) (htm : theta < m)
    (hi : Integrable (fun x => Real.exp (theta * x) * gammaScaledMixture p m x) volume) :
    Integrable (fun x => Real.exp (theta * x) * gammaScaledFirst p m x) volume ∧
      Integrable (fun x => Real.exp (theta * x) * gammaScaledSecond p m x) volume ∧
      (∫ x, Real.exp (theta * x) * |gammaScaledFirst p m x|) ≤
        2 * m * (∫ x, Real.exp (theta * x) * gammaScaledMixture p m x) ∧
      (∫ x, Real.exp (theta * x) * |gammaScaledSecond p m x|) ≤
        4 * m ^ 2 * (∫ x, Real.exp (theta * x) * gammaScaledMixture p m x) := by
  have ht0 : 0 ≤ theta / m := div_nonneg htheta hm.le
  have ht1 : theta / m < 1 := (div_lt_one hm).mpr htm
  obtain ⟨hfirst, hsecond, hF, hS⟩ := gammaMixture_weighted_derivatives hp0 hp ht0 ht1
    (gammaScaled_exponential_raw hm hi)
  refine ⟨integrable_exp_mul_scaled _ (m ^ 2) theta hm hfirst,
    integrable_exp_mul_scaled _ (m ^ 3) theta hm hsecond, ?_, ?_⟩
  · have he : (∫ x, Real.exp (theta * x) * |gammaScaledFirst p m x|) =
        m * (∫ y, Real.exp (theta / m * y) * |gammaMixtureFirst p y|) := by
      simp only [gammaScaledFirst, abs_mul, abs_pow, abs_of_pos hm]
      rw [integral_exp_mul_scaled (fun y => |gammaMixtureFirst p y|) (m ^ 2) theta hm]
      field_simp
    rw [he, integral_exp_mul_gammaScaledMixture p theta hm]
    nlinarith [mul_le_mul_of_nonneg_left hF hm.le]
  · have he : (∫ x, Real.exp (theta * x) * |gammaScaledSecond p m x|) =
        m ^ 2 * (∫ y, Real.exp (theta / m * y) * |gammaMixtureSecond p y|) := by
      simp only [gammaScaledSecond, abs_mul, abs_pow, abs_of_pos hm]
      rw [integral_exp_mul_scaled (fun y => |gammaMixtureSecond p y|) (m ^ 3) theta hm]
      field_simp
    rw [he, integral_exp_mul_gammaScaledMixture p theta hm]
    nlinarith [mul_le_mul_of_nonneg_left hS (sq_nonneg m)]

end

end ProbabilityTheory
