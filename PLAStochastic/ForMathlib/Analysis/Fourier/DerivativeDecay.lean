import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Fourier decay from a chain of integrable derivatives

If `F 0, F 1, …, F k` are integrable functions on `ℝ` with `F (j+1)` the everywhere
derivative of `F j`, then for every real `β`,
`|β|^k |∫ e^{iβx} F 0(x) dx| ≤ ∫ |F k|` (`abs_pow_mul_norm_integral_exp_le`).
This is `k` integrations by parts on the whole line; there are no boundary terms. The
proof applies Mathlib's `Real.fourier_deriv` at the frequency `-β/(2π)`.
-/

noncomputable section

open MeasureTheory Complex Real FourierTransform

namespace PGM

/-- **Repeated integration by parts** against `e^{iβx}` along a chain of derivatives. -/
theorem abs_pow_mul_norm_integral_exp_le {k : ℕ} {F : ℕ → ℝ → ℝ}
    (hd : ∀ j < k, ∀ x, HasDerivAt (F j) (F (j + 1) x) x)
    (hi : ∀ j ≤ k, Integrable (F j)) (β : ℝ) :
    |β| ^ k * ‖∫ x : ℝ, Complex.exp (↑(β * x) * I) * (F 0 x : ℂ)‖ ≤ ∫ x, |F k x| := by
  set w : ℝ := -β / (2 * π) with hw
  set G : ℕ → ℝ → ℂ := fun j x => (F j x : ℂ) with hG
  have hGi : ∀ j ≤ k, Integrable (G j) := fun j hj => (hi j hj).ofReal
  have hGd : ∀ j < k, ∀ x, HasDerivAt (G j) (G (j + 1) x) x := fun j hj x =>
    (hd j hj x).ofReal_comp
  have hderiv : ∀ j < k, deriv (G j) = G (j + 1) := fun j hj => funext fun x =>
    (hGd j hj x).deriv
  have hrec : ∀ j ≤ k, 𝓕 (G j) w = ((2 * π * I * w) ^ j : ℂ) * 𝓕 (G 0) w := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have hjk : j < k := by omega
      have h := Real.fourier_deriv (hGi j hjk.le) (fun x => (hGd j hjk x).differentiableAt)
        (by rw [hderiv j hjk]; exact hGi (j + 1) hj)
      rw [hderiv j hjk] at h
      rw [h]
      simp only [smul_eq_mul]
      rw [ih hjk.le, pow_succ]
      ring
  have hnorm : ‖𝓕 (G k) w‖ ≤ ∫ x, |F k x| := by
    rw [Real.fourier_real_eq]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [G, Circle.norm_smul]
  have h0 : 𝓕 (G 0) w = ∫ x : ℝ, Complex.exp (↑(β * x) * I) * (F 0 x : ℂ) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [G, smul_eq_mul]
    congr 3
    rw [hw]
    field_simp
  have hc : ‖((2 * π * I * w) ^ k : ℂ)‖ = |β| ^ k := by
    rw [norm_pow]
    congr 1
    rw [hw]
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_div, abs_neg, abs_mul, abs_two, abs_of_pos Real.pi_pos]
    field_simp
  calc |β| ^ k * ‖∫ x : ℝ, Complex.exp (↑(β * x) * I) * (F 0 x : ℂ)‖
      = ‖((2 * π * I * w) ^ k : ℂ) * 𝓕 (G 0) w‖ := by rw [norm_mul, hc, h0]
    _ = ‖𝓕 (G k) w‖ := by rw [hrec k le_rfl]
    _ ≤ ∫ x, |F k x| := hnorm

end PGM
