import PLAStochastic.Affine.Moments.Optimal.AllOrders.ImageMellinModes
import Mathlib.Analysis.PSeries

/-! # Spectral form and absolute bounds for the image-mode Mellin integrals

For `re q < -1` and `m = n + 1`, the Mellin integral of the `n`-th image mode,
multiplied by `q`, equals

  `8 ^ q Γ (-q) / (3 (q + 1)) *
    (4 (2q + 1)(2q + 3) (P ^ (q + 1) - m ^ (2q + 2)) +
      4 q (2q + 1) (P ^ q - m ^ (2q)) + q (q - 1) P ^ (q - 1))`,

where `P = m (m + 1)`. We also bound the integral of the absolute integrand by a
constant times `m ^ (2 re q + 2)`, which is summable for `re q < -3/2`.
-/
noncomputable section
open MeasureTheory Set Complex Filter
namespace BrownianAffine

theorem imageIndex_ne_zero (n : ℕ) : (n : ℂ) + 1 ≠ 0 := by
  exact_mod_cast Nat.succ_ne_zero n

theorem imageIndex_add_one_ne_zero (n : ℕ) : (n : ℂ) + 1 + 1 ≠ 0 := by
  exact_mod_cast Nat.succ_ne_zero (n + 1)

theorem imageRateA_cpow (n : ℕ) (s : ℂ) :
    ((imageRateA n : ℝ) : ℂ) ^ s = 8 ^ s * ((n : ℂ) + 1) ^ (2 * s) := by
  have hx : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have hx' : ((((n : ℝ) + 1 : ℝ)) : ℂ) ≠ 0 := by
    push_cast
    exact imageIndex_ne_zero n
  unfold imageRateA
  rw [show 8 * ((n : ℝ) + 1) ^ 2 = 8 * (((n : ℝ) + 1) * ((n : ℝ) + 1)) by ring, ofReal_mul,
    mul_cpow_ofReal_nonneg (by norm_num) (mul_nonneg hx hx), ofReal_mul,
    mul_cpow_ofReal_nonneg hx hx, ← cpow_add _ _ hx', ← two_mul]
  push_cast
  rfl

theorem imageRateB_cpow (n : ℕ) (s : ℂ) :
    ((imageRateB n : ℝ) : ℂ) ^ s = 8 ^ s * ((((n + 1) * (n + 2) : ℕ) : ℂ)) ^ s := by
  have hcast : ((((n : ℝ) + 1) * ((n : ℝ) + 1 + 1) : ℝ) : ℂ) =
      ((((n + 1) * (n + 2) : ℕ) : ℂ)) := by
    push_cast
    ring
  unfold imageRateB
  rw [mul_assoc, ofReal_mul, mul_cpow_ofReal_nonneg (by norm_num) (by positivity), hcast]
  norm_num

/-- The Mellin integral of one image mode, in spectral form. -/
theorem mul_integral_mellin_optimalImageMode {q : ℂ} (hq : q.re < -1) (n : ℕ) :
    q * ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (q - 1) * ((optimalImageMode n t : ℝ) : ℂ) =
      8 ^ q * Gamma (-q) / (3 * (q + 1)) *
        (4 * (2 * q + 1) * (2 * q + 3) *
            ((((n + 1) * (n + 2) : ℕ) : ℂ) ^ (q + 1) - ((n : ℂ) + 1) ^ (2 * q + 2)) +
          4 * q * (2 * q + 1) *
            ((((n + 1) * (n + 2) : ℕ) : ℂ) ^ q - ((n : ℂ) + 1) ^ (2 * q)) +
          q * (q - 1) * (((n + 1) * (n + 2) : ℕ) : ℂ) ^ (q - 1)) := by
  have hq0 : q ≠ 0 := by
    rintro rfl
    simp at hq
    linarith
  have hq1 : q + 1 ≠ 0 := by
    intro h
    have h' : (q + 1).re = 0 := by rw [h]; simp
    simp at h'
    linarith
  have hM0 := imageIndex_ne_zero n
  have hM1 := imageIndex_add_one_ne_zero n
  have hP : ((((n + 1) * (n + 2) : ℕ) : ℂ)) = ((n : ℂ) + 1) * ((n : ℂ) + 1 + 1) := by
    push_cast
    ring
  have hP0 : ((((n + 1) * (n + 2) : ℕ) : ℂ)) ≠ 0 := by
    rw [hP]
    exact mul_ne_zero hM0 hM1
  have hA0 : ((imageRateA n : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (imageRateA_pos n).ne'
  have hB0 : ((imageRateB n : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (imageRateB_pos n).ne'
  have hA1 : ((imageRateA n : ℝ) : ℂ) ^ (q + 1) =
      ((imageRateA n : ℝ) : ℂ) ^ q * ((imageRateA n : ℝ) : ℂ) := by
    rw [cpow_add _ _ hA0, cpow_one]
  have hB1 : ((imageRateB n : ℝ) : ℂ) ^ (q + 1) =
      ((imageRateB n : ℝ) : ℂ) ^ q * ((imageRateB n : ℝ) : ℂ) := by
    rw [cpow_add _ _ hB0, cpow_one]
  have hAc : ((imageRateA n : ℝ) : ℂ) = 8 * ((n : ℂ) + 1) ^ 2 := by
    unfold imageRateA
    push_cast
    ring
  have hBc : ((imageRateB n : ℝ) : ℂ) = 8 * ((((n + 1) * (n + 2) : ℕ) : ℂ)) := by
    unfold imageRateB
    rw [hP]
    push_cast
    ring
  have hz1 : ((n : ℂ) + 1) ^ (2 * q + 2) = ((n : ℂ) + 1) ^ (2 * q) * ((n : ℂ) + 1) ^ 2 := by
    rw [cpow_add _ _ hM0, cpow_two]
  have hd1 : ((((n + 1) * (n + 2) : ℕ) : ℂ)) ^ (q + 1) =
      ((((n + 1) * (n + 2) : ℕ) : ℂ)) ^ (q - 1) * ((((n + 1) * (n + 2) : ℕ) : ℂ)) ^ 2 := by
    rw [show q + 1 = (q - 1) + 2 by ring, cpow_add _ _ hP0, cpow_two]
  have hd0 : ((((n + 1) * (n + 2) : ℕ) : ℂ)) ^ q =
      ((((n + 1) * (n + 2) : ℕ) : ℂ)) ^ (q - 1) * ((((n + 1) * (n + 2) : ℕ) : ℂ)) := by
    have h := cpow_add (q - 1) 1 hP0
    rw [sub_add_cancel, cpow_one] at h
    exact h
  have hΓ : Gamma (-q) = -(q + 1) * Gamma (-(q + 1)) := by
    have h := Complex.Gamma_add_one (-(q + 1)) (neg_ne_zero.mpr hq1)
    rw [show -(q + 1) + 1 = -q by ring] at h
    exact h
  rw [integral_mellin_optimalImageMode hq n]
  dsimp only
  rw [hA1, hB1, imageRateA_cpow, imageRateB_cpow, hAc, hBc, hz1, hd1, hd0, hΓ, hP]
  generalize (8 : ℂ) ^ q = E
  generalize ((n : ℂ) + 1) ^ (2 * q) = U
  generalize (((n : ℂ) + 1) * ((n : ℂ) + 1 + 1)) ^ (q - 1) = V
  generalize Gamma (-(q + 1)) = G
  generalize (n : ℂ) = N at hM0 hM1 ⊢
  field_simp
  ring

/-- A pointwise absolute bound for the Mellin integrand of one image mode. -/
theorem norm_mellin_optimalImageMode_le (q : ℂ) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ (q - 1) * ((optimalImageMode n t : ℝ) : ℂ)‖ ≤
      40 * ((n : ℝ) + 1) ^ 2 * (t ^ (q.re - 1) * Real.exp (-imageRateA n / t)) +
        4 * (t ^ q.re * Real.exp (-imageRateA n / t)) := by
  have hb := optimalImageMode_gaussian_bound n ht le_rfl
  have hexp : Real.exp (-8 * ((n : ℝ) + 1) ^ 2 / t) = Real.exp (-imageRateA n / t) := by
    unfold imageRateA
    ring_nf
  rw [hexp] at hb
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_real, sub_re, one_re]
  have hpow : t ^ q.re = t ^ (q.re - 1) * t := by
    rw [Real.rpow_sub_one ht.ne']
    field_simp
  rw [hpow]
  calc
    t ^ (q.re - 1) * ‖optimalImageMode n t‖ ≤
        t ^ (q.re - 1) * ((40 * ((n : ℝ) + 1) ^ 2 + 4 * t) * Real.exp (-imageRateA n / t)) :=
      mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg ht.le _)
    _ = _ := by ring

theorem imageRateA_rpow (n : ℕ) (σ : ℝ) :
    imageRateA n ^ σ = 8 ^ σ * ((n : ℝ) + 1) ^ (2 * σ) := by
  have hx : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  unfold imageRateA
  rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast_mul hx]
  norm_num

/-- The integral of the absolute integrand is `O(m ^ (2 re q + 2))`. -/
theorem integral_norm_mellin_optimalImageMode_le {q : ℂ} (hq : q.re < -1) (n : ℕ) :
    ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (q - 1) * ((optimalImageMode n t : ℝ) : ℂ)‖ ≤
      (40 * 8 ^ q.re * Real.Gamma (-q.re) + 32 * 8 ^ q.re * Real.Gamma (-(q.re + 1))) *
        ((n : ℝ) + 1) ^ (2 * q.re + 2) := by
  have ha := imageRateA_pos n
  have hx : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have i1 := (integrableOn_rpow_mul_exp_neg_div (σ := q.re) (by linarith) ha).const_mul
    (40 * ((n : ℝ) + 1) ^ 2)
  have i2 := (integrableOn_rpow_mul_exp_neg_div_succ hq ha).const_mul 4
  calc
    _ ≤ ∫ t in Ioi (0 : ℝ), (40 * ((n : ℝ) + 1) ^ 2 *
          (t ^ (q.re - 1) * Real.exp (-imageRateA n / t)) +
          4 * (t ^ q.re * Real.exp (-imageRateA n / t))) := by
      refine integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _)
        (i1.add i2) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact norm_mellin_optimalImageMode_le q n ht
    _ = 40 * ((n : ℝ) + 1) ^ 2 * (imageRateA n ^ q.re * Real.Gamma (-q.re)) +
          4 * (imageRateA n ^ (q.re + 1) * Real.Gamma (-(q.re + 1))) := by
      rw [integral_add i1 i2, integral_const_mul, integral_const_mul,
        integral_rpow_mul_exp_neg_div (by linarith) ha,
        integral_rpow_mul_exp_neg_div_succ hq ha]
    _ = _ := by
      rw [imageRateA_rpow, imageRateA_rpow, Real.rpow_add_one (by norm_num : (8 : ℝ) ≠ 0),
        show 2 * (q.re + 1) = 2 * q.re + 2 by ring, Real.rpow_add hx, Real.rpow_two]
      ring

theorem summable_imageIndex_rpow {p : ℝ} (hp : p < -1) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ p) := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr hp)
  simpa [Nat.cast_add, Nat.cast_one] using h

theorem summable_integral_norm_mellin_optimalImageMode {q : ℂ} (hq : q.re < -3 / 2) :
    Summable (fun n : ℕ =>
      ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (q - 1) * ((optimalImageMode n t : ℝ) : ℂ)‖) := by
  have hs := (summable_imageIndex_rpow (p := 2 * q.re + 2) (by linarith)).mul_left
    (40 * 8 ^ q.re * Real.Gamma (-q.re) + 32 * 8 ^ q.re * Real.Gamma (-(q.re + 1)))
  refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun t => norm_nonneg _)
    (fun n => integral_norm_mellin_optimalImageMode_le (by linarith) n) hs

end BrownianAffine
