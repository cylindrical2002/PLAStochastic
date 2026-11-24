import PLAStochastic.Index.CEPS.BrownianCoeff.Sector
import PLAStochastic.Index.CEPS.BrownianCoeff.Defs

/-!
# Positive-drift root estimates

The rationalized positive root has nonnegative real part on the imaginary axis.
This controls the full-line exponential without losing positive-drift decay.
-/

noncomputable section

open Complex

namespace PGM

theorem cepsBrownianR_re_pos {v : ℂ} {lam : ℝ} {z : ℂ}
    (hv : 0 < v.re) (hlam : 0 < lam) (hz : z.re = 0) :
    0 < (cepsBrownianR v lam z).re := by
  set R := cepsBrownianR v lam z
  have hre : R.re ^ 2 - R.im ^ 2 = lam ^ 2 - 2 * v.im * z.im := by
    have h := congrArg Complex.re (cepsBrownianR_sq v lam z)
    simp [pow_two, mul_re, hz] at h
    nlinarith only [h]
  have him : R.re * R.im = v.re * z.im := by
    have h := congrArg Complex.im (cepsBrownianR_sq v lam z)
    simp [pow_two, mul_im, mul_re, hz] at h
    linear_combination h / 2
  have hnonneg : 0 ≤ R.re := cepsBrownianR_re_nonneg v lam z
  by_contra h
  have hzero : R.re = 0 := by linarith
  have hzim : z.im = 0 := by
    rw [hzero, zero_mul] at him
    exact (mul_eq_zero.mp him.symm).resolve_left hv.ne'
  rw [hzero, hzim] at hre
  nlinarith [sq_nonneg R.im, sq_pos_of_pos hlam]

theorem cepsBrownianXiPlus_rationalized {v : ℂ} {lam : ℝ} {z : ℂ}
    (hv : v ≠ 0) (hlam : 0 < lam) :
    cepsBrownianXiPlus v lam z = 2 * z / ((lam : ℂ) + cepsBrownianR v lam z) := by
  have hden : (lam : ℂ) + cepsBrownianR v lam z ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [add_re, ofReal_re, zero_re] at h'
    linarith [cepsBrownianR_re_nonneg v lam z]
  have hs := cepsBrownianR_sq v lam z
  unfold cepsBrownianXiPlus
  field_simp
  linear_combination hs

theorem cepsBrownianXiPlus_re_nonneg {v : ℂ} {lam : ℝ} {z : ℂ}
    (hv : 0 < v.re) (hlam : 0 < lam) (hz : z.re = 0) :
    0 ≤ (cepsBrownianXiPlus v lam z).re := by
  have hvne : v ≠ 0 := by intro h; simp [h] at hv
  set R := cepsBrownianR v lam z
  have hr : 0 < R.re := cepsBrownianR_re_pos hv hlam hz
  have him : R.re * R.im = v.re * z.im := by
    have h := congrArg Complex.im (cepsBrownianR_sq v lam z)
    simp [pow_two, mul_im, mul_re, hz] at h
    linear_combination h / 2
  have hprod : 0 ≤ z.im * R.im := by
    have hmul := congrArg (fun x : ℝ => x * z.im) him
    have hsq : 0 ≤ v.re * z.im ^ 2 := mul_nonneg hv.le (sq_nonneg _)
    have h : 0 ≤ R.re * (z.im * R.im) := by nlinarith only [hmul, hsq]
    exact nonneg_of_mul_nonneg_right h hr
  rw [cepsBrownianXiPlus_rationalized hvne hlam]
  simp [Complex.div_re, mul_re, mul_im, hz]
  exact div_nonneg (by simpa [R, mul_assoc] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hprod)
    (Complex.normSq_nonneg _)

theorem cepsBrownian_positive_drift_re {v₀ : ℝ} {v : ℂ} {lam : ℝ} {z : ℂ}
    (hv₀ : 0 < v₀) (hv : ‖v - (v₀ : ℂ)‖ ≤ cepsBrownianRadius v₀)
    (hz : z.re = 0) (hlam : 0 < lam) :
    0 ≤ ((lam : ℂ) / v).re ∧
      ((lam : ℂ) / v).re ≤ (cepsBrownianR v lam z / v).re := by
  have hvre := (cepsBrownian_variance_bounds hv₀ hv).1
  have hvpos : 0 < v.re := by linarith
  have ha : 0 ≤ ((lam : ℂ) / v).re := by
    simp only [Complex.div_re, ofReal_re, ofReal_im, zero_mul, zero_div, add_zero]
    exact div_nonneg (mul_nonneg hlam.le hvpos.le) (Complex.normSq_nonneg _)
  have hxi := cepsBrownianXiPlus_re_nonneg hvpos hlam hz
  have he : (cepsBrownianXiPlus v lam z).re =
      (cepsBrownianR v lam z / v).re - ((lam : ℂ) / v).re := by
    rw [cepsBrownianXiPlus, add_div]
    simp only [add_re, neg_div, neg_re]
    ring
  exact ⟨ha, by rw [he] at hxi; linarith⟩

theorem cepsBrownianHInf_norm {v : ℂ} {lam : ℝ} {z : ℂ} (hlam : 1 ≤ lam) :
    ‖cepsBrownianHInf v lam z‖ ≤ 2 := by
  have hden : 1 ≤ ‖(lam : ℂ) + cepsBrownianR v lam z‖ := by
    have h := Complex.re_le_norm ((lam : ℂ) + cepsBrownianR v lam z)
    simp only [add_re, ofReal_re] at h
    linarith [cepsBrownianR_re_nonneg v lam z]
  rw [cepsBrownianHInf, norm_div, Complex.norm_ofNat]
  exact (div_le_iff₀ (by linarith : 0 < ‖(lam : ℂ) + cepsBrownianR v lam z‖)).mpr
    (by linarith)

end PGM
