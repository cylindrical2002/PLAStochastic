import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Brownian roots on a complex variance disc

The radius is `v₀ / 16`. The estimates compare the principal root with the root at
the positive real centre. No branch choice for the quotient `R / v` is assumed.
-/

noncomputable section

open Complex

namespace PGM

/-- An explicit admissible radius for the complex variance disc. -/
def cepsBrownianRadius (v₀ : ℝ) : ℝ := v₀ / 16

/-- The principal Brownian root. -/
def cepsBrownianR (v : ℂ) (lam : ℝ) (z : ℂ) : ℂ :=
  Complex.sqrt ((lam : ℂ) ^ 2 + 2 * v * z)

/-- The two scaled roots. -/
def cepsBrownianXiPlus (v : ℂ) (lam : ℝ) (z : ℂ) : ℂ :=
  (-(lam : ℂ) + cepsBrownianR v lam z) / v

def cepsBrownianXiMinus (v : ℂ) (lam : ℝ) (z : ℂ) : ℂ :=
  (-(lam : ℂ) - cepsBrownianR v lam z) / v

/-- The Brownian strip denominator. -/
def cepsBrownianDelta (v : ℂ) (lam : ℝ) (z : ℂ) : ℂ :=
  1 - Complex.exp (-2 * cepsBrownianR v lam z / v)

theorem cepsBrownianR_sq (v : ℂ) (lam : ℝ) (z : ℂ) :
    cepsBrownianR v lam z ^ 2 = (lam : ℂ) ^ 2 + 2 * v * z := by
  unfold cepsBrownianR Complex.sqrt
  exact cpow_ofNat_inv_pow _ 2

theorem cepsBrownianR_re_nonneg (v : ℂ) (lam : ℝ) (z : ℂ) :
    0 ≤ (cepsBrownianR v lam z).re := by
  rw [cepsBrownianR, Complex.sqrt, cpow_inv_two_re]
  exact Real.sqrt_nonneg _

theorem cepsBrownian_variance_bounds {v₀ : ℝ} {v : ℂ} (hv₀ : 0 < v₀)
    (hv : ‖v - (v₀ : ℂ)‖ ≤ cepsBrownianRadius v₀) :
    v₀ / 2 ≤ v.re ∧ v₀ / 2 ≤ ‖v‖ ∧ ‖v‖ ≤ 2 * v₀ ∧ v ≠ 0 := by
  have hr := Complex.abs_re_le_norm (v - (v₀ : ℂ))
  simp only [sub_re, ofReal_re] at hr
  have hdist : ‖v - (v₀ : ℂ)‖ ≤ v₀ / 16 := hv
  have hre : v₀ / 2 ≤ v.re := by
    have := (abs_le.mp (hr.trans hdist)).1
    linarith
  have hn : v₀ / 2 ≤ ‖v‖ := hre.trans (Complex.re_le_norm v)
  have hupper : ‖v‖ ≤ 2 * v₀ := by
    have ht := norm_add_le (v - (v₀ : ℂ)) (v₀ : ℂ)
    rw [sub_add_cancel, norm_real, Real.norm_eq_abs, abs_of_pos hv₀] at ht
    linarith
  exact ⟨hre, hn, hupper, norm_pos_iff.mp (by linarith)⟩

private theorem root_real_re {v₀ lam : ℝ} {z : ℂ} (hz : z.re = 0) :
    ‖cepsBrownianR (v₀ : ℂ) lam z‖ / 2 ≤ (cepsBrownianR (v₀ : ℂ) lam z).re := by
  set R := cepsBrownianR (v₀ : ℂ) lam z
  have hs : R.re ^ 2 - R.im ^ 2 = lam ^ 2 := by
    simpa [pow_two, add_re, mul_re, hz] using
      congrArg Complex.re (cepsBrownianR_sq (v₀ : ℂ) lam z)
  have hn : ‖R‖ ^ 2 = R.re ^ 2 + R.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hp := cepsBrownianR_re_nonneg (v₀ : ℂ) lam z
  change 0 ≤ R.re at hp
  nlinarith [sq_nonneg lam, sq_nonneg (‖R‖ - 2 * R.re), norm_nonneg R]

private theorem root_real_norm {v₀ lam : ℝ} {z : ℂ} (hv₀ : 0 < v₀) (hz : z.re = 0) :
    |lam| ≤ ‖cepsBrownianR (v₀ : ℂ) lam z‖ ∧
      2 * v₀ * ‖z‖ ≤ ‖cepsBrownianR (v₀ : ℂ) lam z‖ ^ 2 := by
  set W : ℂ := (lam : ℂ) ^ 2 + 2 * (v₀ : ℂ) * z
  have hn : ‖cepsBrownianR (v₀ : ℂ) lam z‖ ^ 2 = ‖W‖ := by
    rw [← norm_pow, cepsBrownianR_sq]
  have hre : W.re = lam ^ 2 := by simp [W, pow_two, mul_re, hz]
  have him : W.im = 2 * v₀ * z.im := by simp [W, pow_two, mul_im]
  have hzNorm : ‖z‖ = |z.im| := by
    rw [← Complex.re_add_im z, hz]
    simp
  constructor
  · have := Complex.re_le_norm W
    rw [hre, ← hn] at this
    nlinarith [sq_abs lam, abs_nonneg lam, norm_nonneg (cepsBrownianR (v₀ : ℂ) lam z)]
  · have h := Complex.abs_im_le_norm W
    rw [him, abs_mul, abs_of_pos (by positivity : 0 < 2 * v₀), ← hzNorm, ← hn] at h
    exact h

/-- Perturbing the variance in the explicit disc perturbs the root by at most an eighth. -/
theorem cepsBrownianR_perturbation {v₀ : ℝ} {v : ℂ} {lam : ℝ} {z : ℂ}
    (hv₀ : 0 < v₀) (hv : ‖v - (v₀ : ℂ)‖ ≤ cepsBrownianRadius v₀) (hz : z.re = 0) :
    ‖cepsBrownianR v lam z - cepsBrownianR (v₀ : ℂ) lam z‖ ≤
      ‖cepsBrownianR (v₀ : ℂ) lam z‖ / 8 := by
  set R := cepsBrownianR v lam z
  set S := cepsBrownianR (v₀ : ℂ) lam z
  have hprod : (R - S) * (R + S) = 2 * (v - (v₀ : ℂ)) * z := by
    calc
      (R - S) * (R + S) = R ^ 2 - S ^ 2 := by ring
      _ = 2 * (v - (v₀ : ℂ)) * z := by rw [cepsBrownianR_sq, cepsBrownianR_sq]; ring
  have hnorm := congrArg norm hprod
  simp only [norm_mul, Complex.norm_ofNat] at hnorm
  have hs := root_real_re (v₀ := v₀) (lam := lam) hz
  have hr := cepsBrownianR_re_nonneg v lam z
  have hsum := Complex.re_le_norm (R + S)
  simp only [add_re] at hsum
  have hsum' : ‖S‖ / 2 ≤ ‖R + S‖ := by linarith
  have hzNorm := (root_real_norm (lam := lam) hv₀ hz).2
  have hdist : ‖v - (v₀ : ℂ)‖ ≤ v₀ / 16 := hv
  have hupper : ‖R - S‖ * (‖S‖ / 2) ≤ v₀ * ‖z‖ / 8 := by
    calc
      ‖R - S‖ * (‖S‖ / 2) ≤ ‖R - S‖ * ‖R + S‖ :=
        mul_le_mul_of_nonneg_left hsum' (norm_nonneg _)
      _ = 2 * ‖v - (v₀ : ℂ)‖ * ‖z‖ := hnorm
      _ ≤ v₀ * ‖z‖ / 8 := by nlinarith [norm_nonneg z]
  by_cases hS : ‖S‖ = 0
  · have hz0 : z = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg z])
    have hlam0 : lam = 0 := by
      have := (root_real_norm (lam := lam) hv₀ hz).1
      change |lam| ≤ ‖S‖ at this
      rw [hS] at this
      exact abs_eq_zero.mp (le_antisymm this (abs_nonneg lam))
    simp [R, S, cepsBrownianR, hlam0, hz0]
  · have hSpos := lt_of_le_of_ne (norm_nonneg S) (Ne.symm hS)
    change ‖R - S‖ ≤ ‖S‖ / 8
    nlinarith

/-- A uniform lower bound expressed first in terms of the real-centre root. -/
theorem cepsBrownian_quotient_re_le {v₀ : ℝ} {v : ℂ} {lam : ℝ} {z : ℂ}
    (hv₀ : 0 < v₀) (hv : ‖v - (v₀ : ℂ)‖ ≤ cepsBrownianRadius v₀) (hz : z.re = 0) :
    ‖cepsBrownianR (v₀ : ℂ) lam z‖ / (8 * v₀) ≤ (cepsBrownianR v lam z / v).re := by
  set R := cepsBrownianR v lam z
  set S := cepsBrownianR (v₀ : ℂ) lam z
  obtain ⟨-, hvnorm, -, hvne⟩ := cepsBrownian_variance_bounds hv₀ hv
  have hv₀ne : (v₀ : ℂ) ≠ 0 := by exact_mod_cast hv₀.ne'
  have heq : R / v - S / (v₀ : ℂ) = (R - S) / v +
      S * ((v₀ : ℂ) - v) / (v * (v₀ : ℂ)) := by field_simp; ring
  have hd := cepsBrownianR_perturbation (lam := lam) hv₀ hv hz
  have hdist : ‖(v₀ : ℂ) - v‖ ≤ v₀ / 16 := by
    rw [norm_sub_rev]
    exact hv
  have hnorm : ‖R / v - S / (v₀ : ℂ)‖ ≤ 3 * ‖S‖ / (8 * v₀) := by
    rw [heq]
    calc
      ‖(R - S) / v + S * ((v₀ : ℂ) - v) / (v * (v₀ : ℂ))‖ ≤
          ‖R - S‖ / ‖v‖ + ‖S‖ * ‖(v₀ : ℂ) - v‖ / (‖v‖ * v₀) := by
        simpa [norm_div, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hv₀] using
          norm_add_le ((R - S) / v) (S * ((v₀ : ℂ) - v) / (v * (v₀ : ℂ)))
      _ ≤ (‖S‖ / 8) / (v₀ / 2) + (‖S‖ * (v₀ / 16)) / ((v₀ / 2) * v₀) := by
        gcongr
      _ = 3 * ‖S‖ / (8 * v₀) := by field_simp; ring
  have hre := (abs_le.mp ((Complex.abs_re_le_norm (R / v - S / (v₀ : ℂ))).trans hnorm)).1
  have hs := root_real_re (v₀ := v₀) (lam := lam) hz
  have hSre : (S / (v₀ : ℂ)).re = S.re / v₀ := by
    simp [Complex.div_re]
    field_simp
  rw [sub_re, hSre] at hre
  change ‖S‖ / 2 ≤ S.re at hs
  have hsdiv : ‖S‖ / (2 * v₀) ≤ S.re / v₀ := by
    simpa [div_div] using (div_le_div_of_nonneg_right hs hv₀.le)
  change ‖S‖ / (8 * v₀) ≤ (R / v).re
  have hrat : ‖S‖ / (2 * v₀) - 3 * ‖S‖ / (8 * v₀) = ‖S‖ / (8 * v₀) := by
    field_simp
    ring
  linarith

/-- A strictly positive decay constant, depending only on the real centre. -/
def cepsBrownianDecay (v₀ : ℝ) : ℝ := min 1 (Real.sqrt v₀) / (16 * v₀)

theorem cepsBrownianDecay_pos {v₀ : ℝ} (hv₀ : 0 < v₀) : 0 < cepsBrownianDecay v₀ := by
  unfold cepsBrownianDecay
  exact div_pos (lt_min zero_lt_one (Real.sqrt_pos.mpr hv₀)) (by positivity)

/-- Uniform exponential decay on the whole imaginary axis, including the origin. -/
theorem cepsBrownian_quotient_re {v₀ : ℝ} {v : ℂ} {lam : ℝ} {z : ℂ}
    (hv₀ : 0 < v₀) (hv : ‖v - (v₀ : ℂ)‖ ≤ cepsBrownianRadius v₀) (hz : z.re = 0) :
    cepsBrownianDecay v₀ * (|lam| + Real.sqrt ‖z‖) ≤ (cepsBrownianR v lam z / v).re := by
  set S := ‖cepsBrownianR (v₀ : ℂ) lam z‖
  obtain ⟨hlam, hzN⟩ := root_real_norm (lam := lam) hv₀ hz
  have hvSq := Real.sq_sqrt hv₀.le
  have hzSq := Real.sq_sqrt (norm_nonneg z)
  have hs : Real.sqrt v₀ * Real.sqrt ‖z‖ ≤ S := by
    nlinarith [Real.sqrt_nonneg v₀, Real.sqrt_nonneg ‖z‖,
      norm_nonneg (cepsBrownianR (v₀ : ℂ) lam z)]
  have hmin0 : 0 ≤ min 1 (Real.sqrt v₀) := le_min zero_le_one (Real.sqrt_nonneg _)
  have hbound : min 1 (Real.sqrt v₀) * (|lam| + Real.sqrt ‖z‖) ≤ 2 * S := by
    have h1 := mul_le_mul_of_nonneg_right (min_le_left 1 (Real.sqrt v₀)) (abs_nonneg lam)
    have h2 := mul_le_mul_of_nonneg_right (min_le_right 1 (Real.sqrt v₀))
      (Real.sqrt_nonneg ‖z‖)
    nlinarith
  have hdiv := div_le_div_of_nonneg_right hbound (by positivity : 0 ≤ 16 * v₀)
  have heq : (2 * S) / (16 * v₀) = S / (8 * v₀) := by ring
  rw [heq] at hdiv
  simpa [cepsBrownianDecay, div_mul_eq_mul_div] using
    hdiv.trans (cepsBrownian_quotient_re_le (lam := lam) hv₀ hv hz)

theorem cepsBrownian_quotient_re_pos {v₀ : ℝ} {v : ℂ} {lam : ℝ} {z : ℂ}
    (hv₀ : 0 < v₀) (hv : ‖v - (v₀ : ℂ)‖ ≤ cepsBrownianRadius v₀)
    (hz : z.re = 0) (hne : lam ≠ 0 ∨ z ≠ 0) : 0 < (cepsBrownianR v lam z / v).re := by
  have hsum : 0 < |lam| + Real.sqrt ‖z‖ := by
    rcases hne with hl | hz0
    · exact add_pos_of_pos_of_nonneg (abs_pos.mpr hl) (Real.sqrt_nonneg _)
    · exact add_pos_of_nonneg_of_pos (abs_nonneg _) (Real.sqrt_pos.mpr (norm_pos_iff.mpr hz0))
  exact (mul_pos (cepsBrownianDecay_pos hv₀) hsum).trans_le
    (cepsBrownian_quotient_re hv₀ hv hz)

/-- No strip pole lies on the imaginary axis away from the joint zero. -/
theorem cepsBrownianDelta_ne_zero {v₀ : ℝ} {v : ℂ} {lam : ℝ} {z : ℂ}
    (hv₀ : 0 < v₀) (hv : ‖v - (v₀ : ℂ)‖ ≤ cepsBrownianRadius v₀)
    (hz : z.re = 0) (hne : lam ≠ 0 ∨ z ≠ 0) : cepsBrownianDelta v lam z ≠ 0 := by
  have hp := cepsBrownian_quotient_re_pos hv₀ hv hz hne
  have hnorm : ‖Complex.exp (-2 * cepsBrownianR v lam z / v)‖ < 1 := by
    rw [show -2 * cepsBrownianR v lam z / v = -2 * (cepsBrownianR v lam z / v) by ring,
      Complex.norm_exp]
    apply Real.exp_lt_one_iff.mpr
    simpa using (show -2 * (cepsBrownianR v lam z / v).re < 0 by linarith)
  intro hzero
  have heq : Complex.exp (-2 * cepsBrownianR v lam z / v) = 1 :=
    (sub_eq_zero.mp hzero).symm
  rw [heq, norm_one] at hnorm
  exact (lt_irrefl 1) hnorm

theorem cepsBrownianR_norm_le {v₀ : ℝ} {v : ℂ} (hv₀ : 0 < v₀)
    (hv : ‖v - (v₀ : ℂ)‖ ≤ cepsBrownianRadius v₀) (lam : ℝ) (z : ℂ) :
    ‖cepsBrownianR v lam z‖ ≤ |lam| + 2 * Real.sqrt v₀ * Real.sqrt ‖z‖ := by
  have hn : ‖cepsBrownianR v lam z‖ ^ 2 ≤ lam ^ 2 + 4 * v₀ * ‖z‖ := by
    rw [← norm_pow, cepsBrownianR_sq]
    calc
      ‖(lam : ℂ) ^ 2 + 2 * v * z‖ ≤ ‖(lam : ℂ) ^ 2‖ + ‖2 * v * z‖ := norm_add_le _ _
      _ = lam ^ 2 + 2 * ‖v‖ * ‖z‖ := by simp [norm_pow, sq_abs]
      _ ≤ lam ^ 2 + 4 * v₀ * ‖z‖ := by
        have := (cepsBrownian_variance_bounds hv₀ hv).2.2.1
        nlinarith [norm_nonneg z]
  have hs : (Real.sqrt v₀ * Real.sqrt ‖z‖) ^ 2 = v₀ * ‖z‖ := by
    rw [mul_pow, Real.sq_sqrt hv₀.le, Real.sq_sqrt (norm_nonneg z)]
  set B := Real.sqrt v₀ * Real.sqrt ‖z‖
  have hB : 0 ≤ B := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  change B ^ 2 = v₀ * ‖z‖ at hs
  have hRHS : lam ^ 2 + 4 * v₀ * ‖z‖ ≤ (|lam| + 2 * B) ^ 2 := by
    nlinarith [sq_abs lam, mul_nonneg (abs_nonneg lam) hB]
  have hfinal := (sq_le_sq₀ (norm_nonneg (cepsBrownianR v lam z))
    (by positivity : 0 ≤ |lam| + 2 * B)).mp (hn.trans hRHS)
  simpa [B, mul_assoc] using hfinal

/-- Holomorphy of the root in the variance; the joint-zero case is constant. -/
theorem cepsBrownianR_differentiableAt {v lam z} (hv : 0 < v.re) (hz : z.re = 0) :
    DifferentiableAt ℂ (fun u => cepsBrownianR u lam z) v := by
  by_cases hz0 : z = 0
  · simp only [cepsBrownianR, hz0, mul_zero, add_zero]
    exact differentiableAt_const _
  · have hzim : z.im ≠ 0 := by
      intro heq
      exact hz0 (Complex.ext hz heq)
    have hslit : (lam : ℂ) ^ 2 + 2 * v * z ∈ Complex.slitPlane := by
      right
      simpa [pow_two, add_im, mul_im, hz] using
        (mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hv.ne') hzim)
    exact (Complex.differentiableAt_sqrt hslit).comp v
      (differentiableAt_const _ |>.add ((differentiableAt_id.const_mul 2).mul_const z))

end PGM
