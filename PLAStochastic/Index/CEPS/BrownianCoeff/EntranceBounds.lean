import PLAStochastic.Index.CEPS.BrownianCoeff.EntranceIntegral
import PLAStochastic.Index.CEPS.BrownianCoeff.SinhcInverse
import PLAStochastic.Index.CEPS.BrownianCoeff.Sector

/-!
# A real-part budget for the Brownian entrance

The growing exponent is retained explicitly so it can cancel against the bridge.
-/

noncomputable section

open Complex Set MeasureTheory

namespace PGM

private theorem unit_mul_le_max {t x : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : t * x ≤ max 0 x := by
  rcases le_total 0 x with hx | hx
  · rw [max_eq_right hx]
    nlinarith [ht.1, ht.2]
  · rw [max_eq_left hx]
    exact mul_nonpos_of_nonneg_of_nonpos ht.1 hx

theorem cepsBrownianEntranceIntegral_norm (a s : ℂ) (hs : 0 ≤ s.re) :
    ‖cepsBrownianEntranceIntegral a (s ^ 2)‖ ≤
      Real.exp (s.re + max 0 (-a.re - s.re)) := by
  unfold cepsBrownianEntranceIntegral
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (f := fun t : ℝ => Complex.exp (-a * t) * ((1 - t : ℝ) : ℂ) *
      cepsBrownianSinhc (((1 - t : ℝ) : ℂ) ^ 2 * s ^ 2))
    (C := Real.exp (s.re + max 0 (-a.re - s.re))) ?_
  · simpa using h
  · intro t ht
    rw [uIoc_of_le zero_le_one] at ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self ht
    have hq : 0 ≤ 1 - t := by linarith [ht'.2]
    have hS := cepsBrownian_sinhc_norm (((1 - t : ℝ) : ℂ) * s)
    rw [mul_pow] at hS
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
      abs_of_nonneg (mul_nonneg hq hs)] at hS
    rw [norm_mul, norm_mul, Complex.norm_exp, norm_real, Real.norm_eq_abs, abs_of_nonneg hq]
    have hre : (-a * (t : ℂ)).re = -a.re * t := by simp
    rw [hre]
    calc
      Real.exp (-a.re * t) * (1 - t) *
          ‖cepsBrownianSinhc (((1 - t : ℝ) : ℂ) ^ 2 * s ^ 2)‖ ≤
          Real.exp (-a.re * t) * 1 * Real.exp ((1 - t) * s.re) := by gcongr; linarith [ht'.1]
      _ = Real.exp (s.re + t * (-a.re - s.re)) := by
        rw [mul_one, ← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (s.re + max 0 (-a.re - s.re)) :=
        Real.exp_le_exp.mpr (by have h := unit_mul_le_max (x := -a.re - s.re) ht'; linarith)

def cepsBrownianEntranceConst (v₀ : ℝ) : ℝ := 4 * cepsBrownianSinhcConst / v₀

theorem cepsBrownianH_norm {v₀ : ℝ} {v : ℂ} (lam : ℝ) (z : ℂ) (hv₀ : 0 < v₀)
    (hv : ‖v - (v₀ : ℂ)‖ ≤ cepsBrownianRadius v₀) (hz : z.re = 0) :
    ‖cepsBrownianH v lam z‖ ≤ cepsBrownianEntranceConst v₀ *
      (1 + ‖cepsBrownianR v lam z / v‖) *
        Real.exp (max 0 (-((lam : ℂ) / v).re - (cepsBrownianR v lam z / v).re)) := by
  set a := (lam : ℂ) / v
  set s := cepsBrownianR v lam z / v
  have hvne := (cepsBrownian_variance_bounds hv₀ hv).2.2.2
  have hvnorm := (cepsBrownian_variance_bounds hv₀ hv).2.1
  have hsector := cepsBrownian_quotient_sector (lam := lam) hv₀ hv hz
  have hs : 0 ≤ s.re := by linarith [norm_nonneg s]
  have hI := cepsBrownianEntranceIntegral_norm a s hs
  have hInv := cepsBrownianSinhc_inverse hsector
  rw [cepsBrownianH_integral, ← cepsBrownian_normalized_sq hvne, norm_div, norm_mul,
    norm_div, Complex.norm_ofNat, div_eq_mul_inv]
  change 2 / ‖v‖ * ‖cepsBrownianEntranceIntegral a (s ^ 2)‖ *
    ‖cepsBrownianSinhc (s ^ 2)‖⁻¹ ≤ _
  have hC0 : 0 ≤ cepsBrownianSinhcConst := by linarith [cepsBrownianSinhcConst_bounds.1]
  have hconst : 2 * cepsBrownianSinhcConst / ‖v‖ ≤ cepsBrownianEntranceConst v₀ := by
    unfold cepsBrownianEntranceConst
    calc
      2 * cepsBrownianSinhcConst / ‖v‖ ≤ 2 * cepsBrownianSinhcConst / (v₀ / 2) := by gcongr
      _ = 4 * cepsBrownianSinhcConst / v₀ := by ring
  calc
    2 / ‖v‖ * ‖cepsBrownianEntranceIntegral a (s ^ 2)‖ * ‖cepsBrownianSinhc (s ^ 2)‖⁻¹ ≤
        2 / ‖v‖ * Real.exp (s.re + max 0 (-a.re - s.re)) *
          (cepsBrownianSinhcConst * (1 + ‖s‖) * Real.exp (-s.re)) := by gcongr
    _ = (2 * cepsBrownianSinhcConst / ‖v‖) * (1 + ‖s‖) *
        Real.exp (max 0 (-a.re - s.re)) := by
      rw [Real.exp_add]
      have he : Real.exp s.re * Real.exp (-s.re) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      calc
        _ = (2 * cepsBrownianSinhcConst / ‖v‖) * (1 + ‖s‖) *
          Real.exp (max 0 (-a.re - s.re)) * (Real.exp s.re * Real.exp (-s.re)) := by ring
        _ = _ := by rw [he, mul_one]
    _ ≤ cepsBrownianEntranceConst v₀ * (1 + ‖s‖) *
        Real.exp (max 0 (-a.re - s.re)) := by gcongr

end PGM
