import PLAStochastic.Index.CEPS.BrownianCoeff.PositiveBounds
import PLAStochastic.Index.CEPS.BrownianCoeff.LowerDrift

/-!
# The positive-drift cancellation and the all-drift kernel envelope

The half-line subtraction is estimated as a difference, including zero frequency.
-/

noncomputable section

open Complex

namespace PGM

def cepsBrownianUpperAmplitude (v₀ : ℝ) : ℝ :=
  2 * cepsBrownianSinhcConst * (cepsBrownianEntranceConst v₀ + 2) *
      (1 + (cepsBrownianDecay v₀)⁻¹) +
    cepsBrownianEntranceConst v₀ ^ 2 * cepsBrownianBridgeDifferenceConst v₀

def cepsBrownianUpperConst (v₀ : ℝ) : ℝ :=
  cepsBrownianUpperAmplitude v₀ * cepsBrownianRootBudget v₀ ^ 2

def cepsBrownianKernelConst (v₀ : ℝ) : ℝ :=
  cepsBrownianLowerConst v₀ + cepsBrownianUpperConst v₀

theorem cepsBrownianKernel_upper_cancellation {v₀ : ℝ} {v : ℂ} {lam : ℝ} {z : ℂ}
    (hv₀ : 0 < v₀) (hv : ‖v - (v₀ : ℂ)‖ ≤ cepsBrownianRadius v₀)
    (hz : z.re = 0) (hlam : 1 ≤ lam) :
    cepsBrownianKernel v lam z =
      -(cepsBrownianH v lam z ^ 2 - cepsBrownianHInf v lam z ^ 2) *
          deriv (fun u => cepsBrownianUInf v lam u) z -
        cepsBrownianH v lam z ^ 2 *
          (deriv (fun u => cepsBrownianU v lam u) z -
            deriv (fun u => cepsBrownianUInf v lam u) z) := by
  have hvne := (cepsBrownian_variance_bounds hv₀ hv).2.2.2
  have hS := cepsBrownianSinhc_ne (lam := lam) hv₀ hv hz
  rw [cepsBrownianKernel, if_pos hlam,
    (cepsBrownianU_hasDerivAt lam z hvne hS).deriv,
    (cepsBrownianUInf_hasDerivAt hv₀ hv hz (Or.inl (by linarith : lam ≠ 0))).deriv]
  ring

theorem cepsBrownianKernel_upper_amplitude {v₀ : ℝ} {v : ℂ} {lam : ℝ} {z : ℂ}
    (hv₀ : 0 < v₀) (hv : ‖v - (v₀ : ℂ)‖ ≤ cepsBrownianRadius v₀)
    (hz : z.re = 0) (hlam : 1 ≤ lam) :
    ‖cepsBrownianKernel v lam z‖ ≤ cepsBrownianUpperAmplitude v₀ *
      (1 + ‖cepsBrownianR v lam z / v‖) ^ 2 *
        Real.exp (-2 * (cepsBrownianR v lam z / v).re) := by
  set a := ((lam : ℂ) / v).re
  set s := (cepsBrownianR v lam z / v).re
  set Q := 1 + ‖cepsBrownianR v lam z / v‖
  set A := cepsBrownianEntranceConst v₀
  set C := cepsBrownianSinhcConst
  set B := cepsBrownianBridgeDifferenceConst v₀
  set T := 1 + (cepsBrownianDecay v₀)⁻¹
  have hC : 0 ≤ C := by dsimp [C]; linarith [cepsBrownianSinhcConst_bounds.1]
  have hA : 0 ≤ A := by dsimp [A, cepsBrownianEntranceConst]; positivity
  have hT : 0 ≤ T := by have hc := (cepsBrownianDecay_pos hv₀).le; dsimp [T]; positivity
  have hB : 0 ≤ B := by
    have hd := (cepsBrownianDeltaInverseConst_pos hv₀).le
    dsimp [B, cepsBrownianBridgeDifferenceConst]
    positivity
  have hQ : 1 ≤ Q := by dsimp [Q]; linarith [norm_nonneg (cepsBrownianR v lam z / v)]
  have ha : a ≤ s := (cepsBrownian_positive_drift_re hv₀ hv hz (by linarith)).2
  have hH := cepsBrownianH_positive_norm (lam := lam) hv₀ hv hz (by linarith : 0 < lam)
  have hInf := cepsBrownianHInf_norm (v := v) (z := z) hlam
  have hDiff := cepsBrownianH_difference_norm hv₀ hv hz hlam
  have hUinf := cepsBrownianUInf_deriv_norm hv₀ hv hz hlam
  have hUdiff := cepsBrownianU_deriv_difference_norm hv₀ hv hz hlam
  have hsum : ‖cepsBrownianH v lam z + cepsBrownianHInf v lam z‖ ≤ (A + 2) * Q := by
    have h := norm_add_le (cepsBrownianH v lam z) (cepsBrownianHInf v lam z)
    change ‖cepsBrownianH v lam z‖ ≤ A * Q at hH
    nlinarith
  have hsquares : ‖cepsBrownianH v lam z ^ 2 - cepsBrownianHInf v lam z ^ 2‖ ≤
      (2 * C * Q * Real.exp (-a - s)) * ((A + 2) * Q) := by
    rw [show cepsBrownianH v lam z ^ 2 - cepsBrownianHInf v lam z ^ 2 =
      (cepsBrownianH v lam z - cepsBrownianHInf v lam z) *
        (cepsBrownianH v lam z + cepsBrownianHInf v lam z) by ring, norm_mul]
    exact mul_le_mul hDiff hsum (norm_nonneg _) (by positivity)
  have hexp : Real.exp (a - 3 * s) ≤ Real.exp (-2 * s) := Real.exp_le_exp.mpr (by linarith)
  rw [cepsBrownianKernel_upper_cancellation hv₀ hv hz hlam]
  calc
    _ ≤ ‖-(cepsBrownianH v lam z ^ 2 - cepsBrownianHInf v lam z ^ 2) *
          deriv (fun u => cepsBrownianUInf v lam u) z‖ +
        ‖cepsBrownianH v lam z ^ 2 *
          (deriv (fun u => cepsBrownianU v lam u) z -
            deriv (fun u => cepsBrownianUInf v lam u) z)‖ := norm_sub_le _ _
    _ = ‖cepsBrownianH v lam z ^ 2 - cepsBrownianHInf v lam z ^ 2‖ *
          ‖deriv (fun u => cepsBrownianUInf v lam u) z‖ +
        ‖cepsBrownianH v lam z‖ ^ 2 *
          ‖deriv (fun u => cepsBrownianU v lam u) z -
            deriv (fun u => cepsBrownianUInf v lam u) z‖ := by
      rw [norm_mul, norm_neg, norm_mul, norm_pow]
    _ ≤ ((2 * C * Q * Real.exp (-a - s)) * ((A + 2) * Q)) *
          (T * Real.exp (a - s)) + (A * Q) ^ 2 * (B * Real.exp (a - 3 * s)) := by gcongr
    _ ≤ ((2 * C * Q * Real.exp (-a - s)) * ((A + 2) * Q)) *
          (T * Real.exp (a - s)) + (A * Q) ^ 2 * (B * Real.exp (-2 * s)) := by gcongr
    _ = _ := by
      have he : Real.exp (-a - s) * Real.exp (a - s) = Real.exp (-2 * s) := by
        rw [← Real.exp_add]
        congr 1
        ring
      change _ = cepsBrownianUpperAmplitude v₀ * Q ^ 2 * Real.exp (-2 * s)
      unfold cepsBrownianUpperAmplitude
      change _ = (2 * C * (A + 2) * T + A ^ 2 * B) * Q ^ 2 * Real.exp (-2 * s)
      calc
        _ = (2 * C * (A + 2) * T) * Q ^ 2 *
            (Real.exp (-a - s) * Real.exp (a - s)) + A ^ 2 * B * Q ^ 2 *
              Real.exp (-2 * s) := by ring
        _ = _ := by rw [he]; ring

theorem cepsBrownianUpperConst_nonneg {v₀ : ℝ} (hv₀ : 0 < v₀) :
    0 ≤ cepsBrownianUpperConst v₀ := by
  have hC : 0 ≤ cepsBrownianSinhcConst := by linarith [cepsBrownianSinhcConst_bounds.1]
  have hc := (cepsBrownianDecay_pos hv₀).le
  have hd := (cepsBrownianDeltaInverseConst_pos hv₀).le
  unfold cepsBrownianUpperConst cepsBrownianUpperAmplitude cepsBrownianBridgeDifferenceConst
    cepsBrownianEntranceConst
  positivity

theorem cepsBrownianKernel_upper_decay {v₀ : ℝ} {v : ℂ} {lam : ℝ} {z : ℂ}
    (hv₀ : 0 < v₀) (hv : ‖v - (v₀ : ℂ)‖ ≤ cepsBrownianRadius v₀)
    (hz : z.re = 0) (hlam : 1 ≤ lam) :
    ‖cepsBrownianKernel v lam z‖ ≤ cepsBrownianUpperConst v₀ * (1 + |lam| + ‖z‖) ^ 4 *
      Real.exp (-(cepsBrownianDecay v₀ / 3) * (|lam| + Real.sqrt ‖z‖)) := by
  have h := cepsBrownianKernel_upper_amplitude hv₀ hv hz hlam
  have hp := cepsBrownian_root_polynomial lam z hv₀ hv
  have hc := cepsBrownianDecay_pos hv₀
  have hs := cepsBrownian_quotient_re (lam := lam) hv₀ hv hz
  have hsum : 0 ≤ |lam| + Real.sqrt ‖z‖ := by positivity
  have ha : 0 ≤ cepsBrownianUpperAmplitude v₀ := by
    have hC : 0 ≤ cepsBrownianSinhcConst := by linarith [cepsBrownianSinhcConst_bounds.1]
    have hd := (cepsBrownianDeltaInverseConst_pos hv₀).le
    unfold cepsBrownianUpperAmplitude cepsBrownianEntranceConst cepsBrownianBridgeDifferenceConst
    positivity
  have hexp : Real.exp (-2 * (cepsBrownianR v lam z / v).re) ≤
      Real.exp (-(cepsBrownianDecay v₀ / 3) * (|lam| + Real.sqrt ‖z‖)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hpoly : (1 + |lam| + ‖z‖) ^ 2 ≤ (1 + |lam| + ‖z‖) ^ 4 := by
    have hP : 1 ≤ 1 + |lam| + ‖z‖ := by linarith [abs_nonneg lam, norm_nonneg z]
    exact pow_le_pow_right₀ hP (by norm_num : (2 : ℕ) ≤ 4)
  have hu : 0 ≤ cepsBrownianUpperConst v₀ := cepsBrownianUpperConst_nonneg hv₀
  calc
    _ ≤ cepsBrownianUpperAmplitude v₀ * (1 + ‖cepsBrownianR v lam z / v‖) ^ 2 *
        Real.exp (-2 * (cepsBrownianR v lam z / v).re) := h
    _ ≤ cepsBrownianUpperAmplitude v₀ *
        (cepsBrownianRootBudget v₀ * (1 + |lam| + ‖z‖)) ^ 2 *
          Real.exp (-(cepsBrownianDecay v₀ / 3) * (|lam| + Real.sqrt ‖z‖)) := by gcongr
    _ = cepsBrownianUpperConst v₀ * (1 + |lam| + ‖z‖) ^ 2 *
        Real.exp (-(cepsBrownianDecay v₀ / 3) * (|lam| + Real.sqrt ‖z‖)) := by
      unfold cepsBrownianUpperConst
      ring
    _ ≤ _ := by gcongr

theorem cepsBrownianKernelConst_nonneg {v₀ : ℝ} (hv₀ : 0 < v₀) :
    0 ≤ cepsBrownianKernelConst v₀ := by
  have hl : 0 ≤ cepsBrownianLowerConst v₀ := by
    unfold cepsBrownianLowerConst cepsBrownianBridgeDerivConst
    positivity
  exact add_nonneg hl (cepsBrownianUpperConst_nonneg hv₀)

theorem cepsBrownianKernelConst_pos {v₀ : ℝ} (hv₀ : 0 < v₀) :
    0 < cepsBrownianKernelConst v₀ := by
  have hC : 0 < cepsBrownianSinhcConst := by linarith [cepsBrownianSinhcConst_bounds.1]
  have hRoot := cepsBrownianRootBudget_pos hv₀
  have hl : 0 < cepsBrownianLowerConst v₀ := by
    unfold cepsBrownianLowerConst cepsBrownianEntranceConst cepsBrownianBridgeDerivConst
    positivity
  exact add_pos_of_pos_of_nonneg hl (cepsBrownianUpperConst_nonneg hv₀)

theorem cepsBrownianKernel_decay {v₀ : ℝ} {v : ℂ} (lam : ℝ) (z : ℂ)
    (hv₀ : 0 < v₀) (hv : ‖v - (v₀ : ℂ)‖ ≤ cepsBrownianRadius v₀) (hz : z.re = 0) :
    ‖cepsBrownianKernel v lam z‖ ≤ cepsBrownianKernelConst v₀ * (1 + |lam| + ‖z‖) ^ 4 *
      Real.exp (-(cepsBrownianDecay v₀ / 3) * (|lam| + Real.sqrt ‖z‖)) := by
  have hu := cepsBrownianUpperConst_nonneg hv₀
  have hl : 0 ≤ cepsBrownianLowerConst v₀ := by
    unfold cepsBrownianLowerConst cepsBrownianBridgeDerivConst
    positivity
  by_cases hlam : 1 ≤ lam
  · exact (cepsBrownianKernel_upper_decay hv₀ hv hz hlam).trans (by
      unfold cepsBrownianKernelConst
      gcongr
      linarith)
  · exact (cepsBrownianKernel_lower_decay hv₀ hv hz (lt_of_not_ge hlam)).trans (by
      unfold cepsBrownianKernelConst
      gcongr
      linarith)

end PGM
