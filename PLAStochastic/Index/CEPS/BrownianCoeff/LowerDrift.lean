import PLAStochastic.Index.CEPS.BrownianCoeff.EntranceBounds
import PLAStochastic.Index.CEPS.BrownianCoeff.BridgeBounds

/-!
# Exponential decay below the half-line subtraction threshold

This includes the negative-drift tail and the joint zero-frequency point.
-/

noncomputable section

open Complex

namespace PGM

theorem cepsBrownian_drift_re_le {v₀ : ℝ} {v : ℂ} {lam : ℝ}
    (hv₀ : 0 < v₀) (hv : ‖v - (v₀ : ℂ)‖ ≤ cepsBrownianRadius v₀) (hlam : lam ≤ 1) :
    ((lam : ℂ) / v).re ≤ 2 / v₀ := by
  obtain ⟨hvre, hvnorm, -, -⟩ := cepsBrownian_variance_bounds hv₀ hv
  have hinv0 : 0 ≤ (1 / v : ℂ).re := by
    have hvre0 : 0 ≤ v.re := by linarith
    simpa [Complex.div_re] using div_nonneg hvre0 (Complex.normSq_nonneg v)
  have hinv : (1 / v : ℂ).re ≤ 2 / v₀ := by
    calc
      (1 / v : ℂ).re ≤ ‖(1 / v : ℂ)‖ := Complex.re_le_norm _
      _ = 1 / ‖v‖ := by simp
      _ ≤ 2 / v₀ := by
        have h := div_le_div_of_nonneg_left zero_le_one (by positivity : 0 < v₀ / 2) hvnorm
        simpa using h
  have he : ((lam : ℂ) / v).re = lam * (1 / v : ℂ).re := by
    rw [show (lam : ℂ) / v = (lam : ℂ) * (1 / v) by ring]
    simp
  rw [he]
  exact (mul_le_mul_of_nonneg_right hlam hinv0).trans (by simpa using hinv)

theorem cepsBrownian_lower_exponent {v₀ : ℝ} {v : ℂ} {lam : ℝ} {z : ℂ}
    (hv₀ : 0 < v₀) (hv : ‖v - (v₀ : ℂ)‖ ≤ cepsBrownianRadius v₀) (hz : z.re = 0)
    (hlam : lam ≤ 1) :
    2 * max 0 (-((lam : ℂ) / v).re - (cepsBrownianR v lam z / v).re) +
        ((lam : ℂ) / v).re - (cepsBrownianR v lam z / v).re ≤
      2 / v₀ - cepsBrownianDecay v₀ / 3 * (|lam| + Real.sqrt ‖z‖) := by
  have ha := cepsBrownian_drift_re_le hv₀ hv hlam
  have hr := cepsBrownian_quotient_re (lam := lam) hv₀ hv hz
  have hc := cepsBrownian_combined_exponent (lam := lam) hv₀ hv hz
  have hcp := cepsBrownianDecay_pos hv₀
  have hp : 0 ≤ cepsBrownianDecay v₀ * (|lam| + Real.sqrt ‖z‖) := by positivity
  by_cases hX : 0 ≤ -((lam : ℂ) / v).re - (cepsBrownianR v lam z / v).re
  · rw [max_eq_right hX]
    have habs := neg_le_abs (((lam : ℂ) / v).re)
    have hvdiv : 0 ≤ 2 / v₀ := by positivity
    linarith
  · rw [max_eq_left (le_of_not_ge hX)]
    linarith

def cepsBrownianLowerConst (v₀ : ℝ) : ℝ :=
  cepsBrownianEntranceConst v₀ ^ 2 * cepsBrownianBridgeDerivConst *
    cepsBrownianRootBudget v₀ ^ 4 * Real.exp (2 / v₀)

theorem cepsBrownianKernel_of_lt {v₀ : ℝ} {v : ℂ} {lam : ℝ} {z : ℂ}
    (hv₀ : 0 < v₀) (hv : ‖v - (v₀ : ℂ)‖ ≤ cepsBrownianRadius v₀) (hz : z.re = 0)
    (hlam : lam < 1) :
    cepsBrownianKernel v lam z = -(cepsBrownianH v lam z ^ 2) *
      deriv (fun u => cepsBrownianU v lam u) z := by
  have hvne := (cepsBrownian_variance_bounds hv₀ hv).2.2.2
  have hS := cepsBrownianSinhc_ne (lam := lam) hv₀ hv hz
  rw [cepsBrownianKernel, if_neg (not_le.mpr hlam), add_zero,
    (cepsBrownianU_hasDerivAt lam z hvne hS).deriv]
  ring

theorem cepsBrownianKernel_lower_decay {v₀ : ℝ} {v : ℂ} {lam : ℝ} {z : ℂ}
    (hv₀ : 0 < v₀) (hv : ‖v - (v₀ : ℂ)‖ ≤ cepsBrownianRadius v₀) (hz : z.re = 0)
    (hlam : lam < 1) :
    ‖cepsBrownianKernel v lam z‖ ≤ cepsBrownianLowerConst v₀ * (1 + |lam| + ‖z‖) ^ 4 *
      Real.exp (-(cepsBrownianDecay v₀ / 3) * (|lam| + Real.sqrt ‖z‖)) := by
  set a := ((lam : ℂ) / v).re
  set s := (cepsBrownianR v lam z / v).re
  set Q := 1 + ‖cepsBrownianR v lam z / v‖
  set X := max 0 (-a - s)
  have hH := cepsBrownianH_norm lam z hv₀ hv hz
  have hU := cepsBrownianU_deriv_norm lam z hv₀ hv hz
  have hP := cepsBrownian_root_polynomial lam z hv₀ hv
  have hConst0 : 0 ≤ cepsBrownianEntranceConst v₀ := by
    unfold cepsBrownianEntranceConst
    have hC : 0 ≤ cepsBrownianSinhcConst := by linarith [cepsBrownianSinhcConst_bounds.1]
    positivity
  have hBridge0 : 0 ≤ cepsBrownianBridgeDerivConst := by unfold cepsBrownianBridgeDerivConst; positivity
  have hExp : Real.exp (2 * X + a - s) ≤ Real.exp (2 / v₀) *
      Real.exp (-(cepsBrownianDecay v₀ / 3) * (|lam| + Real.sqrt ‖z‖)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    simpa only [X, a, s, sub_eq_add_neg, neg_mul] using
      cepsBrownian_lower_exponent hv₀ hv hz hlam.le
  rw [cepsBrownianKernel_of_lt hv₀ hv hz hlam, norm_mul, norm_neg, norm_pow]
  calc
    ‖cepsBrownianH v lam z‖ ^ 2 * ‖deriv (fun u => cepsBrownianU v lam u) z‖ ≤
        (cepsBrownianEntranceConst v₀ * Q * Real.exp X) ^ 2 *
          (cepsBrownianBridgeDerivConst * Q ^ 2 * Real.exp (a - s)) := by gcongr
    _ = cepsBrownianEntranceConst v₀ ^ 2 * cepsBrownianBridgeDerivConst * Q ^ 4 *
        Real.exp (2 * X + a - s) := by
      have he : Real.exp X ^ 2 * Real.exp (a - s) = Real.exp (2 * X + a - s) := by
        rw [pow_two, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      calc
        _ = cepsBrownianEntranceConst v₀ ^ 2 * cepsBrownianBridgeDerivConst * Q ^ 4 *
          (Real.exp X ^ 2 * Real.exp (a - s)) := by ring
        _ = _ := by rw [he]
    _ ≤ cepsBrownianEntranceConst v₀ ^ 2 * cepsBrownianBridgeDerivConst *
        (cepsBrownianRootBudget v₀ * (1 + |lam| + ‖z‖)) ^ 4 *
          (Real.exp (2 / v₀) * Real.exp (-(cepsBrownianDecay v₀ / 3) * (|lam| + Real.sqrt ‖z‖))) := by
      gcongr
    _ = _ := by unfold cepsBrownianLowerConst; ring

end PGM
