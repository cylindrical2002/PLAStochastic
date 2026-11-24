import PLAStochastic.Index.CEPS.BrownianCoeff.EntranceCancellation
import PLAStochastic.Index.CEPS.BrownianCoeff.BridgeCancellation

/-!
# Uniform bounds for the positive-drift cancellations

All constants depend only on the variance centre; the estimates include `z = 0`.
-/

noncomputable section

open Complex

namespace PGM

def cepsBrownianDeltaInverseConst (v₀ : ℝ) : ℝ :=
  (1 - Real.exp (-2 * cepsBrownianDecay v₀))⁻¹

theorem cepsBrownianDeltaInverseConst_pos {v₀ : ℝ} (hv₀ : 0 < v₀) :
    0 < cepsBrownianDeltaInverseConst v₀ := by
  unfold cepsBrownianDeltaInverseConst
  exact inv_pos.mpr (sub_pos.mpr (Real.exp_lt_one_iff.mpr
    (by linarith [cepsBrownianDecay_pos hv₀])))

theorem cepsBrownianDelta_inverse {v₀ : ℝ} {v : ℂ} {lam : ℝ} {z : ℂ}
    (hv₀ : 0 < v₀) (hv : ‖v - (v₀ : ℂ)‖ ≤ cepsBrownianRadius v₀)
    (hz : z.re = 0) (hlam : 1 ≤ lam) :
    ‖(cepsBrownianDelta v lam z)⁻¹‖ ≤ cepsBrownianDeltaInverseConst v₀ := by
  have hc := cepsBrownianDecay_pos hv₀
  have hs := cepsBrownian_quotient_re (lam := lam) hv₀ hv hz
  have hs' : cepsBrownianDecay v₀ ≤ (cepsBrownianR v lam z / v).re := by
    rw [abs_of_pos (by linarith : 0 < lam)] at hs
    nlinarith [Real.sqrt_nonneg ‖z‖]
  have he : ‖Complex.exp (-2 * cepsBrownianR v lam z / v)‖ ≤
      Real.exp (-2 * cepsBrownianDecay v₀) := by
    rw [show -2 * cepsBrownianR v lam z / v = -2 * (cepsBrownianR v lam z / v) by ring,
      Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp
    linarith
  have hbase : 0 < 1 - Real.exp (-2 * cepsBrownianDecay v₀) := by
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hd : 1 - Real.exp (-2 * cepsBrownianDecay v₀) ≤ ‖cepsBrownianDelta v lam z‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (Complex.exp (-2 * cepsBrownianR v lam z / v))
    rw [norm_one] at h
    change 1 - ‖Complex.exp (-2 * cepsBrownianR v lam z / v)‖ ≤
      ‖cepsBrownianDelta v lam z‖ at h
    linarith
  rw [norm_inv, cepsBrownianDeltaInverseConst, ← one_div, ← one_div]
  exact div_le_div_of_nonneg_left zero_le_one hbase hd

theorem cepsBrownian_root_inverse {v₀ : ℝ} {v : ℂ} {lam : ℝ} {z : ℂ}
    (hv₀ : 0 < v₀) (hv : ‖v - (v₀ : ℂ)‖ ≤ cepsBrownianRadius v₀)
    (hz : z.re = 0) (hlam : 1 ≤ lam) :
    ‖v / cepsBrownianR v lam z‖ ≤ (cepsBrownianDecay v₀)⁻¹ := by
  have hc := cepsBrownianDecay_pos hv₀
  have hs := cepsBrownian_quotient_re (lam := lam) hv₀ hv hz
  have hs' : cepsBrownianDecay v₀ ≤ ‖cepsBrownianR v lam z / v‖ := by
    rw [abs_of_pos (by linarith : 0 < lam)] at hs
    have h := Complex.re_le_norm (cepsBrownianR v lam z / v)
    nlinarith [Real.sqrt_nonneg ‖z‖]
  have he : v / cepsBrownianR v lam z = (cepsBrownianR v lam z / v)⁻¹ := by simp
  rw [he, norm_inv, ← one_div, ← one_div]
  exact div_le_div_of_nonneg_left zero_le_one hc hs'

theorem cepsBrownianH_positive_norm {v₀ : ℝ} {v : ℂ} {lam : ℝ} {z : ℂ}
    (hv₀ : 0 < v₀) (hv : ‖v - (v₀ : ℂ)‖ ≤ cepsBrownianRadius v₀)
    (hz : z.re = 0) (hlam : 0 < lam) :
    ‖cepsBrownianH v lam z‖ ≤ cepsBrownianEntranceConst v₀ *
      (1 + ‖cepsBrownianR v lam z / v‖) := by
  have h := cepsBrownianH_norm lam z hv₀ hv hz
  have ha := (cepsBrownian_positive_drift_re hv₀ hv hz hlam).1
  have hs := cepsBrownian_quotient_re_pos hv₀ hv hz (Or.inl hlam.ne')
  rw [max_eq_left (by linarith), Real.exp_zero, mul_one] at h
  exact h

theorem cepsBrownianH_difference_norm {v₀ : ℝ} {v : ℂ} {lam : ℝ} {z : ℂ}
    (hv₀ : 0 < v₀) (hv : ‖v - (v₀ : ℂ)‖ ≤ cepsBrownianRadius v₀)
    (hz : z.re = 0) (hlam : 1 ≤ lam) :
    ‖cepsBrownianH v lam z - cepsBrownianHInf v lam z‖ ≤
      2 * cepsBrownianSinhcConst * (1 + ‖cepsBrownianR v lam z / v‖) *
        Real.exp (-((lam : ℂ) / v).re - (cepsBrownianR v lam z / v).re) := by
  have hvne := (cepsBrownian_variance_bounds hv₀ hv).2.2.2
  have hvpos : 0 < v.re := by linarith [(cepsBrownian_variance_bounds hv₀ hv).1]
  have hAvg := cepsBrownianExpAverage_norm
    (cepsBrownianXiPlus_re_nonneg (lam := lam) hvpos (by linarith) hz)
  have hInf := cepsBrownianHInf_norm (v := v) (z := z) hlam
  have hInv := cepsBrownianSinhc_inverse (cepsBrownian_quotient_sector (lam := lam) hv₀ hv hz)
  have hC : 0 ≤ cepsBrownianSinhcConst := by linarith [cepsBrownianSinhcConst_bounds.1]
  rw [cepsBrownianH_sub_HInf hv₀ hv hz (by linarith), norm_mul, norm_mul, norm_neg,
    norm_div, Complex.norm_exp, ← cepsBrownian_normalized_sq hvne, div_eq_mul_inv]
  simp only [neg_div, neg_re]
  calc
    Real.exp (-((lam : ℂ) / v).re) * ‖cepsBrownianSinhc ((cepsBrownianR v lam z / v) ^ 2)‖⁻¹ *
        ‖cepsBrownianHInf v lam z‖ * ‖cepsBrownianExpAverage (cepsBrownianXiPlus v lam z)‖ ≤
      Real.exp (-((lam : ℂ) / v).re) *
        (cepsBrownianSinhcConst * (1 + ‖cepsBrownianR v lam z / v‖) *
          Real.exp (-(cepsBrownianR v lam z / v).re)) * 2 * 1 := by gcongr
    _ = _ := by simp only [Real.exp_sub, Real.exp_neg]; ring

theorem cepsBrownianUInf_deriv_norm {v₀ : ℝ} {v : ℂ} {lam : ℝ} {z : ℂ}
    (hv₀ : 0 < v₀) (hv : ‖v - (v₀ : ℂ)‖ ≤ cepsBrownianRadius v₀)
    (hz : z.re = 0) (hlam : 1 ≤ lam) :
    ‖deriv (fun u => cepsBrownianUInf v lam u) z‖ ≤
      (1 + (cepsBrownianDecay v₀)⁻¹) *
        Real.exp (((lam : ℂ) / v).re - (cepsBrownianR v lam z / v).re) := by
  have hroot := cepsBrownian_root_inverse hv₀ hv hz hlam
  have hsub : ‖v / cepsBrownianR v lam z - 1‖ ≤ 1 + (cepsBrownianDecay v₀)⁻¹ := by
    have h := norm_sub_le (v / cepsBrownianR v lam z) (1 : ℂ)
    rw [norm_one] at h
    linarith
  rw [(cepsBrownianUInf_hasDerivAt hv₀ hv hz (Or.inl (by linarith : lam ≠ 0))).deriv,
    norm_mul, Complex.norm_exp]
  have he : (-cepsBrownianXiPlus v lam z).re =
      ((lam : ℂ) / v).re - (cepsBrownianR v lam z / v).re := by
    have harg : -cepsBrownianXiPlus v lam z =
        (lam : ℂ) / v - cepsBrownianR v lam z / v := by
      unfold cepsBrownianXiPlus
      ring
    rw [harg, sub_re]
  rw [he, mul_comm]
  exact mul_le_mul_of_nonneg_right hsub (Real.exp_pos _).le

def cepsBrownianBridgeDifferenceConst (v₀ : ℝ) : ℝ :=
  (1 + (cepsBrownianDecay v₀)⁻¹) * cepsBrownianDeltaInverseConst v₀ +
    2 * cepsBrownianDeltaInverseConst v₀ ^ 2

theorem cepsBrownianU_deriv_difference_norm {v₀ : ℝ} {v : ℂ} {lam : ℝ} {z : ℂ}
    (hv₀ : 0 < v₀) (hv : ‖v - (v₀ : ℂ)‖ ≤ cepsBrownianRadius v₀)
    (hz : z.re = 0) (hlam : 1 ≤ lam) :
    ‖deriv (fun u => cepsBrownianU v lam u) z - deriv (fun u => cepsBrownianUInf v lam u) z‖ ≤
      cepsBrownianBridgeDifferenceConst v₀ *
        Real.exp (((lam : ℂ) / v).re - 3 * (cepsBrownianR v lam z / v).re) := by
  have hD := cepsBrownianDelta_inverse hv₀ hv hz hlam
  have hroot := cepsBrownian_root_inverse hv₀ hv hz hlam
  have hsub : ‖v / cepsBrownianR v lam z - 1‖ ≤ 1 + (cepsBrownianDecay v₀)⁻¹ := by
    have h := norm_sub_le (v / cepsBrownianR v lam z) (1 : ℂ)
    rw [norm_one] at h
    linarith
  have hD0 := (cepsBrownianDeltaInverseConst_pos hv₀).le
  have hc0 := (cepsBrownianDecay_pos hv₀).le
  have hr : 0 ≤ 1 + (cepsBrownianDecay v₀)⁻¹ := by positivity
  have hbracket : ‖(v / cepsBrownianR v lam z - 1) / cepsBrownianDelta v lam z -
      2 / cepsBrownianDelta v lam z ^ 2‖ ≤ cepsBrownianBridgeDifferenceConst v₀ := by
    calc
      _ ≤ ‖(v / cepsBrownianR v lam z - 1) / cepsBrownianDelta v lam z‖ +
          ‖2 / cepsBrownianDelta v lam z ^ 2‖ := norm_sub_le _ _
      _ = ‖v / cepsBrownianR v lam z - 1‖ * ‖(cepsBrownianDelta v lam z)⁻¹‖ +
          2 * ‖(cepsBrownianDelta v lam z)⁻¹‖ ^ 2 := by
        simp [norm_pow, norm_inv, div_eq_mul_inv, inv_pow]
      _ ≤ _ := by unfold cepsBrownianBridgeDifferenceConst; gcongr
  rw [cepsBrownianU_deriv_sub_UInf_deriv hv₀ hv hz (by linarith), norm_mul, norm_mul,
    Complex.norm_exp, Complex.norm_exp]
  have he : (-cepsBrownianXiPlus v lam z).re =
      ((lam : ℂ) / v).re - (cepsBrownianR v lam z / v).re := by
    have harg : -cepsBrownianXiPlus v lam z =
        (lam : ℂ) / v - cepsBrownianR v lam z / v := by
      unfold cepsBrownianXiPlus
      ring
    rw [harg, sub_re]
  have he2 : (-2 * cepsBrownianR v lam z / v).re =
      -2 * (cepsBrownianR v lam z / v).re := by
    rw [show -2 * cepsBrownianR v lam z / v = -2 * (cepsBrownianR v lam z / v) by ring]
    simp
  rw [he, he2]
  calc
    _ ≤ Real.exp (((lam : ℂ) / v).re - (cepsBrownianR v lam z / v).re) *
        Real.exp (-2 * (cepsBrownianR v lam z / v).re) *
          cepsBrownianBridgeDifferenceConst v₀ := by gcongr
    _ = _ := by
      rw [← Real.exp_add, mul_comm]
      congr 1
      congr 1
      ring

end PGM
