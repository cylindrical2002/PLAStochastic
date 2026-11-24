import PLAStochastic.Index.CEPS.Scaled.TruePairScaling

/-! # Coarse frequency budgets for the complete scaled time pair -/

noncomputable section
open Complex
namespace PGM

theorem cepsNorm_completeTimePair_frequency_bound {b lam r X A K L : ℝ}
    {z H U U' : ℂ} (hb : 0 < b) (hb1 : b ≤ 1)
    (hwlo : 1 / 2 ≤ 1 + b * lam) (hwhi : 1 + b * lam ≤ 2)
    (hz : ‖z‖ ≤ r)
    (hH : ‖H‖ ≤ A / b) (hU : ‖U‖ ≤ K * X) (hU' : ‖U'‖ ≤ L * X) :
    ‖exp (((b : ℂ) * z) * (1 + (b : ℂ) * lam)) * H ^ 2 *
        (-(1 / (1 + (b : ℂ) * lam)) * U' - (b : ℂ) * U)‖ ≤
      Real.exp (2 * r) * A ^ 2 * (2 * L + K) / b ^ 2 * X := by
  have hw : 0 < 1 + b * lam := by linarith
  have hwr : (1 : ℂ) + (b : ℂ) * lam = ((1 + b * lam : ℝ) : ℂ) := by push_cast; rfl
  have hwn : ‖(1 : ℂ) + (b : ℂ) * lam‖ = 1 + b * lam := by
    rw [hwr, norm_real, Real.norm_eq_abs, abs_of_pos hw]
  have hi : ‖(1 : ℂ) / (1 + (b : ℂ) * lam)‖ ≤ 2 := by
    rw [norm_div, norm_one, hwn]
    exact (div_le_iff₀ hw).mpr (by linarith)
  have he : ‖exp (((b : ℂ) * z) * (1 + (b : ℂ) * lam))‖ ≤ Real.exp (2 * r) := by
    rw [norm_exp]
    apply Real.exp_le_exp.mpr
    apply (re_le_norm _).trans
    rw [norm_mul, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hb, hwn]
    calc
      _ ≤ 1 * ‖z‖ * 2 := by gcongr
      _ ≤ 2 * r := by linarith
  have ho : ‖-(1 / (1 + (b : ℂ) * lam)) * U' - (b : ℂ) * U‖ ≤ (2 * L + K) * X := by
    calc
      _ ≤ ‖-(1 / (1 + (b : ℂ) * lam)) * U'‖ + ‖(b : ℂ) * U‖ := norm_sub_le _ _
      _ = ‖(1 : ℂ) / (1 + (b : ℂ) * lam)‖ * ‖U'‖ + b * ‖U‖ := by
        rw [norm_mul, norm_mul, norm_neg, norm_real, Real.norm_eq_abs, abs_of_pos hb]
      _ ≤ 2 * (L * X) + 1 * (K * X) := by gcongr
      _ = _ := by ring
  calc
    _ = ‖exp (((b : ℂ) * z) * (1 + (b : ℂ) * lam))‖ * ‖H‖ ^ 2 *
        ‖-(1 / (1 + (b : ℂ) * lam)) * U' - (b : ℂ) * U‖ := by rw [norm_mul, norm_mul, norm_pow]
    _ ≤ Real.exp (2 * r) * (A / b) ^ 2 * ((2 * L + K) * X) := by gcongr
    _ = _ := by ring

end PGM
