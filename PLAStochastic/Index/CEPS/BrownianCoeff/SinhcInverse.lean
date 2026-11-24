import PLAStochastic.Index.CEPS.BrownianCoeff.SinhcBounds

/-!
# A quantitative reciprocal-sinhc estimate in a fixed sector

The small-root region is paid for by a Taylor bound. Outside that region the real
part of the root separates the exponential denominator from zero.
-/

noncomputable section

open Complex

namespace PGM

def cepsBrownianSinhcConst : ℝ := 6 + 2 / (1 - Real.exp (-1 / 12))

theorem cepsBrownianSinhcConst_bounds : 6 ≤ cepsBrownianSinhcConst ∧
    2 / (1 - Real.exp (-1 / 12)) ≤ cepsBrownianSinhcConst := by
  have hd : 0 < 1 - Real.exp (-1 / 12) := by
    have := Real.exp_lt_one_iff.mpr (by norm_num : (-1 / 12 : ℝ) < 0)
    linarith
  unfold cepsBrownianSinhcConst
  constructor
  · have hp : 0 ≤ 2 / (1 - Real.exp (-1 / 12)) := by positivity
    linarith
  · linarith

private theorem delta_sinhc (s : ℂ) :
    2 * Complex.exp (-s) * s * cepsBrownianSinhc (s ^ 2) = 1 - Complex.exp (-2 * s) := by
  rw [show 2 * Complex.exp (-s) * s * cepsBrownianSinhc (s ^ 2) =
    Complex.exp (-s) * (2 * (s * cepsBrownianSinhc (s ^ 2))) by ring,
    cepsBrownianSinhc_mul, Complex.two_sinh, mul_sub, ← Complex.exp_add,
    neg_add_cancel, Complex.exp_zero, ← Complex.exp_add]
  congr 2
  ring

theorem cepsBrownianSinhc_sector_ne {s : ℂ} (hs : ‖s‖ ≤ 3 * s.re) :
    cepsBrownianSinhc (s ^ 2) ≠ 0 := by
  by_cases hs0 : s = 0
  · simp [hs0]
  · have hp : 0 < s.re := by have := norm_pos_iff.mpr hs0; linarith
    have he : ‖Complex.exp (-2 * s)‖ < 1 := by
      rw [Complex.norm_exp]
      apply Real.exp_lt_one_iff.mpr
      simpa using (show -2 * s.re < 0 by linarith)
    intro hzero
    have heq := delta_sinhc s
    rw [hzero, mul_zero] at heq
    have hone : Complex.exp (-2 * s) = 1 := (sub_eq_zero.mp heq.symm).symm
    rw [hone, norm_one] at he
    exact (lt_irrefl 1) he

theorem cepsBrownianSinhc_inverse {s : ℂ} (hs : ‖s‖ ≤ 3 * s.re) :
    ‖cepsBrownianSinhc (s ^ 2)‖⁻¹ ≤ cepsBrownianSinhcConst * (1 + ‖s‖) * Real.exp (-s.re) := by
  have hsre : 0 ≤ s.re := by linarith [norm_nonneg s]
  have hC := cepsBrownianSinhcConst_bounds.1
  have hC0 : 0 ≤ cepsBrownianSinhcConst := by linarith
  have hSpos := norm_pos_iff.mpr (cepsBrownianSinhc_sector_ne hs)
  by_cases hsmall : ‖s‖ ≤ 1 / 8
  · have hS : 1 / 2 ≤ ‖cepsBrownianSinhc (s ^ 2)‖ := by
      have ht := norm_sub_norm_le (1 : ℂ) (cepsBrownianSinhc (s ^ 2))
      rw [norm_one, norm_sub_rev] at ht
      have hd := cepsBrownianSinhc_sub_one s hsmall
      linarith
    have hinv : ‖cepsBrownianSinhc (s ^ 2)‖⁻¹ ≤ 2 := by
      rw [inv_eq_one_div, div_le_iff₀ hSpos]
      linarith
    have hexp : Real.exp s.re ≤ 3 := by
      have hres := Complex.re_le_norm s
      exact (Real.exp_le_exp.mpr (by linarith : s.re ≤ 1)).trans Real.exp_one_lt_three.le
    have hscaled : ‖cepsBrownianSinhc (s ^ 2)‖⁻¹ * Real.exp s.re ≤
        cepsBrownianSinhcConst * (1 + ‖s‖) := by
      have hi0 : 0 ≤ ‖cepsBrownianSinhc (s ^ 2)‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
      have he0 := (Real.exp_pos s.re).le
      nlinarith [norm_nonneg s]
    calc
      ‖cepsBrownianSinhc (s ^ 2)‖⁻¹ =
          (‖cepsBrownianSinhc (s ^ 2)‖⁻¹ * Real.exp s.re) * Real.exp (-s.re) := by
        rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
      _ ≤ cepsBrownianSinhcConst * (1 + ‖s‖) * Real.exp (-s.re) := by gcongr
  · let d : ℝ := 1 - Real.exp (-1 / 12)
    have hd : 0 < d := by
      have := Real.exp_lt_one_iff.mpr (by norm_num : (-1 / 12 : ℝ) < 0)
      dsimp [d]
      linarith
    have hres : 1 / 24 ≤ s.re := by linarith
    have he : Real.exp (-2 * s.re) ≤ Real.exp (-1 / 12) := Real.exp_le_exp.mpr (by linarith)
    have hdelta : d ≤ ‖1 - Complex.exp (-2 * s)‖ := by
      have ht := norm_sub_norm_le (1 : ℂ) (Complex.exp (-2 * s))
      rw [norm_one, Complex.norm_exp] at ht
      have hre : (-2 * s).re = -2 * s.re := by simp
      rw [hre] at ht
      dsimp [d]
      linarith
    have hnorm : ‖1 - Complex.exp (-2 * s)‖ =
        2 * Real.exp (-s.re) * ‖s‖ * ‖cepsBrownianSinhc (s ^ 2)‖ := by
      rw [← delta_sinhc, norm_mul, norm_mul, norm_mul, Complex.norm_ofNat,
        Complex.norm_exp, neg_re]
    rw [hnorm] at hdelta
    have hinv : ‖cepsBrownianSinhc (s ^ 2)‖⁻¹ ≤ 2 * ‖s‖ * Real.exp (-s.re) / d := by
      rw [inv_eq_one_div, div_le_div_iff₀ hSpos hd]
      nlinarith [hdelta]
    have hCd : 2 / d ≤ cepsBrownianSinhcConst := cepsBrownianSinhcConst_bounds.2
    calc
      ‖cepsBrownianSinhc (s ^ 2)‖⁻¹ ≤ 2 * ‖s‖ * Real.exp (-s.re) / d := hinv
      _ = (2 / d) * ‖s‖ * Real.exp (-s.re) := by ring
      _ ≤ cepsBrownianSinhcConst * (1 + ‖s‖) * Real.exp (-s.re) := by gcongr; linarith

end PGM
