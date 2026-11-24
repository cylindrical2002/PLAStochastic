import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Basic

/-! # Exponential bookkeeping for a subtracted entrance-square bridge -/

noncomputable section
open Complex
namespace PGM

private theorem exp_weighted_square_le {p m t d : ℝ}
    (h₁ : d ≤ p - t) (h₂ : d ≤ p - 2 * m + t) :
    Real.exp t * (2 + Real.exp (m - t)) ^ 2 * Real.exp (-p) ≤ 10 * Real.exp (-d) := by
  have hs : (2 + Real.exp (m - t)) ^ 2 ≤ 8 + 2 * (Real.exp (m - t)) ^ 2 := by
    nlinarith [sq_nonneg (Real.exp (m - t) - 2)]
  have he₁ : Real.exp (t - p) ≤ Real.exp (-d) := Real.exp_le_exp.mpr (by linarith)
  have he₂ : Real.exp (2 * m - t - p) ≤ Real.exp (-d) := Real.exp_le_exp.mpr (by linarith)
  calc
    _ ≤ Real.exp t * (8 + 2 * (Real.exp (m - t)) ^ 2) * Real.exp (-p) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le) (Real.exp_pos _).le
    _ = 8 * Real.exp (t - p) + 2 * Real.exp (2 * m - t - p) := by
      rw [pow_two]
      have he : Real.exp t * (Real.exp (m - t) * Real.exp (m - t)) * Real.exp (-p) =
          Real.exp (2 * m - t - p) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      have he' : Real.exp t * Real.exp (-p) = Real.exp (t - p) := by
        rw [← Real.exp_add, sub_eq_add_neg]
      linear_combination 2 * he + 8 * he'
    _ ≤ _ := by linarith

theorem cepsNorm_weighted_square_bridge_le {H U E : ℂ} {AH AU p m t d : ℝ}
    (hAU : 0 ≤ AU) (hE : ‖E‖ ≤ Real.exp t)
    (hH : ‖H‖ ≤ AH * (2 + Real.exp (m - t))) (hU : ‖U‖ ≤ AU * Real.exp (-p))
    (hdir₁ : d ≤ p - t) (hdir₂ : d ≤ p - 2 * m + t) :
    ‖E * H ^ 2 * U‖ ≤ 10 * AH ^ 2 * AU * Real.exp (-d) := by
  rw [norm_mul, norm_mul, norm_pow]
  apply (mul_le_mul (mul_le_mul hE (pow_le_pow_left₀ (norm_nonneg _) hH 2)
    (sq_nonneg _) (Real.exp_pos _).le) hU (norm_nonneg _) (by positivity)).trans
  have hh := mul_le_mul_of_nonneg_left (exp_weighted_square_le hdir₁ hdir₂)
    (mul_nonneg (sq_nonneg AH) hAU)
  convert hh using 1 <;> ring

private theorem exp_correction_product_le {p m t d : ℝ}
    (h₁ : d ≤ 2 * p - m - t) (h₂ : d ≤ p - m) :
    Real.exp t * (Real.exp (m - p) + Real.exp (m - t)) * Real.exp (-p) ≤
      2 * Real.exp (-d) := by
  have he : Real.exp t * (Real.exp (m - p) + Real.exp (m - t)) * Real.exp (-p) =
      Real.exp (-(2 * p - m - t)) + Real.exp (-(p - m)) := by
    rw [mul_add, add_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1 <;> congr 1 <;> ring
  rw [he]
  linarith [Real.exp_le_exp.mpr (neg_le_neg h₁), Real.exp_le_exp.mpr (neg_le_neg h₂)]

theorem cepsNorm_weighted_square_subtraction_le {H Hh U Uh E : ℂ}
    {AH Ah AC AU AUh p m t d : ℝ}
    (hAH : 0 ≤ AH) (hAh : 0 ≤ Ah) (hAC : 0 ≤ AC) (hAU : 0 ≤ AU) (hAUh : 0 ≤ AUh)
    (hH : ‖H‖ ≤ AH) (hHalf : ‖Hh‖ ≤ Ah) (hE : ‖E‖ ≤ Real.exp t)
    (hCorr : ‖H - Hh‖ ≤ AC * (Real.exp (m - p) + Real.exp (m - t)))
    (hUc : ‖U - Uh‖ ≤ AU * Real.exp (-(2 * p - m)))
    (hUh : ‖Uh‖ ≤ AUh * Real.exp (-p))
    (hdir₁ : d ≤ 2 * p - m - t) (hdir₂ : d ≤ p - m) :
    ‖E * (H ^ 2 * U - Hh ^ 2 * Uh)‖ ≤
      (AH ^ 2 * AU + 2 * AC * (AH + Ah) * AUh) * Real.exp (-d) := by
  have he : E * (H ^ 2 * U - Hh ^ 2 * Uh) =
      E * H ^ 2 * (U - Uh) + E * (H - Hh) * (H + Hh) * Uh := by ring
  have hs : ‖H + Hh‖ ≤ AH + Ah := (norm_add_le _ _).trans (add_le_add hH hHalf)
  have hdec₁ : Real.exp t * Real.exp (-(2 * p - m)) ≤ Real.exp (-d) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hdec₂ := exp_correction_product_le hdir₁ hdir₂
  have ht₁ : ‖E * H ^ 2 * (U - Uh)‖ ≤ AH ^ 2 * AU * Real.exp (-d) := by
    rw [norm_mul, norm_mul, norm_pow]
    apply (mul_le_mul (mul_le_mul hE (pow_le_pow_left₀ (norm_nonneg _) hH 2)
      (sq_nonneg _) (Real.exp_pos _).le) hUc (norm_nonneg _) (by positivity)).trans
    have hh := mul_le_mul_of_nonneg_left hdec₁ (mul_nonneg (sq_nonneg AH) hAU)
    convert hh using 1
    ring
  have ht₂ : ‖E * (H - Hh) * (H + Hh) * Uh‖ ≤
      2 * AC * (AH + Ah) * AUh * Real.exp (-d) := by
    rw [norm_mul, norm_mul, norm_mul]
    apply (mul_le_mul (mul_le_mul (mul_le_mul hE hCorr (norm_nonneg _) (Real.exp_pos _).le)
      hs (norm_nonneg _) (by positivity)) hUh (norm_nonneg _) (by positivity)).trans
    have hh := mul_le_mul_of_nonneg_left hdec₂ (mul_nonneg (mul_nonneg hAC (add_nonneg hAH hAh)) hAUh)
    convert hh using 1 <;> ring
  rw [he]
  exact ((norm_add_le _ _).trans (add_le_add ht₁ ht₂)).trans_eq (by ring)

end PGM
