import PLAStochastic.ForMathlib.Probability.Hellinger.Reparametrization
import PLAStochastic.ForMathlib.Probability.Distributions.LogExponential

/-!
# Quantitative square-root estimates for exponential transports

The exponential difference is controlled by the smaller argument and the true
Jacobian error by its difference from one. These estimates retain an exponential
envelope instead of replacing Hellinger distance by the square root of variation.
-/

set_option autoImplicit false

namespace ProbabilityTheory

noncomputable section

open MeasureTheory Set

private theorem exp_neg_half_sub_le_of_le {u v l : ℝ} (huv : u ≤ v) (hlu : l ≤ u) :
    |Real.exp (-u / 2) - Real.exp (-v / 2)| ≤ |u - v| / 2 * Real.exp (-l / 2) := by
  have hsmall : 1 - Real.exp (-(v - u) / 2) ≤ (v - u) / 2 := by
    have h := Real.add_one_le_exp (-(v - u) / 2)
    linarith only [h]
  have he : Real.exp (-u / 2) * (1 - Real.exp (-(v - u) / 2)) =
      Real.exp (-u / 2) - Real.exp (-v / 2) := by
    rw [mul_sub, mul_one, ← Real.exp_add]
    congr 1
    congr 1
    ring
  have hnon : 0 ≤ Real.exp (-u / 2) - Real.exp (-v / 2) :=
    sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith only [huv]))
  rw [abs_of_nonneg hnon, ← he, abs_sub_comm u v, abs_of_nonneg (sub_nonneg.mpr huv)]
  calc
    _ ≤ Real.exp (-u / 2) * ((v - u) / 2) :=
      mul_le_mul_of_nonneg_left hsmall (Real.exp_pos _).le
    _ ≤ Real.exp (-l / 2) * ((v - u) / 2) :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith only [hlu])) (by positivity)
    _ = _ := by ring

theorem abs_exp_neg_half_sub_le {u v l : ℝ} (hlu : l ≤ u) (hlv : l ≤ v) :
    |Real.exp (-u / 2) - Real.exp (-v / 2)| ≤ |u - v| / 2 * Real.exp (-l / 2) := by
  rcases le_total u v with huv | hvu
  · exact exp_neg_half_sub_le_of_le huv hlu
  · have h := exp_neg_half_sub_le_of_le hvu hlv
    simpa only [abs_sub_comm] using h

theorem abs_sqrt_sub_one_le {d : ℝ} (hd : 0 ≤ d) : |Real.sqrt d - 1| ≤ |d - 1| := by
  have hs := Real.sq_sqrt hd
  have hs0 := Real.sqrt_nonneg d
  have he : (Real.sqrt d - 1) * (Real.sqrt d + 1) = d - 1 := by nlinarith only [hs]
  have hnorm : |Real.sqrt d - 1| * (Real.sqrt d + 1) = |d - 1| := by
    rw [← abs_of_nonneg (by linarith only [hs0] : 0 ≤ Real.sqrt d + 1), ← abs_mul, he]
  calc
    _ ≤ |Real.sqrt d - 1| * (Real.sqrt d + 1) :=
      le_mul_of_one_le_right (abs_nonneg _) (by linarith only [hs0])
    _ = _ := hnorm

theorem exponential_jacobian_root_difference_le {t u d l : ℝ}
    (hd : 0 ≤ d) (hlt : l ≤ t) (hlu : l ≤ u) :
    |Real.exp (-t / 2) - Real.sqrt d * Real.exp (-u / 2)| ≤
      (|t - u| / 2 + |d - 1|) * Real.exp (-l / 2) := by
  have hroot : |Real.exp (-u / 2) - Real.sqrt d * Real.exp (-u / 2)| ≤
      |d - 1| * Real.exp (-l / 2) := by
    rw [show Real.exp (-u / 2) - Real.sqrt d * Real.exp (-u / 2) =
      (1 - Real.sqrt d) * Real.exp (-u / 2) by ring, abs_mul,
      abs_of_pos (Real.exp_pos _), abs_sub_comm 1 (Real.sqrt d)]
    apply mul_le_mul (abs_sqrt_sub_one_le hd)
      (Real.exp_le_exp.mpr (by linarith only [hlu])) (Real.exp_pos _).le (abs_nonneg _)
  calc
    _ ≤ |Real.exp (-t / 2) - Real.exp (-u / 2)| +
        |Real.exp (-u / 2) - Real.sqrt d * Real.exp (-u / 2)| := abs_sub_le _ _ _
    _ ≤ |t - u| / 2 * Real.exp (-l / 2) + |d - 1| * Real.exp (-l / 2) :=
      add_le_add (abs_exp_neg_half_sub_le hlt hlu) hroot
    _ = _ := by ring

end

end ProbabilityTheory
