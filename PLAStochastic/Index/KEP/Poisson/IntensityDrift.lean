import PLAStochastic.Index.KEP.Poisson.Intensity
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Actual logarithmic intensity drift in fixed parent units

Positivity and the original Lipschitz bound control the logarithmic density
ratio at every state. Normalization by the reference physical scale introduces
exactly the reference span divided by the Poisson intensity.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory Set

private theorem kep_log_difference_le_of_le {a b flo : ℝ}
    (hlo : 0 < flo) (hla : flo ≤ a) (hab : a ≤ b) :
    Real.log b - Real.log a ≤ (b - a) / flo := by
  have ha : 0 < a := hlo.trans_le hla
  have hb : 0 < b := ha.trans_le hab
  calc
    _ = Real.log (b / a) := (Real.log_div hb.ne' ha.ne').symm
    _ ≤ b / a - 1 := Real.log_le_sub_one_of_pos (div_pos hb ha)
    _ = (b - a) / a := by field_simp [ha.ne']
    _ ≤ _ := div_le_div_of_nonneg_left (sub_nonneg.mpr hab) hlo hla

theorem KepIntensityProfile.log_difference_le {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (x y : ℝ) :
    |Real.log (f x) - Real.log (f y)| ≤ (L / flo) * |x - y| := by
  have hnum : |f x - f y| ≤ L * |x - y| := hf.lip x y
  have hlog : |Real.log (f x) - Real.log (f y)| ≤ |f x - f y| / flo := by
    rcases le_total (f x) (f y) with hxy | hyx
    · have hl : Real.log (f x) ≤ Real.log (f y) := Real.log_le_log (hf.f_pos x) hxy
      rw [abs_sub_comm (Real.log (f x)) (Real.log (f y)), abs_of_nonneg (sub_nonneg.mpr hl),
        abs_sub_comm (f x) (f y), abs_of_nonneg (sub_nonneg.mpr hxy)]
      exact kep_log_difference_le_of_le hf.pos (hf.lower x) hxy
    · have hl : Real.log (f y) ≤ Real.log (f x) := Real.log_le_log (hf.f_pos y) hyx
      rw [abs_of_nonneg (sub_nonneg.mpr hl), abs_of_nonneg (sub_nonneg.mpr hyx)]
      exact kep_log_difference_le_of_le hf.pos (hf.lower y) hyx
  calc
    _ ≤ |f x - f y| / flo := hlog
    _ ≤ (L * |x - y|) / flo := div_le_div_of_nonneg_right hnum hf.pos.le
    _ = _ := by ring

theorem kepPoisson_log_state_drift {f : ℝ → ℝ} {flo fhi L n m S : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hn : 0 < n)
    (hm : 0 ≤ m) (hS : 0 ≤ S) (x : ℝ) :
    |Real.log (f x / f (x + (m / (n * f x)) * S))| ≤
      (L / flo ^ 2) * (m / n) * S := by
  have hlo := hf.pos
  have hfx := hf.f_pos x
  have hL := hf.lip_nonneg
  have hell : 0 ≤ m / (n * f x) := by positivity
  have h := hf.log_difference_le x (x + (m / (n * f x)) * S)
  rw [Real.log_div hfx.ne' (hf.f_pos _).ne']
  apply h.trans
  rw [abs_sub_comm x _, add_sub_cancel_left, abs_of_nonneg (mul_nonneg hell hS)]
  have hb : m / (n * f x) ≤ m / (n * flo) :=
    div_le_div_of_nonneg_left hm (mul_pos hn hlo)
      (mul_le_mul_of_nonneg_left (hf.lower x) hn.le)
  calc
    _ ≤ (L / flo) * ((m / (n * flo)) * S) := by gcongr
    _ = _ := by field_simp [hn.ne', hlo.ne']

end

end PGM
