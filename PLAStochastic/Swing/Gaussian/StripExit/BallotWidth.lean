import PLAStochastic.Swing.Gaussian.StripExit.Estimates

/-! # Strip-width selection for the discrete Gaussian survival estimate -/
noncomputable section
namespace SwingRepair
open scoped NNReal ENNReal
set_option backward.isDefEq.respectTransparency false

def gaussianBallotWidth (a : ℝ) (n : ℕ) : ℝ :=
  if a = 0 then Real.sqrt (n : ℝ) else min (Real.sqrt (n : ℝ)) (1/(2*a))

theorem gaussianBallotWidth_bounds {a : ℝ} {n : ℕ}
    (ha : 0 ≤ a) (ha' : a ≤ 1/2) (hn : 0 < n) :
    1 ≤ gaussianBallotWidth a n ∧ a*gaussianBallotWidth a n ≤ 1/2 ∧
      (gaussianBallotWidth a n)⁻¹ ≤ 2*a+(Real.sqrt (n : ℝ))⁻¹ ∧
      gaussianBallotWidth a n / (n : ℝ) ≤ (Real.sqrt (n : ℝ))⁻¹ := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by positivity
  have hs : 1 ≤ Real.sqrt (n : ℝ) := by
    have hh := Real.sqrt_le_sqrt hn1
    simpa only [Real.sqrt_one] using hh
  have hs0 : 0 < Real.sqrt (n : ℝ) := by positivity
  have hsq := Real.sq_sqrt hn0.le
  have hratio : Real.sqrt (n : ℝ)/(n : ℝ) = (Real.sqrt (n : ℝ))⁻¹ := by
    apply (div_eq_iff hn0.ne').mpr
    field_simp
    nlinarith
  by_cases ha0 : a = 0
  · subst a
    simp only [gaussianBallotWidth, zero_mul, mul_zero, zero_add]
    exact ⟨hs, by norm_num, le_rfl, hratio.le⟩
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hc : 0 < 2*a := by positivity
    have hc1 : 1 ≤ 1/(2*a) := (le_div_iff₀ hc).mpr (by linarith)
    have hm0 : 0 < min (Real.sqrt (n : ℝ)) (1/(2*a)) := lt_min hs0 (by positivity)
    simp only [gaussianBallotWidth, if_neg ha0]
    refine ⟨le_min hs hc1, ?_, ?_, ?_⟩
    · calc
        a * min (Real.sqrt (n : ℝ)) (1/(2*a)) ≤ a*(1/(2*a)) := mul_le_mul_of_nonneg_left (min_le_right _ _) ha
        _ = 1/2 := by field_simp
    · by_cases hm : Real.sqrt (n : ℝ) ≤ 1/(2*a)
      · rw [min_eq_left hm]
        linarith
      · rw [min_eq_right (le_of_not_ge hm)]
        have he : (1/(2*a))⁻¹ = 2*a := by simp
        rw [he]
        exact le_add_of_nonneg_right (inv_nonneg.mpr hs0.le)
    · exact (div_le_div_of_nonneg_right (min_le_left _ _) hn0.le).trans_eq hratio

end SwingRepair
