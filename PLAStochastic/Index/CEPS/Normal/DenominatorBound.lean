import PLAStochastic.Index.CEPS.Normal.Defs

/-! # Quantitative lower bound for the normal two-passage denominator -/

noncomputable section
open Complex
namespace PGM

private theorem normal_exp_gap {x : ℝ} (hx : 0 ≤ x) :
    min 1 x / 2 ≤ 1 - Real.exp (-x) := by
  have he := Real.exp_pos x
  have hl := Real.add_one_le_exp x
  rw [Real.exp_neg]
  by_cases h : x ≤ 1
  · rw [min_eq_right h]
    apply (le_sub_iff_add_le).2
    apply (le_of_mul_le_mul_right ?_ he)
    have hmul : (2 - x) * (Real.exp x - (x + 1)) ≥ 0 :=
      mul_nonneg (by linarith) (by linarith)
    have hxx := mul_nonneg hx (sub_nonneg.mpr h)
    field_simp
    nlinarith
  · rw [min_eq_left (le_of_not_ge h)]
    have h2 : 2 ≤ Real.exp x := by linarith
    apply (le_sub_iff_add_le).2
    apply (le_of_mul_le_mul_right ?_ he)
    field_simp
    nlinarith

/-- This is the C-7 denominator estimate from a root-sector bound and a
first-order factor bound. The conclusion is not an input hypothesis.

The constant is explicit: `c / 4`, with `0 < c ≤ 1`, and a sufficient width
condition is `2 C ≤ c l`. The value `R = 0` is included.
-/
theorem cepsNormal_delta_lower_bound {η P : ℂ} {l R c C : ℝ}
    (hl : 0 ≤ l) (hR : 0 ≤ R) (hc : 0 < c) (hc1 : c ≤ 1) (_hC : 0 ≤ C)
    (hsector : c * R ≤ η.re) (hfactor : ‖P - 1‖ ≤ C * R)
    (hwidth : 2 * C ≤ c * l) :
    c / 4 * min 1 (R * l) ≤ ‖1 - exp (-η * (l : ℂ)) * P‖ := by
  let x := η.re * l
  have hx : 0 ≤ x := mul_nonneg (le_trans (mul_nonneg hc.le hR) hsector) hl
  have hxy : c * (R * l) ≤ x := by
    dsimp [x]
    nlinarith [mul_nonneg (sub_nonneg.mpr hsector) hl]
  have hCR : 2 * C * R ≤ x := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hwidth) hR]
  have hnorm : ‖exp (-η * (l : ℂ))‖ = Real.exp (-x) := by
    rw [Complex.norm_exp]
    congr 1
    simp [x]
  have hpi : ‖P‖ ≤ 1 + C * R := by
    calc
      ‖P‖ = ‖(P - 1) + 1‖ := by congr 1; ring
      _ ≤ ‖P - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 1 + C * R := by rw [norm_one]; linarith
  have hexp := Real.exp_pos (-x)
  have hxgap : x * Real.exp (-x) ≤ 1 - Real.exp (-x) := by
    have h := Real.add_one_le_exp x
    have he := Real.exp_pos x
    rw [Real.exp_neg]
    apply (le_sub_iff_add_le).2
    apply (le_of_mul_le_mul_right ?_ he)
    field_simp
    linarith
  have hnormlow := norm_sub_norm_le (1 : ℂ) (exp (-η * (l : ℂ)) * P)
  rw [norm_one, norm_mul, hnorm] at hnormlow
  have hmul := mul_le_mul_of_nonneg_left hpi hexp.le
  have hsmall : Real.exp (-x) * (C * R) ≤ (1 - Real.exp (-x)) / 2 := by
    nlinarith [mul_nonneg hexp.le (sub_nonneg.mpr hCR)]
  have hhalf : (1 - Real.exp (-x)) / 2 ≤ ‖1 - exp (-η * (l : ℂ)) * P‖ := by
    nlinarith
  have hmin : c * min 1 (R * l) ≤ min 1 x := by
    apply le_min
    · have hm : min 1 (R * l) ≤ 1 := min_le_left _ _
      have hn : 0 ≤ min 1 (R * l) := le_min (by norm_num) (mul_nonneg hR hl)
      nlinarith
    · exact le_trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hc.le) hxy
  have hgap := normal_exp_gap hx
  nlinarith

end PGM
