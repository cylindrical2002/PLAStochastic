import PLAStochastic.Index.GEP.StrongApprox.Saddle.RateTaylor
import PLAStochastic.Index.GEP.LayerLaw.WeightedDistance

/-! # WP5: logarithmic control of the saddle variance prefactor -/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory

def saLogVarianceConstant (vlo B θ : ℝ) : ℝ :=
  16 * saCumulantThird B θ / (9 * vlo ^ 2)

theorem saLogVarianceConstant_pos {vlo B θ : ℝ} (hvlo : 0 < vlo) (hθ : 0 < θ) :
    0 < saLogVarianceConstant vlo B θ := by
  unfold saLogVarianceConstant
  have := saCumulantThird_pos B hθ
  positivity

variable {vlo vhi κ₃ B θ : ℝ} {ν : ProbabilityMeasure ℝ}

/-- The logarithm of the smoothed tilted variance is uniformly Lipschitz in the
tilt, using the actual second cumulant derivative. -/
theorem UnivClass.log_saSmoothCGF_variance_sub_zero (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) {lam : ℝ}
    (hlam : |lam| ≤ saTiltRadius vlo B θ) (s : ℝ) :
    |Real.log (iteratedDeriv 2 (saSmoothCGF ν s) lam) - Real.log (lawVar ν + s ^ 2)| ≤
      (4 * saCumulantThird B θ / (3 * vlo)) * |lam| := by
  have hl := hlam.trans (saTiltRadius_le_half vlo B hθ)
  have hv := (h.saSmoothCGF_variance_bracket hvlo hθ hlam s).1
  have hvar := h.var_ge
  have hb := abs_log_sub_log_le (by positivity : 0 < 3 / 4 * vlo)
    (show 3 / 4 * vlo ≤ iteratedDeriv 2 (saSmoothCGF ν s) lam by nlinarith [sq_nonneg s])
    (show 3 / 4 * vlo ≤ lawVar ν + s ^ 2 by nlinarith [sq_nonneg s])
  have hd := h.iteratedDeriv_two_centered_cgf_sub_var_le hθ hl
  rw [h.iteratedDeriv_two_saSmoothCGF (hl.trans_lt (by linarith)) s,
    add_sub_add_right_eq_sub] at hb
  rw [h.iteratedDeriv_two_saSmoothCGF (hl.trans_lt (by linarith)) s]
  calc
    _ ≤ (saCumulantThird B θ * |lam|) / (3 / 4 * vlo) :=
      hb.trans (div_le_div_of_nonneg_right hd (by positivity))
    _ = _ := by field_simp

/-- At the saddle, the logarithmic variance error is linear in the target mean. -/
theorem UnivClass.log_saSaddle_variance_sub_zero (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) (s : ℝ) {w : ℝ}
    (hw : |w| ≤ saMeanRadius vlo B θ) :
    |Real.log (iteratedDeriv 2 (saSmoothCGF ν s) (saSaddle vlo B θ ν s w)) -
        Real.log (lawVar ν + s ^ 2)| ≤ saLogVarianceConstant vlo B θ * |w| := by
  have hw' := hw.trans (saMeanRadius_lt_full hvlo hθ).le
  have hlam := abs_le.mpr (h.saSaddle_spec hvlo hθ s hw').1
  have hc := saCumulantThird_pos B hθ
  calc
    _ ≤ (4 * saCumulantThird B θ / (3 * vlo)) * |saSaddle vlo B θ ν s w| :=
      h.log_saSmoothCGF_variance_sub_zero hvlo hθ hlam s
    _ ≤ (4 * saCumulantThird B θ / (3 * vlo)) * (4 / (3 * vlo) * |w|) :=
      mul_le_mul_of_nonneg_left (h.abs_saSaddle_le hvlo hθ s hw') (by positivity)
    _ = _ := by unfold saLogVarianceConstant; field_simp; ring

/-- The logarithm of the square-root variance factor inherits half the bound. -/
theorem UnivClass.log_saSaddle_sqrt_variance_sub_zero (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) (s : ℝ) {w : ℝ}
    (hw : |w| ≤ saMeanRadius vlo B θ) :
    |Real.log (Real.sqrt (iteratedDeriv 2 (saSmoothCGF ν s) (saSaddle vlo B θ ν s w))) -
        Real.log (Real.sqrt (lawVar ν + s ^ 2))| ≤
      saLogVarianceConstant vlo B θ / 2 * |w| := by
  have hmem := (h.saSaddle_spec hvlo hθ s (hw.trans (saMeanRadius_lt_full hvlo hθ).le)).1
  have hb := (h.saSmoothCGF_variance_bracket hvlo hθ (abs_le.mpr hmem) s).1
  have hvar := h.var_ge
  rw [Real.log_sqrt (by nlinarith [sq_nonneg s]), Real.log_sqrt (by nlinarith [sq_nonneg s]),
    ← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hh := h.log_saSaddle_variance_sub_zero hvlo hθ s hw
  nlinarith

end

end PGM
