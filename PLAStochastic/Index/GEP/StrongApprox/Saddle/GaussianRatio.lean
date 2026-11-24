import PLAStochastic.Index.GEP.StrongApprox.Saddle.SumDensityBounds

/-! # WP5: Gaussian density ratios from the quantitative saddle expansion -/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Real ENNReal NNReal

theorem sa_log_gaussianPDFReal {v : ℝ} (hv : 0 < v) (x : ℝ) :
    Real.log (gaussianPDFReal 0 (Real.toNNReal v) x) =
      -Real.log (Real.sqrt (2 * π * v)) - x ^ 2 / (2 * v) := by
  simp only [gaussianPDFReal, Real.coe_toNNReal _ hv.le, sub_zero]
  rw [Real.log_mul (inv_ne_zero (Real.sqrt_pos.mpr (by positivity)).ne')
    (Real.exp_ne_zero _), Real.log_inv, Real.log_exp]
  ring

/-- A Gaussian with variance `l V`, at the sum location `l w`. -/
theorem sa_log_gaussianPDFReal_sum {V : ℝ} (hV : 0 < V) {l : ℕ} (hl : 0 < l) (w : ℝ) :
    Real.log (gaussianPDFReal 0 (Real.toNNReal ((l : ℝ) * V)) ((l : ℝ) * w)) =
      -Real.log (Real.sqrt l) - Real.log (Real.sqrt (2 * π * V)) -
        (l : ℝ) * (w ^ 2 / (2 * V)) := by
  have hlr : 0 < (l : ℝ) := by exact_mod_cast hl
  rw [sa_log_gaussianPDFReal (mul_pos hlr hV),
    show 2 * π * ((l : ℝ) * V) = (l : ℝ) * (2 * π * V) by ring,
    Real.sqrt_mul hlr.le, Real.log_mul (Real.sqrt_pos.mpr hlr).ne'
      (Real.sqrt_pos.mpr (by positivity)).ne']
  field_simp
  ring

variable {vlo vhi κ₃ B θ : ℝ} {ν : ProbabilityMeasure ℝ}

theorem UnivClass.saRate_quadratic_error (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) (s : ℝ) {w : ℝ}
    (hw : |w| ≤ saMeanRadius vlo B θ) :
    |saRate vlo B θ ν s w - w ^ 2 / (2 * (lawVar ν + s ^ 2))| ≤
      saRateThird vlo B θ * |w| ^ 3 / 6 := by
  have hz : |(0 : ℝ)| < 3 / 4 * vlo * saTiltRadius vlo B θ := by
    have := saTiltRadius_pos (B := B) hvlo hθ
    simp only [abs_zero]
    positivity
  have ht := h.saRate_taylor_two hvlo hθ s (u := 0) (t := w) (by simpa using hw)
  rw [h.saRate_zero hvlo hθ s, h.deriv_saRate hvlo hθ s hz,
    h.saSaddle_zero hvlo hθ s, h.iteratedDeriv_two_saRate_zero hvlo hθ s] at ht
  simp only [zero_add, sub_zero, zero_mul] at ht
  convert ht using 1
  congr 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The unconditional central Gaussian ratio for the actual smoothed sum. -/
theorem exists_uniform_saCenteredSumDensity_gaussian_ratio
    (vlo vhi κ₃ B θ D c : ℝ) (hvlo : 0 < vlo) (hvhi : 0 < vhi)
    (hB : 0 < B) (hθ : 0 < θ) (hD : 0 < D) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ν : ProbabilityMeasure ℝ, UnivClass vlo vhi κ₃ B θ ν → SmoothPart D c ν →
      ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ l : ℕ, 2 ≤ l →
      1 / s ≤ (l : ℝ) ^ 8 → 2 * C ≤ Real.sqrt l →
      ∀ w : ℝ, |w| ≤ saMeanRadius vlo B θ →
        |Real.log (saCenteredSumDensity ν s l (l * w) /
          gaussianPDFReal 0 (Real.toNNReal ((l : ℝ) * (lawVar ν + s ^ 2))) (l * w))| ≤
          (2 * C) / Real.sqrt l + saLogVarianceConstant vlo B θ / 2 * |w| +
            (l : ℝ) * saRateThird vlo B θ * |w| ^ 3 / 6 := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_saCenteredSumDensity_log_correction
    vlo vhi κ₃ B θ D c hvlo hvhi hB hθ hD hc
  refine ⟨C, hC, ?_⟩
  intro ν hν hsm s hs hs1 l hl hscale hlarge w hw
  have hl0 : 0 < l := by omega
  have hlr : 0 < (l : ℝ) := by exact_mod_cast hl0
  have hV : 0 < lawVar ν + s ^ 2 := by nlinarith [hν.var_ge, sq_nonneg s]
  have hp := saCenteredSumDensity_pos ν hs hl0 ((l : ℝ) * w)
  have hg : 0 < gaussianPDFReal 0 (Real.toNNReal ((l : ℝ) * (lawVar ν + s ^ 2))) (l * w) := by
    apply gaussianPDFReal_pos
    simp [Real.toNNReal_eq_zero, (mul_pos hlr hV).not_ge]
  rw [Real.log_div hp.ne' hg.ne', sa_log_gaussianPDFReal_sum hV hl0 w]
  have he : Real.log (saCenteredSumDensity ν s l (l * w)) -
      (-Real.log (Real.sqrt l) - Real.log (Real.sqrt (2 * π * (lawVar ν + s ^ 2))) -
        (l : ℝ) * (w ^ 2 / (2 * (lawVar ν + s ^ 2)))) =
      (Real.log (saCenteredSumDensity ν s l (l * w)) +
        (l : ℝ) * saRate vlo B θ ν s w + Real.log (Real.sqrt l) +
        Real.log (Real.sqrt (2 * π * (lawVar ν + s ^ 2)))) -
      (l : ℝ) * (saRate vlo B θ ν s w - w ^ 2 / (2 * (lawVar ν + s ^ 2))) := by ring
  rw [he]
  have hrate := hν.saRate_quadratic_error hvlo hθ s hw
  have hrate' : |(l : ℝ) * (saRate vlo B θ ν s w - w ^ 2 / (2 * (lawVar ν + s ^ 2)))| ≤
      (l : ℝ) * saRateThird vlo B θ * |w| ^ 3 / 6 := by
    rw [abs_mul, abs_of_pos hlr]
    convert mul_le_mul_of_nonneg_left hrate hlr.le using 1 <;> first | rfl | ring
  exact (abs_sub _ _).trans (add_le_add (hb ν hν hsm s hs hs1 l hl hscale hlarge w hw) hrate')

end

end PGM
