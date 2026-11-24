import PLAStochastic.Index.GEP.StrongApprox.Quantile.DensitySandwich

/-! # WP5: a coarse Gaussian tail lower bound for the uniform horizon choice -/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped Real

/-- Integrating over a single unit interval gives a lower tail bound sufficient
for all logarithmic-window comparisons. -/
theorem saGaussianTail_lower {R : ℝ} (hR : 0 ≤ R) :
    Real.exp (-1) / Real.sqrt (2 * π) * Real.exp (-R ^ 2) ≤ saGaussianTail R := by
  have hpdf : ∀ x ∈ Icc R (R + 1), gaussianPDFReal 0 1 (R + 1) ≤ gaussianPDFReal 0 1 x := by
    intro x hx
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    nlinarith [hx.1, hx.2]
  have hint : gaussianPDFReal 0 1 (R + 1) ≤ ∫ x in R..(R + 1), gaussianPDFReal 0 1 x := by
    have hm := intervalIntegral.integral_mono_on (show R ≤ R + 1 by linarith)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => gaussianPDFReal 0 1 (R + 1)) volume R (R + 1))
      saDensity_standardGaussian.integrable.intervalIntegrable hpdf
    simpa only [intervalIntegral.integral_const, add_sub_cancel_left, one_smul] using hm
  have hsplit := saDensity_standardGaussian.tail_split R (R + 1)
  rw [sa_standardGaussian_law] at hsplit
  have htail : gaussianPDFReal 0 1 (R + 1) ≤ saGaussianTail R := by
    change saGaussianTail R = _ + saGaussianTail (R + 1) at hsplit
    linarith [(saGaussianTail_pos (R + 1)).le]
  apply le_trans _ htail
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  have he : -1 - R ^ 2 ≤ -(R + 1) ^ 2 / 2 := by nlinarith [sq_nonneg (R - 1)]
  calc
    _ = (Real.sqrt (2 * π))⁻¹ * Real.exp (-1 - R ^ 2) := by rw [show -1 - R ^ 2 = (-1) + (-R ^ 2) by ring, Real.exp_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity)

end

end PGM
