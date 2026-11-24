import PLAStochastic.Index.GEP.StrongApprox.Quantile.SplitLaw

/-! # WP5: the Gaussian conditional split and its exact quantile -/

namespace PGM

noncomputable section

open MeasureTheory Measure ProbabilityTheory Set
open scoped Real NNReal ENNReal

theorem saDensity_gaussianPDF (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    SADensity (gaussianPDFReal m v) := by
  refine ⟨?_, fun x => gaussianPDFReal_pos m v x hv,
    integrable_gaussianPDFReal _ _, integral_gaussianPDFReal_eq_one _ hv,
    ⟨_, fun x => gaussianPDFReal_le_inv_sqrt m x v⟩⟩
  unfold gaussianPDFReal
  fun_prop

theorem saDensity_gaussianPDF_law (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    ((saDensity_gaussianPDF m hv).law : Measure ℝ) = gaussianReal m v :=
  (gaussianReal_of_var_ne_zero m hv).symm

theorem saGaussianPDF_split_product {v : ℝ≥0} (hv : v ≠ 0) (a x : ℝ) :
    gaussianPDFReal 0 v x * gaussianPDFReal 0 v (a - x) =
      gaussianPDFReal 0 (v + v) a * gaussianPDFReal (a / 2) (v / 2) x := by
  have hv0 : 0 < (v : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  have hpos : 0 < 2 * π * (v : ℝ) := by positivity
  have hsqrt : Real.sqrt (2 * π * ((v : ℝ) + v)) * Real.sqrt (2 * π * (v / 2 : ℝ)) =
      2 * π * v := by
    rw [← Real.sqrt_mul (by positivity)]
    have he : (2 * π * ((v : ℝ) + v)) * (2 * π * (v / 2 : ℝ)) = (2 * π * v) ^ 2 := by ring
    rw [he, Real.sqrt_sq hpos.le]
  have hcoef : (Real.sqrt (2 * π * (v : ℝ)))⁻¹ * (Real.sqrt (2 * π * (v : ℝ)))⁻¹ =
      (Real.sqrt (2 * π * ((v : ℝ) + v)))⁻¹ * (Real.sqrt (2 * π * (v / 2 : ℝ)))⁻¹ := by
    rw [← mul_inv, ← mul_inv, hsqrt, ← pow_two, Real.sq_sqrt hpos.le]
  have hexp : -(x ^ 2 / (2 * (v : ℝ))) - (a - x) ^ 2 / (2 * v) =
      -(a ^ 2 / (2 * ((v : ℝ) + v))) - (x - a / 2) ^ 2 / (2 * (v / 2)) := by
    field_simp
    ring
  simp only [gaussianPDFReal, sub_zero, NNReal.coe_add, NNReal.coe_div, NNReal.coe_ofNat]
  rw [mul_mul_mul_comm, mul_mul_mul_comm
    (Real.sqrt (2 * π * ((v : ℝ) + v)))⁻¹, ← Real.exp_add, ← Real.exp_add, hcoef]
  congr 1
  congr 1
  simpa only [neg_div, sub_eq_add_neg] using hexp

theorem saSumDensity_gaussian {v : ℝ≥0} (hv : v ≠ 0) :
    saSumDensity (gaussianPDFReal 0 v) = gaussianPDFReal 0 (v + v) := by
  have hvv : v + v ≠ 0 := by positivity
  apply (saDensity_gaussianPDF 0 hv).sumDensity.eq_of_law (saDensity_gaussianPDF 0 hvv)
  change volume.withDensity (fun a => ENNReal.ofReal (saSumDensity (gaussianPDFReal 0 v) a)) = _
  rw [(saDensity_gaussianPDF 0 hv).sumDensity_law, saDensity_gaussianPDF_law 0 hv,
    saDensity_gaussianPDF_law 0 hvv, gaussianReal_conv_gaussianReal, zero_add]

theorem saSplitDensity_gaussian {v : ℝ≥0} (hv : v ≠ 0) (a : ℝ) :
    saSplitDensity (gaussianPDFReal 0 v) a = gaussianPDFReal (a / 2) (v / 2) := by
  funext x
  have hvv : v + v ≠ 0 := by positivity
  rw [saSplitDensity, saSumDensity_gaussian hv, saGaussianPDF_split_product hv]
  exact mul_div_cancel_left₀ _ (gaussianPDFReal_pos 0 (v + v) a hvv).ne'

theorem saCDF_map_affine (μ : Measure ℝ) [IsProbabilityMeasure μ] (c : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (z : ℝ) :
    cdf (μ.map (fun x => c + σ * x)) (c + σ * z) = cdf μ z := by
  have hm : Measurable (fun x : ℝ => c + σ * x) := by fun_prop
  have : IsProbabilityMeasure (μ.map (fun x => c + σ * x)) := isProbabilityMeasure_map hm.aemeasurable
  rw [cdf_eq_real, cdf_eq_real, map_measureReal_apply hm measurableSet_Iic]
  congr 1
  ext x
  simp only [mem_preimage, mem_Iic, add_le_add_iff_left, mul_le_mul_iff_right₀ hσ]

theorem saGaussian_affine_law (m : ℝ) (v : ℝ≥0) :
    (gaussianReal 0 1).map (fun z => m + Real.sqrt v * z) = gaussianReal m v := by
  have he : (fun z : ℝ => m + Real.sqrt v * z) =
      (fun x : ℝ => m + x) ∘ (fun z : ℝ => Real.sqrt v * z) := rfl
  rw [he, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
    gaussianReal_map_const_add]
  congr 1
  · simp
  · ext
    simp [Real.sq_sqrt v.coe_nonneg]

theorem saQuantile_gaussian (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (z : ℝ) :
    saQuantile (cdf (gaussianReal m v)) (cdf (gaussianReal 0 1) z) = m + Real.sqrt v * z := by
  have hF := saCDF_gaussianReal m hv
  have h0 := saCDF_gaussianReal 0 (v := 1) one_ne_zero
  have hs : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast pos_iff_ne_zero.mpr hv)
  apply hF.strictMono.injective
  rw [hF.apply_quantile (h0.mem_Ioo z)]
  have h := saCDF_map_affine (gaussianReal 0 1) m hs z
  rw [saGaussian_affine_law m v] at h
  exact h.symm

/-- The Gaussian tree driven by the common normal innovation has the usual bridge formula. -/
theorem saSplitQuantile_gaussian {v : ℝ≥0} (hv : v ≠ 0) (a z : ℝ) :
    saSplitQuantile (saDensity_gaussianPDF 0 hv) a (cdf (gaussianReal 0 1) z) =
      a / 2 + Real.sqrt (v / 2 : ℝ≥0) * z := by
  have hvh : v / 2 ≠ 0 := div_ne_zero hv (by norm_num)
  have hl : (((saDensity_gaussianPDF 0 hv).splitDensity a).law : Measure ℝ) =
      gaussianReal (a / 2) (v / 2) := by
    change volume.withDensity (fun x => ENNReal.ofReal (saSplitDensity (gaussianPDFReal 0 v) a x)) = _
    rw [saSplitDensity_gaussian hv]
    exact (gaussianReal_of_var_ne_zero (a / 2) hvh).symm
  unfold saSplitQuantile
  rw [hl]
  exact saQuantile_gaussian _ hvh z

end

end PGM
