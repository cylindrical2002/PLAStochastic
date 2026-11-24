import PLAStochastic.Index.KEP.ReferenceScale.ConvolutionWeakTests
import PLAStochastic.Index.KEP.ReferenceScale.CleanMomentBudget
import PLAStochastic.Index.KEP.ReferenceScale.SurvivingCoreBudget

/-!
# The actual normalization and physical convolution tests

The original next-layer normalization is the actual expected reference segment
length. Bounded C2 output tests give genuine bounded C2 physical tests, and the
convolution increment has the same positive exponential weight with a paid
one-gap moment factor.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem kepReference_lawC_eq_segMean {eps : ℝ}
    (heps : kepReferenceClassicalThreshold ≤ eps) (j : ℕ) :
    lawC eps (kepReferenceLaw eps j) =
      segMean expSeqMeasure eps (epLayerSeq eps expCoord j) := by
  have he := (le_max_right _ _).trans heps
  exact (layer_law_orbit gapLaw_expCoord he expPM (by
    change expMeasure 1 = expSeqMeasure.map (fun ω => expCoord 0 ω / 1)
    simpa only [div_one] using (hasLaw_expCoord 0).map_eq.symm) j).2.symm

theorem kepReference_lawC_bracket {eps : ℝ}
    (heps : kepReferenceClassicalThreshold ≤ eps) (j : ℕ) :
    eps ^ 2 / kepGraphMeanBracket ≤ lawC eps (kepReferenceLaw eps j) ∧
      lawC eps (kepReferenceLaw eps j) ≤ kepGraphMeanBracket * eps ^ 2 := by
  rw [kepReference_lawC_eq_segMean heps j]
  exact segMean_bracket gapLaw_expCoord ((le_max_right _ _).trans heps) j

theorem kep_scaled_output_test_C2 {phi phi' phi'' : ℝ → ℝ}
    (hdphi : ∀ s, HasDerivAt phi (phi' s) s)
    (hddphi : ∀ s, HasDerivAt phi' (phi'' s) s)
    (hcphi'' : Continuous phi'') {M C : ℝ} (hC : 1 ≤ C)
    (hb : ∀ t, |phi t| ≤ M ∧ |phi' t| ≤ M ∧ |phi'' t| ≤ M) :
    (∀ s, HasDerivAt (fun t => phi (t / C)) (phi' (s / C) / C) s) ∧
      (∀ s, HasDerivAt (fun t => phi' (t / C) / C) (phi'' (s / C) / C ^ 2) s) ∧
      Continuous (fun t => phi'' (t / C) / C ^ 2) ∧
      (∀ s, |phi (s / C)| ≤ M ∧ |phi' (s / C) / C| ≤ M ∧
        |phi'' (s / C) / C ^ 2| ≤ M) := by
  have hM : 0 ≤ M := (abs_nonneg (phi 0)).trans (hb 0).1
  have hCp : 0 < C := by linarith
  have hC2 : 1 ≤ C ^ 2 := by nlinarith
  refine ⟨?_, ?_, (hcphi''.comp (continuous_id.div_const C)).div_const _, ?_⟩
  · intro s
    simpa only [Function.comp_def, id_eq, div_eq_mul_inv, one_mul] using
      (hdphi (s / C)).comp s ((hasDerivAt_id s).div_const C)
  · intro s
    simpa only [Function.comp_def, id_eq, div_eq_mul_inv, one_mul, pow_two,
      mul_inv_rev, mul_assoc] using
      ((hddphi (s / C)).comp s ((hasDerivAt_id s).div_const C)).div_const C
  · intro s
    refine ⟨(hb _).1, ?_, ?_⟩
    · rw [abs_div, abs_of_pos hCp]
      exact (div_le_div_of_nonneg_right (hb _).2.1 hCp.le).trans (div_le_self hM hC)
    · rw [abs_div, abs_of_pos (sq_pos_of_pos hCp)]
      exact (div_le_div_of_nonneg_right (hb _).2.2 (sq_nonneg C)).trans (div_le_self hM hC2)

theorem kepConvolutionTest_exponential_bound (nu : ProbabilityMeasure ℝ)
    (hnu : (nu : Measure ℝ) (Iic 0) = 0) {phi : ℝ → ℝ} (hphi : Measurable phi)
    {M B u : ℝ} (hb : ∀ t, |phi t| ≤ M) (_hB : 0 ≤ B)
    (hphiB : ∀ t, 0 ≤ t → |phi t| ≤ B * Real.exp (u * t))
    (hmgf : Integrable (fun x => Real.exp (u * x)) (nu : Measure ℝ))
    (s : ℝ) (hs : 0 ≤ s) :
    |kepConvolutionTest nu phi s| ≤
      B * (1 + ∫ x, Real.exp (u * x) ∂(nu : Measure ℝ)) * Real.exp (u * s) := by
  have hi : Integrable (fun x => phi (s + x)) (nu : Measure ℝ) :=
    (integrable_const M).mono' (hphi.comp (measurable_const.add measurable_id)).aestronglyMeasurable
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hb (s + x))
  have heq (x : ℝ) : B * Real.exp (u * (s + x)) =
      (B * Real.exp (u * s)) * Real.exp (u * x) := by
    rw [mul_add, Real.exp_add]
    ring
  have hiexp : Integrable (fun x => B * Real.exp (u * (s + x))) (nu : Measure ℝ) := by
    simp_rw [heq]
    exact hmgf.const_mul _
  have hpos : ∀ᵐ x ∂(nu : Measure ℝ), 0 < x := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnu] with x hx
    exact lt_of_not_ge hx
  have hI : |∫ x, phi (s + x) ∂(nu : Measure ℝ)| ≤
      B * Real.exp (u * s) * ∫ x, Real.exp (u * x) ∂(nu : Measure ℝ) := by
    have hnorm : |∫ x, phi (s + x) ∂(nu : Measure ℝ)| ≤
        ∫ x, |phi (s + x)| ∂(nu : Measure ℝ) := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (μ := (nu : Measure ℝ)) (fun x : ℝ => phi (s + x))
    apply hnorm.trans
    have hh := integral_mono_ae hi.abs hiexp (hpos.mono fun x hx => hphiB _ (by linarith))
    simp_rw [heq, integral_const_mul] at hh
    exact hh
  exact (abs_sub _ _).trans ((add_le_add hI (hphiB s hs)).trans_eq (by ring))

end

end PGM
