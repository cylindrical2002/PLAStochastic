import PLAStochastic.Index.KEP.ReferenceScale.ActualBridgeWard

/-!
# Spatial derivative representatives as actual final killed convolutions

This identifies both oriented logarithmic bridge derivatives with the physical
first and second kernels used in the quantitative estimates. The original
endpoint is on the band; the final endpoint of the smooth convolution may be
arbitrary, so its boundary values are also covered.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem kepLogStepFirst_eq_kepStepSpatialFirst (g : ℝ → ℝ) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (s t : ℝ) :
    kepLogStepFirst g σ s t = kepStepSpatialFirst g σ (σ * Real.exp s) t := by
  rcases hσ with rfl | rfl
  · simp only [kepLogStepFirst, kepStepSpatialFirst, one_mul, neg_one_mul,
      abs_of_pos (Real.exp_pos s), Real.exp_neg, div_eq_mul_inv, mul_inv_rev]
    ring
  · simp only [kepLogStepFirst, kepStepSpatialFirst, neg_one_mul, abs_neg,
      abs_of_pos (Real.exp_pos s), Real.exp_neg, div_eq_mul_inv, mul_inv_rev, inv_neg,
      neg_neg]
    ring_nf

theorem kepLogStepSecond_eq_kepStepSpatialSecond (g : ℝ → ℝ) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (s t : ℝ) :
    kepLogStepSecond g σ s t = kepStepSpatialSecond g σ (σ * Real.exp s) t := by
  rcases hσ with rfl | rfl
  · simp only [kepLogStepSecond, kepStepSpatialSecond, one_mul, one_pow,
      abs_of_pos (Real.exp_pos s), Real.exp_neg, div_eq_mul_inv, mul_inv_rev, ← inv_pow]
    ring
  · simp only [kepLogStepSecond, kepStepSpatialSecond, neg_one_mul,
      abs_neg, abs_of_pos (Real.exp_pos s), Real.exp_neg, div_eq_mul_inv, mul_inv_rev,
      inv_neg, neg_sq, ← inv_pow]
    ring_nf

theorem kepLogBridgeRight_eq_first_convolution (ν : ProbabilityMeasure ℝ)
    {f g : ℝ → ℝ} {D w σ : ℝ} (hf : Measurable f) (hf0 : ∀ t, 0 ≤ f t)
    (hfD : ∀ t, f t ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun t => ENNReal.ofReal (f t)))
    (hσ : σ = 1 ∨ σ = -1) (s : ℝ) (n : ℕ) {x : ℝ} (hx : x ∈ Icc 0 w) (y : ℝ) :
    kepFixedBridgeRight (kepLogStep f σ) (kepLogStepFirst g σ) w s (n + 1) x y =
      truncatedConvolution 0 w (kepStepSpatialFirst g σ (σ * Real.exp s))
        (fun z => krDens (Icc 0 w) ν f σ (σ * Real.exp s) (n + 1) x z) y := by
  unfold kepFixedBridgeRight truncatedConvolution
  apply setIntegral_congr_fun measurableSet_Ioc
  intro z hz
  dsimp only
  rw [kepLogBridge_eq_krDens ν hf hf0 hfD hν hσ s n hx ⟨hz.1.le, hz.2⟩,
    kepLogStepFirst_eq_kepStepSpatialFirst g hσ]
  ring

theorem kepLogBridgeRight_eq_second_convolution (ν : ProbabilityMeasure ℝ)
    {f g : ℝ → ℝ} {D w σ : ℝ} (hf : Measurable f) (hf0 : ∀ t, 0 ≤ f t)
    (hfD : ∀ t, f t ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun t => ENNReal.ofReal (f t)))
    (hσ : σ = 1 ∨ σ = -1) (s : ℝ) (n : ℕ) {x : ℝ} (hx : x ∈ Icc 0 w) (y : ℝ) :
    kepFixedBridgeRight (kepLogStep f σ) (kepLogStepSecond g σ) w s (n + 1) x y =
      truncatedConvolution 0 w (kepStepSpatialSecond g σ (σ * Real.exp s))
        (fun z => krDens (Icc 0 w) ν f σ (σ * Real.exp s) (n + 1) x z) y := by
  unfold kepFixedBridgeRight truncatedConvolution
  apply setIntegral_congr_fun measurableSet_Ioc
  intro z hz
  dsimp only
  rw [kepLogBridge_eq_krDens ν hf hf0 hfD hν hσ s n hx ⟨hz.1.le, hz.2⟩,
    kepLogStepSecond_eq_kepStepSpatialSecond g hσ]
  ring

end

end PGM
