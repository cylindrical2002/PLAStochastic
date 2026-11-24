import PLAStochastic.Index.GEP.Kernel.Output.Identification.BoundaryKernel

/-! # Transfers to the original kernel interfaces -/

namespace PGM
noncomputable section
open MeasureTheory Set Filter

theorem KernelApproxLip.congr_ae {R L ρ : ℝ} {j k : ℝ → ℝ}
    (h : KernelApproxLip R L ρ j) (he : k =ᵐ[volume.restrict (Ioo (0 : ℝ) R)] j) :
    KernelApproxLip R L ρ k := by
  obtain ⟨G,hG,hb⟩ := h
  refine ⟨G,hG,?_⟩
  filter_upwards [he,hb] with x hx hb
  simpa only [hx] using hb

theorem KernelTail.congr_ae {N ζ : ℝ} {j k : ℝ → ℝ}
    (h : KernelTail N ζ j) (he : k =ᵐ[volume.restrict (Ioi (0 : ℝ))] j) :
    KernelTail N ζ k := by
  filter_upwards [h,he] with x hx he
  simpa only [he] using hx

theorem KernelApproxLip.mono_radius {R R' L ρ : ℝ} {j : ℝ → ℝ}
    (h : KernelApproxLip R L ρ j) (hR : R' ≤ R) : KernelApproxLip R' L ρ j := by
  obtain ⟨G,hG,hb⟩ := h
  refine ⟨G,fun x hx y hy => hG x ⟨hx.1,hx.2.trans hR⟩ y ⟨hy.1,hy.2.trans hR⟩,?_⟩
  exact ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl hR) hb

theorem KernelApproxLip.of_close {R L ρ E : ℝ} {j k : ℝ → ℝ}
    (h : KernelApproxLip R L ρ j)
    (he : ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) R), |k x-j x| ≤ E) :
    KernelApproxLip R L (ρ+E) k := by
  obtain ⟨G,hG,hb⟩ := h
  refine ⟨G,hG,?_⟩
  filter_upwards [he,hb] with x hx hy
  calc
    |k x-G x| = |(k x-j x)+(j x-G x)| := by congr 1; ring
    _ ≤ |k x-j x|+|j x-G x| := abs_add_le _ _
    _ ≤ ρ+E := by linarith

theorem kernel_log_double_le {eps : ℝ} (heps : 2 ≤ eps) :
    Real.log (2*eps) ≤ 2*Real.log eps := by
  have heps0 : 0 < eps := by linarith
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) heps0.ne']
  have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2) heps
  linarith

theorem kernel_sqrt_double_le {eps : ℝ} (_heps : 0 ≤ eps) :
    Real.sqrt (2*eps) ≤ 2*Real.sqrt eps := by
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  exact mul_le_mul_of_nonneg_right (by norm_num : Real.sqrt (2 : ℝ) ≤ 2) (Real.sqrt_nonneg _)

/-- The analytic width is exactly twice the original tolerance. This changes
only the class constant, preserving the original square-root and logarithmic
powers in `KernelC` and `KernelPhi`. -/
theorem kernelApproxLip_width_transfer {eps b K : ℝ} {P : ℕ} {j : ℝ → ℝ}
    (heps : 2 ≤ eps) (hb : 0 ≤ b) (hK : 0 ≤ K)
    (h : KernelApproxLip (b*Real.log (2*eps))
      (K*Real.sqrt (2*eps)*Real.log (2*eps)^P) (K/(2*eps)) j) :
    KernelApproxLip (b*Real.log eps)
      ((2^(P+1)*K)*Real.sqrt eps*Real.log eps^P) (K/eps) j := by
  have heps0 : 0 < eps := by linarith
  have hl0 : 0 ≤ Real.log eps := Real.log_nonneg (by linarith)
  have hR : b*Real.log eps ≤ b*Real.log (2*eps) :=
    mul_le_mul_of_nonneg_left (Real.log_le_log heps0 (by linarith)) hb
  apply (h.mono_radius hR).mono
  · have hpow := pow_le_pow_left₀ (Real.log_nonneg (by linarith : 1 ≤ 2*eps))
      (kernel_log_double_le heps) P
    calc
      _ ≤ (K*(2*Real.sqrt eps))*(2*Real.log eps)^P :=
        mul_le_mul (mul_le_mul_of_nonneg_left (kernel_sqrt_double_le heps0.le) hK)
          hpow (pow_nonneg (Real.log_nonneg (by linarith : 1 ≤ 2*eps)) P) (by positivity)
      _ = _ := by rw [mul_pow,pow_succ]; ring
  · exact div_le_div_of_nonneg_left hK heps0 (by linarith)

end
end PGM
