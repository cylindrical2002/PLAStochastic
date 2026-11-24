import PLAStochastic.Index.GEP.Kernel.Influence.Signed.CoareaIntegral

/-! # The original absolute physical mass controls signed coarea in L1 -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

/-- The same absolute mass that justifies signed coarea controls the integral
of its norm, and hence justifies subsequent series and integral interchanges. -/
theorem kernel_IF_signed_iterated_weight_norm {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν]
    {c : A → ℝ} {O H : A × B → ℝ} (hc : Measurable c) (hc0 : ∀ a, 0 ≤ c a)
    (hO : Measurable O) (hO0 : ∀ p, 0 ≤ O p) (hH : Measurable H)
    (hfin : (∫⁻ a, ENNReal.ofReal (c a) *
      (∫⁻ b, ENNReal.ofReal (O (a,b)) * ENNReal.ofReal |H (a,b)| ∂ν) ∂μ) ≠ ∞) :
    (∫ a, ‖c a * ∫ b, O (a,b) * H (a,b) ∂ν‖ ∂μ) ≤
      (∫⁻ a, ENNReal.ofReal (c a) *
        (∫⁻ b, ENNReal.ofReal (O (a,b)) * ENNReal.ofReal |H (a,b)| ∂ν) ∂μ).toReal := by
  have hSigned := kernel_IF_signed_iterated_weight μ ν hc hc0 hO hO0 hH hfin
  have hAbs := kernel_IF_signed_iterated_weight μ ν hc hc0 hO hO0 hH.abs
    (by simpa only [abs_abs] using hfin)
  have hzero (a : A) (b : B) : ENNReal.ofReal (-|H (a,b)|) = 0 :=
    ENNReal.ofReal_eq_zero.mpr (neg_nonpos.mpr (abs_nonneg _))
  have heAbs := hAbs.2
  simp only [hzero, mul_zero, lintegral_zero, ENNReal.toReal_zero, sub_zero] at heAbs
  rw [heAbs]
  apply integral_mono hSigned.1.norm hAbs.1
  intro a
  dsimp only
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hc0 a)]
  apply mul_le_mul_of_nonneg_left _ (hc0 a)
  calc
    ‖∫ b, O (a,b) * H (a,b) ∂ν‖ ≤ ∫ b, ‖O (a,b) * H (a,b)‖ ∂ν :=
      norm_integral_le_integral_norm _
    _ = ∫ b, O (a,b) * |H (a,b)| ∂ν := by
      apply integral_congr_ae
      exact ae_of_all _ (fun b => by
        dsimp only
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hO0 (a,b))])

end
end PGM
