import PLAStochastic.Index.GEP.Kernel.Influence.Reward.TotalSum
import Mathlib.MeasureTheory.Integral.Prod

/-! # Signed physical coarea from the actual finite absolute mass -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option maxHeartbeats 1200000

/-- Signed Fubini is justified by the actual nonnegative absolute mass. -/
theorem kernel_IF_signed_nested_integral {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν]
    {K H : A × B → ℝ} (hK : Measurable K) (hK0 : ∀ p, 0 ≤ K p) (hH : Measurable H)
    (hfin : (∫⁻ a, ∫⁻ b, ENNReal.ofReal (K (a,b)) * ENNReal.ofReal |H (a,b)| ∂ν ∂μ) ≠ ∞) :
    Integrable (fun p => K p * H p) (μ.prod ν) ∧
      ((∫⁻ a, ∫⁻ b, ENNReal.ofReal (K (a,b)) * ENNReal.ofReal (H (a,b)) ∂ν ∂μ).toReal -
        (∫⁻ a, ∫⁻ b, ENNReal.ofReal (K (a,b)) * ENNReal.ofReal (-H (a,b)) ∂ν ∂μ).toReal) =
      ∫ a, ∫ b, K (a,b) * H (a,b) ∂ν ∂μ := by
  have hi : Integrable (fun p => K p * H p) (μ.prod ν) := by
    refine ⟨(hK.mul hH).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_prod (fun p => ‖K p * H p‖ₑ)
      ((show Measurable (fun p => K p * H p) from hK.mul hH).enorm.aemeasurable)]
    simp only [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg (hK0 _),
      ENNReal.ofReal_mul (hK0 _)]
    exact lt_top_iff_ne_top.mpr hfin
  refine ⟨hi, ?_⟩
  rw [← integral_prod _ hi, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi,
    lintegral_prod (fun p => ENNReal.ofReal (K p * H p))
      (hK.mul hH).ennreal_ofReal.aemeasurable,
    lintegral_prod (fun p => ENNReal.ofReal (-(K p * H p)))
      (hK.mul hH).neg.ennreal_ofReal.aemeasurable]
  simp only [ENNReal.ofReal_mul (hK0 _), ← mul_neg]


/-- Factored nonnegative pins may be retained outside the signed exterior
integral after the absolute physical mass has been shown finite. -/
theorem kernel_IF_signed_iterated_weight {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν]
    {c : A → ℝ} {O H : A × B → ℝ} (hc : Measurable c) (hc0 : ∀ a, 0 ≤ c a)
    (hO : Measurable O) (hO0 : ∀ p, 0 ≤ O p) (hH : Measurable H)
    (hfin : (∫⁻ a, ENNReal.ofReal (c a) *
      (∫⁻ b, ENNReal.ofReal (O (a,b)) * ENNReal.ofReal |H (a,b)| ∂ν) ∂μ) ≠ ∞) :
    Integrable (fun a => c a * ∫ b, O (a,b) * H (a,b) ∂ν) μ ∧
      ((∫⁻ a, ENNReal.ofReal (c a) *
          (∫⁻ b, ENNReal.ofReal (O (a,b)) * ENNReal.ofReal (H (a,b)) ∂ν) ∂μ).toReal -
        (∫⁻ a, ENNReal.ofReal (c a) *
          (∫⁻ b, ENNReal.ofReal (O (a,b)) * ENNReal.ofReal (-H (a,b)) ∂ν) ∂μ).toReal) =
        ∫ a, c a * ∫ b, O (a,b) * H (a,b) ∂ν ∂μ := by
  have he (F : A × B → ℝ≥0∞) :
      (∫⁻ a, ∫⁻ b, ENNReal.ofReal (c a * O (a,b)) * F (a,b) ∂ν ∂μ) =
        ∫⁻ a, ENNReal.ofReal (c a) * (∫⁻ b, ENNReal.ofReal (O (a,b)) * F (a,b) ∂ν) ∂μ := by
    apply lintegral_congr
    intro a
    simp only [ENNReal.ofReal_mul (hc0 a), mul_assoc]
    exact lintegral_const_mul' _ _ (by finiteness)
  obtain ⟨hi, hh⟩ := kernel_IF_signed_nested_integral μ ν (K := fun p => c p.1 * O p)
    ((hc.comp measurable_fst).mul hO)
    (fun p => mul_nonneg (hc0 p.1) (hO0 p)) hH (by rwa [he (fun p => ENNReal.ofReal |H p|)])
  have hg (a : A) : (∫ b, (c a * O (a,b)) * H (a,b) ∂ν) =
      c a * ∫ b, O (a,b) * H (a,b) ∂ν := by
    simp only [mul_assoc, integral_const_mul]
  refine ⟨hi.integral_prod_left.congr (ae_of_all _ hg), ?_⟩
  rw [he (fun p => ENNReal.ofReal (H p)), he (fun p => ENNReal.ofReal (-H p))] at hh
  simpa only [hg] using hh

end
end PGM
