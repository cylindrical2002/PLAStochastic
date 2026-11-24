import PLAStochastic.Index.CEPS.Scaled.DiscountFrequencyRadius
import PLAStochastic.ForMathlib.Analysis.Complex.TaylorSeriesBudget

/-! # Marked-discount Taylor series on the full square-root frequency scale -/

noncomputable section
open Complex Set Metric MeasureTheory PowerSeries
open PGM.WienerHopf
namespace PGM

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledMarkedDiscount_frequency_differentiableOn (z : ℂ) :
    DifferentiableOn ℂ (cepsScaledMarkedDiscount ρW z)
      (ball 0 (cepsDiscountFrequencyBase D θ / (1 + Real.sqrt ‖z‖))) := by
  have hg : DifferentiableOn ℂ (fun b : ℂ => b ^ 2 * z)
      (ball 0 (cepsDiscountFrequencyBase D θ / (1 + Real.sqrt ‖z‖))) :=
    (differentiableOn_id.pow 2).mul_const z
  have ht : MapsTo (fun b : ℂ => b ^ 2 * z)
      (ball 0 (cepsDiscountFrequencyBase D θ / (1 + Real.sqrt ‖z‖)))
      (ball 0 (cepsMarkedUnitRadius D θ)) := by
    intro b hb
    apply cepsDiscountFrequency_mem hD hθ
    exact (lt_div_iff₀ (by positivity)).mp (mem_ball_zero_iff.mp hb)
  exact ((cepsMarkedDiscountUnit_budget hW hθ hD).1.comp hg ht).const_mul z

include hW hθ hD in
theorem cepsScaledMarkedDiscount_seriesApprox (N : ℕ) (z : ℂ) {b : ℝ} (hb : 0 ≤ b)
    (hsmall : b * (1 + Real.sqrt ‖z‖) < cepsDiscountFrequencyBase D θ / 2) :
    SeriesApprox (cepsScaledMarkedDiscount ρW z b)
      (complexTaylorSeries (cepsScaledMarkedDiscount ρW z) 0) N b
      (complexTaylorBudgetConstant N (cepsDiscountFrequencyBase D θ)
        (cepsMarkedDiscountBound D θ / (θ / 2)) * (1 + Real.sqrt ‖z‖) ^ (N + 3)) := by
  have hd : 0 ≤ cepsMarkedDiscountBound D θ / (θ / 2) :=
    div_nonneg (cepsMarkedDiscountBound_pos hD hθ).le (half_pos hθ).le
  have hH : 1 ≤ 1 + Real.sqrt ‖z‖ := by linarith [Real.sqrt_nonneg ‖z‖]
  have hbound : ∀ c ∈ ball (0 : ℂ) (cepsDiscountFrequencyBase D θ / (1 + Real.sqrt ‖z‖)),
      ‖cepsScaledMarkedDiscount ρW z c‖ ≤
        (cepsMarkedDiscountBound D θ / (θ / 2)) * (1 + Real.sqrt ‖z‖) ^ 2 := by
    intro c hc
    have ht := cepsScaledMarkedDiscount_frequency_budget hW hθ hD
      ((lt_div_iff₀ (by positivity)).mp (mem_ball_zero_iff.mp hc))
    apply ht.trans
    have hs := Real.sq_sqrt (norm_nonneg z)
    have hs0 := Real.sqrt_nonneg ‖z‖
    nlinarith [mul_le_mul_of_nonneg_right (show ‖z‖ ≤ (1 + Real.sqrt ‖z‖) ^ 2 by nlinarith) hd]
  have hbs : (b : ℂ) ∈ ball (0 : ℂ)
      ((cepsDiscountFrequencyBase D θ / (1 + Real.sqrt ‖z‖)) / 2) := by
    rw [mem_ball_zero_iff, norm_real, Real.norm_eq_abs, abs_of_nonneg hb]
    rw [show cepsDiscountFrequencyBase D θ / (1 + Real.sqrt ‖z‖) / 2 =
      (cepsDiscountFrequencyBase D θ / 2) / (1 + Real.sqrt ‖z‖) by ring]
    exact (lt_div_iff₀ (by positivity)).mpr hsmall
  simpa only [show N + 1 + 2 = N + 3 by omega] using
    seriesApprox_of_polynomial_disc (cepsDiscountFrequencyBase_pos hD hθ) hH hd 2 N
      (cepsScaledMarkedDiscount_frequency_differentiableOn hW hθ hD z) hbound hb hbs

end PGM
