import PLAStochastic.Index.CEPS.Scaled.DiscountScale
import PLAStochastic.ForMathlib.Analysis.Complex.TaylorDisc

/-! # All-order Taylor budgets for the actual scaled discount and its unit -/

noncomputable section
open Complex MeasureTheory Set Metric
open PGM.WienerHopf
namespace PGM

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledDiscountUnit_taylor_le (z : ℂ) (n : ℕ) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (cepsDiscountScaleRadius D θ z / 2)) :
    ‖cepsScaledDiscountUnit ρW z b - complexTaylorSum (cepsScaledDiscountUnit ρW z) n 0 b‖ ≤
      ((n.factorial : ℝ) * (cepsMarkedDiscountBound D θ / (θ / 2)) /
        (cepsDiscountScaleRadius D θ z / 4) ^ n) * ‖b‖ ^ n := by
  obtain ⟨hd, hm, _, _⟩ := cepsScaledDiscountUnit_budget hW hθ hD z
  simpa only [sub_zero] using norm_sub_complexTaylorSum_le_of_ball n
    (cepsDiscountScaleRadius_pos hD hθ z) hd hm hb

include hW hθ hD in
theorem cepsScaledDiscountUnit_inverse_taylor_le (z : ℂ) (n : ℕ) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (cepsDiscountScaleRadius D θ z / 2)) :
    ‖(cepsScaledDiscountUnit ρW z b)⁻¹ -
        complexTaylorSum (fun b => (cepsScaledDiscountUnit ρW z b)⁻¹) n 0 b‖ ≤
      ((n.factorial : ℝ) * 2 / (cepsDiscountScaleRadius D θ z / 4) ^ n) * ‖b‖ ^ n := by
  obtain ⟨_, _, hd, hm⟩ := cepsScaledDiscountUnit_budget hW hθ hD z
  simpa only [sub_zero] using norm_sub_complexTaylorSum_le_of_ball n
    (cepsDiscountScaleRadius_pos hD hθ z) hd (fun b hb => (hm b hb).2) hb

include hW hθ hD in
theorem cepsScaledMarkedDiscount_taylor_le (z : ℂ) (n : ℕ) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (cepsDiscountScaleRadius D θ z / 2)) :
    ‖cepsScaledMarkedDiscount ρW z b -
        complexTaylorSum (cepsScaledMarkedDiscount ρW z) n 0 b‖ ≤
      ((n.factorial : ℝ) * (‖z‖ * (cepsMarkedDiscountBound D θ / (θ / 2))) /
        (cepsDiscountScaleRadius D θ z / 4) ^ n) * ‖b‖ ^ n := by
  obtain ⟨hd, hm, _, _⟩ := cepsScaledDiscountUnit_budget hW hθ hD z
  have hf : DifferentiableOn ℂ (cepsScaledMarkedDiscount ρW z)
      (ball 0 (cepsDiscountScaleRadius D θ z)) := hd.const_mul z
  have hnorm : ∀ b ∈ ball (0 : ℂ) (cepsDiscountScaleRadius D θ z),
      ‖cepsScaledMarkedDiscount ρW z b‖ ≤ ‖z‖ * (cepsMarkedDiscountBound D θ / (θ / 2)) := by
    intro b hb
    rw [cepsScaledMarkedDiscount, norm_mul]
    exact mul_le_mul_of_nonneg_left (hm b hb) (norm_nonneg z)
  simpa only [sub_zero] using norm_sub_complexTaylorSum_le_of_ball n
    (cepsDiscountScaleRadius_pos hD hθ z) hf hnorm hb

end PGM
