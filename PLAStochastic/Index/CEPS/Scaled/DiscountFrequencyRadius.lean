import PLAStochastic.Index.CEPS.Scaled.DiscountScale

/-! # Marked discount unit on the square-root frequency scale -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def cepsDiscountFrequencyBase (D θ : ℝ) : ℝ :=
  Real.sqrt (cepsMarkedUnitRadius D θ)

theorem cepsDiscountFrequencyBase_pos {D θ : ℝ} (hD : 0 < D) (hθ : 0 < θ) :
    0 < cepsDiscountFrequencyBase D θ :=
  Real.sqrt_pos.2 (cepsMarkedUnitRadius_pos hD hθ)

theorem cepsDiscountFrequency_mem {D θ : ℝ} (hD : 0 < D) (hθ : 0 < θ)
    {z b : ℂ} (hb : ‖b‖ * (1 + Real.sqrt ‖z‖) < cepsDiscountFrequencyBase D θ) :
    b ^ 2 * z ∈ ball (0 : ℂ) (cepsMarkedUnitRadius D θ) := by
  have hR := cepsMarkedUnitRadius_pos hD hθ
  have hs := Real.sqrt_nonneg ‖z‖
  have hx : ‖b‖ * Real.sqrt ‖z‖ < cepsDiscountFrequencyBase D θ := by
    nlinarith [norm_nonneg b]
  have hB := cepsDiscountFrequencyBase_pos hD hθ
  have hx0 := mul_nonneg (norm_nonneg b) hs
  rw [mem_ball_zero_iff, norm_mul, norm_pow]
  have hsq : (cepsDiscountFrequencyBase D θ) ^ 2 = cepsMarkedUnitRadius D θ :=
    Real.sq_sqrt hR.le
  have hsz := Real.sq_sqrt (norm_nonneg z)
  nlinarith

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledMarkedDiscount_frequency_budget {z b : ℂ}
    (hb : ‖b‖ * (1 + Real.sqrt ‖z‖) < cepsDiscountFrequencyBase D θ) :
    ‖cepsScaledMarkedDiscount ρW z b‖ ≤
      ‖z‖ * (cepsMarkedDiscountBound D θ / (θ / 2)) := by
  have hu := (cepsMarkedDiscountUnit_budget hW hθ hD).2.1 _
    (cepsDiscountFrequency_mem hD hθ hb)
  unfold cepsScaledMarkedDiscount cepsScaledDiscountUnit
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left hu (norm_nonneg _)

end PGM
