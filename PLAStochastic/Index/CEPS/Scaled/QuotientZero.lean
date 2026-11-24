import PLAStochastic.Index.CEPS.Scaled.QuotientCurve

/-! # Actual variance as the zero-scale quadratic-quotient value -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledQuotientAtRoot_zero (lam : ℝ) (z sign : ℂ) :
    cepsScaledQuotientAtRoot D θ ρW lam z sign 0 = (cepsStepVar ρW : ℂ) / 2 := by
  have hq : cepsComplexScaledDiscount lam z 0 = 0 := by simp [cepsComplexScaledDiscount]
  have hG : (fun w : ℂ => -cepsD ρW 0 0 w) = fun w => stepTransform ρW w - 1 := by
    funext w
    simp only [cepsD, neg_zero, exp_zero, zero_mul, one_mul]
    ring
  dsimp only [cepsScaledQuotientAtRoot, cepsScaledQuotient]
  simp only [zero_mul]
  rw [hq, hG, dslope_same]
  have hf := (differentiableOn_stepTransform_ball hW hθ hD.le).sub_const 1
  have h0 : (0 : ℂ) ∈ ball 0 (θ / 2) := mem_ball_self (half_pos hθ)
  rw [cepsNormal_deriv_dslope_eq_integral hf h0 h0]
  simp only [sub_self, mul_zero, add_zero]
  have he : deriv (fun w : ℂ => stepTransform ρW w - 1) = deriv (stepTransform ρW) := by
    funext w
    rw [deriv_sub_const]
  rw [he, deriv_deriv_stepTransform_zero hW hθ hD.le,
    intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal, integral_id]
  norm_num
  ring

end PGM
