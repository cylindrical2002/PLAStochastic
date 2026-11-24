import PLAStochastic.Index.CEPS.Normal.ZeroRootNumerator

/-! # The marked discount denominator and its actual zero jets -/

noncomputable section
open Complex MeasureTheory Set Metric
open PGM.WienerHopf
namespace PGM

def cepsMarkedDiscount (ρW : Measure ℝ) (t : ℂ) : ℂ := 1 - exp (-t) * stepTransform ρW t

theorem cepsD_marked_eq (ρW : Measure ℝ) (μ t : ℂ) :
    cepsD ρW μ (t * (1 + μ)) t = cepsMarkedDiscount ρW t := by
  unfold cepsD cepsMarkedDiscount
  rw [← exp_add, show -(t * (1 + μ)) + μ * t = -t by ring]

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsMarkedDiscount_analyticAt_zero : AnalyticAt ℂ (cepsMarkedDiscount ρW) 0 := by
  have hM := (differentiableOn_stepTransform_ball hW hθ hD.le).analyticAt
    (ball_mem_nhds 0 (div_pos hθ (by norm_num : (0 : ℝ) < 2)))
  exact analyticAt_const.sub (analyticAt_id.neg.cexp.mul hM)

include hW hθ hD in
theorem cepsMarkedDiscount_zero_jets : cepsMarkedDiscount ρW 0 = 0 ∧
    deriv (cepsMarkedDiscount ρW) 0 = 1 ∧
      deriv (deriv (cepsMarkedDiscount ρW)) 0 = -(cepsStepVar ρW : ℂ) - 1 := by
  let E := fun t : ℂ => exp (-t)
  have hE : AnalyticAt ℂ E 0 := analyticAt_id.neg.cexp
  have hEd : ∀ t : ℂ, HasDerivAt E (-exp (-t)) t := by
    intro t
    simpa only [E, Pi.neg_apply, id_eq, mul_neg_one] using! (hasDerivAt_id t).neg.cexp
  have hE1 : deriv E 0 = -1 := by simpa [E] using (hEd 0).deriv
  have hE2 : deriv (deriv E) 0 = 1 := by
    have he : deriv E = fun t : ℂ => -exp (-t) := funext fun t => (hEd t).deriv
    rw [he]
    simpa only [E, Pi.neg_apply, id_eq, neg_zero, exp_zero, mul_neg_one, neg_neg] using!
      (hEd 0).neg.deriv
  have hM := (differentiableOn_stepTransform_ball hW hθ hD.le).analyticAt
    (ball_mem_nhds 0 (div_pos hθ (by norm_num : (0 : ℝ) < 2)))
  have hMd := hM.differentiableAt.hasDerivAt
  rw [deriv_stepTransform_zero hW hθ hD.le] at hMd
  have hd := (hEd 0).fun_mul hMd |>.const_sub 1
  refine ⟨by simp [cepsMarkedDiscount, stepTransform_zero hW], ?_, ?_⟩
  · change deriv (fun t => 1 - E t * stepTransform ρW t) 0 = 1
    rw [hd.deriv]
    simp [E, stepTransform_zero hW]
  · have h1 : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) 0 := analyticAt_const
    have hEM : AnalyticAt ℂ (fun t => E t * stepTransform ρW t) 0 := hE.mul hM
    change deriv (deriv (fun t => 1 - E t * stepTransform ρW t)) 0 = _
    rw [deriv_deriv_sub_of_analyticAt h1 hEM, deriv_deriv_mul_of_analyticAt hE hM,
      hE1, hE2, stepTransform_zero hW, deriv_stepTransform_zero hW hθ hD.le,
      deriv_deriv_stepTransform_zero hW hθ hD.le]
    simp [E]
    ring

end PGM
