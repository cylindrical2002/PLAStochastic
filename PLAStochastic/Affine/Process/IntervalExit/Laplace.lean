import PLAStochastic.Affine.Process.IntervalExit.ExponentialStopping

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem intervalTouchClock_aemeasurable (hB : IsBrownianReal B μ)
    {r : ℝ} (hr : 0 < r) (x : ℝ) : AEMeasurable (intervalTouchClock B x r) μ :=
  (WithTop.measurable_untopD 0).comp_aemeasurable (intervalTouchTime_aemeasurable hB x hr)

theorem intervalTouchEndpoint_aemeasurable (hB : IsBrownianReal B μ)
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) : AEMeasurable (intervalTouchEndpoint B x r) μ := by
  have ht : AEMeasurable (fun ω => (intervalTouchClock B x r ω : ℝ)) μ :=
    NNReal.continuous_coe.measurable.comp_aemeasurable (intervalTouchClock_aemeasurable hB hr x)
  have hm := ((integral_actualBrownianExponentialWith_intervalTouch hB hr hx 1).1.aemeasurable.log.add (ht.div_const 2)).const_add x
  convert! hm using 1
  funext ω
  dsimp only [intervalTouchEndpoint,actualBrownianExponentialWith,Pi.add_apply]
  rw [Real.log_exp]
  ring

/-- Any shifted exponential martingale can be evaluated at the actual first contact. -/
theorem integral_shifted_exponential_intervalTouch (hB : IsBrownianReal B μ)
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) (c a : ℝ) :
    Integrable (fun ω => Real.exp (c*(a+B (intervalTouchClock B x r ω) ω)-
      (c^2/2)*(intervalTouchClock B x r ω : ℝ))) μ ∧
    (∫ ω, Real.exp (c*(a+B (intervalTouchClock B x r ω) ω)-
      (c^2/2)*(intervalTouchClock B x r ω : ℝ)) ∂μ) = Real.exp (c*a) := by
  have hi := integral_actualBrownianExponentialWith_intervalTouch hB hr hx c
  have he (ω : Ω) : Real.exp (c*(a+B (intervalTouchClock B x r ω) ω)-
      (c^2/2)*(intervalTouchClock B x r ω : ℝ)) =
      Real.exp (c*a)*actualBrownianExponentialWith B c (intervalTouchClock B x r ω) ω := by
    dsimp only [actualBrownianExponentialWith]
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [he]
  exact ⟨hi.1.const_mul _, by rw [integral_const_mul,hi.2,mul_one]⟩

/-- The actual discounted hyperbolic sine expectation follows from the two real
exponential martingales, with no exit law hypothesis. -/
theorem integral_discounted_sinh_intervalTouch (hB : IsBrownianReal B μ)
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) (k a : ℝ) :
    Integrable (fun ω => Real.exp (-(k^2/2)*(intervalTouchClock B x r ω : ℝ))*
      Real.sinh (k*(a+B (intervalTouchClock B x r ω) ω))) μ ∧
    (∫ ω, Real.exp (-(k^2/2)*(intervalTouchClock B x r ω : ℝ))*
      Real.sinh (k*(a+B (intervalTouchClock B x r ω) ω)) ∂μ) = Real.sinh (k*a) := by
  have hp := integral_shifted_exponential_intervalTouch hB hr hx k a
  have hn := integral_shifted_exponential_intervalTouch hB hr hx (-k) a
  have he (ω : Ω) : Real.exp (-(k^2/2)*(intervalTouchClock B x r ω : ℝ))*
      Real.sinh (k*(a+B (intervalTouchClock B x r ω) ω)) =
      (Real.exp (k*(a+B (intervalTouchClock B x r ω) ω)-(k^2/2)*(intervalTouchClock B x r ω : ℝ))-
       Real.exp ((-k)*(a+B (intervalTouchClock B x r ω) ω)-((-k)^2/2)*(intervalTouchClock B x r ω : ℝ)))/2 := by
    rw [Real.sinh_eq]
    rw [show k*(a+B (intervalTouchClock B x r ω) ω)-(k^2/2)*(intervalTouchClock B x r ω : ℝ) =
      -(k^2/2)*(intervalTouchClock B x r ω : ℝ)+k*(a+B (intervalTouchClock B x r ω) ω) by ring,
      show (-k)*(a+B (intervalTouchClock B x r ω) ω)-((-k)^2/2)*(intervalTouchClock B x r ω : ℝ) =
      -(k^2/2)*(intervalTouchClock B x r ω : ℝ)+ -(k*(a+B (intervalTouchClock B x r ω) ω)) by ring,
      Real.exp_add,Real.exp_add]
    ring
  simp only [he]
  refine ⟨(hp.1.sub hn.1).div_const _, ?_⟩
  rw [integral_div,integral_sub hp.1 hn.1,hp.2,hn.2,Real.sinh_eq]
  simp only [neg_mul]

end BrownianAffine
