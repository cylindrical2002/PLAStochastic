import PLAStochastic.Affine.Process.IntervalExit.Laplace
import PLAStochastic.ForMathlib.MeasureTheory.Measure.PositiveLaplaceUniqueness

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- The true time law restricted to paths exiting at the specified endpoint. -/
def intervalExitSideMeasure {Ω : Type*} [MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ)
    (μ : Measure Ω) (x r side : ℝ) : Measure ℝ :=
  (μ.restrict {ω | intervalTouchEndpoint B x r ω = side}).map
    (fun ω => (intervalTouchClock B x r ω : ℝ))

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem intervalExitSideMeasure_ae_nonneg (hB : IsBrownianReal B μ)
    {r : ℝ} (hr : 0 < r) (x side : ℝ) :
    ∀ᵐ t ∂intervalExitSideMeasure B μ x r side, 0 ≤ t := by
  apply (ae_map_iff ((intervalTouchClock_aemeasurable hB hr x).coe_nnreal_real.restrict)
    measurableSet_Ici).mpr
  exact Eventually.of_forall (fun ω => (intervalTouchClock B x r ω).property)

theorem integral_intervalExitSideMeasure (hB : IsBrownianReal B μ)
    {r : ℝ} (hr : 0 < r) (x side : ℝ) {g : ℝ → ℝ} (hg : Measurable g) :
    (∫ t, g t ∂intervalExitSideMeasure B μ x r side) =
      ∫ ω in {ω | intervalTouchEndpoint B x r ω = side}, g (intervalTouchClock B x r ω) ∂μ := by
  apply integral_map ((intervalTouchClock_aemeasurable hB hr x).coe_nnreal_real.restrict)
    hg.aestronglyMeasurable

theorem integrable_intervalExitSideMeasure_exp (hB : IsBrownianReal B μ)
    {r lam : ℝ} (hr : 0 < r) (hlam : 0 ≤ lam) (x side : ℝ) :
    Integrable (fun t => Real.exp (-lam*t)) (intervalExitSideMeasure B μ x r side) := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have : IsFiniteMeasure (intervalExitSideMeasure B μ x r side) := by
    unfold intervalExitSideMeasure
    infer_instance
  apply Integrable.of_bound (by fun_prop) 1
  filter_upwards [intervalExitSideMeasure_ae_nonneg hB hr x side] with t ht
  rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
  exact Real.exp_le_one_iff.mpr (by nlinarith)

theorem integral_intervalExitSideMeasure_right_laplace (hB : IsBrownianReal B μ)
    {r x k : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) (hk : 0 < k) :
    (∫ t, Real.exp (-(k^2/2)*t) ∂intervalExitSideMeasure B μ x r r) =
      Real.sinh (k*x)/Real.sinh (k*r) := by
  let D : Ω → ℝ := fun ω => Real.exp (-(k^2/2)*(intervalTouchClock B x r ω : ℝ))
  have hset : NullMeasurableSet {ω | intervalTouchEndpoint B x r ω = r} μ :=
    (intervalTouchEndpoint_aemeasurable hB hr hx).nullMeasurableSet_preimage (measurableSet_singleton r)
  have hi := (integral_discounted_sinh_intervalTouch hB hr hx k x).2
  have he : (fun ω => D ω*Real.sinh (k*intervalTouchEndpoint B x r ω)) =ᵐ[μ]
      (fun ω => Real.sinh (k*r)*({ω | intervalTouchEndpoint B x r ω = r}.indicator D ω)) := by
    filter_upwards [intervalTouchEndpoint_boundary_ae hB hr hx] with ω hω
    rcases hω with hω | hω
    · simp only [hω,mul_zero,Real.sinh_zero,indicator_apply,mem_ofPred_eq]
      simp only [Ne.symm hr.ne',if_false,mul_zero]
    · simp only [hω,indicator_apply,mem_ofPred_eq,if_true]
      ring
  change (∫ ω, D ω*Real.sinh (k*intervalTouchEndpoint B x r ω) ∂μ) = _ at hi
  rw [integral_congr_ae he,integral_const_mul,integral_indicator₀ hset] at hi
  rw [integral_intervalExitSideMeasure hB hr x r (by fun_prop)]
  exact (eq_div_iff (Real.sinh_pos_iff.mpr (mul_pos hk hr)).ne').mpr (by simpa only [D,mul_comm] using hi)

theorem integral_intervalExitSideMeasure_left_laplace (hB : IsBrownianReal B μ)
    {r x k : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) (hk : 0 < k) :
    (∫ t, Real.exp (-(k^2/2)*t) ∂intervalExitSideMeasure B μ x r 0) =
      Real.sinh (k*(r-x))/Real.sinh (k*r) := by
  let D : Ω → ℝ := fun ω => Real.exp (-(k^2/2)*(intervalTouchClock B x r ω : ℝ))
  have hset : NullMeasurableSet {ω | intervalTouchEndpoint B x r ω = 0} μ :=
    (intervalTouchEndpoint_aemeasurable hB hr hx).nullMeasurableSet_preimage (measurableSet_singleton 0)
  have hi := (integral_discounted_sinh_intervalTouch hB hr hx k (x-r)).2
  have he : (fun ω => D ω*Real.sinh (k*((x-r)+B (intervalTouchClock B x r ω) ω))) =ᵐ[μ]
      (fun ω => -Real.sinh (k*r)*({ω | intervalTouchEndpoint B x r ω = 0}.indicator D ω)) := by
    filter_upwards [intervalTouchEndpoint_boundary_ae hB hr hx] with ω hω
    have heq : (x-r)+B (intervalTouchClock B x r ω) ω = intervalTouchEndpoint B x r ω-r := by
      dsimp only [intervalTouchEndpoint]
      ring
    rw [heq]
    rcases hω with hω | hω
    · simp only [hω,zero_sub,mul_neg,Real.sinh_neg,indicator_apply,mem_ofPred_eq,if_true]
      ring
    · simp only [hω,sub_self,mul_zero,Real.sinh_zero,indicator_apply,mem_ofPred_eq,hr.ne',if_false,mul_zero]
  change (∫ ω, D ω*Real.sinh (k*((x-r)+B (intervalTouchClock B x r ω) ω)) ∂μ) = _ at hi
  rw [integral_congr_ae he,integral_const_mul,integral_indicator₀ hset] at hi
  rw [show k*(x-r)=-(k*(r-x)) by ring,Real.sinh_neg] at hi
  rw [integral_intervalExitSideMeasure hB hr x 0 (by fun_prop)]
  apply (eq_div_iff (Real.sinh_pos_iff.mpr (mul_pos hk hr)).ne').mpr
  dsimp only [D] at hi
  nlinarith

end BrownianAffine
