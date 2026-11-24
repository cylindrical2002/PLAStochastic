import PLAStochastic.Swing.Gaussian.Stopping.StoppedQuadraticDrift
import PLAStochastic.ForMathlib.Probability.Process.CappedStopping.Mean

/-! # True stopped linear drift of the actual Gaussian walk -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- The selected increment has its mean computed by original-past independence,
with the true survival indicator retained. -/
theorem gaussianStrip_linear_step_eq
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (x a R : ℝ) (n : ℕ) :
    (∫ ω, if (n : WithTop ℕ) < gaussianStripExit X x a R ω then
      gaussianDriftWalk X x a (n+1) ω - gaussianDriftWalk X x a n ω else 0 ∂μ) =
      a * μ.real {ω | (n : WithTop ℕ) < gaussianStripExit X x a R ω} := by
  have : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  let A := gaussianStripSurvives X x a R n
  let F := A.indicator (fun _ => (1 : ℝ))
  have hAp : MeasurableSet[incrementIndexSpace X (Iio n)] A :=
    gaussianStripSurvives_measurable_past X x a R n
  have hA : MeasurableSet A := incrementIndexSpace_le hX _ _ hAp
  have hFp : Measurable[incrementIndexSpace X (Iio n)] F := by
    let : MeasurableSpace Ω := incrementIndexSpace X (Iio n)
    exact measurable_const.indicator hAp
  have hF : Integrable F μ := (integrable_const _).indicator hA
  have hZ := (iid_standardGaussian_hasGaussianLaw hX hG n).integrable
  have hiF := past_statistic_indep_currentIncrement hX hi n hFp
  have hprod : Integrable (fun ω => F ω * X n ω) μ := hiF.integrable_mul hF hZ
  have he (ω : Ω) :
      (if (n : WithTop ℕ) < gaussianStripExit X x a R ω then
      gaussianDriftWalk X x a (n+1) ω - gaussianDriftWalk X x a n ω else 0) =
        F ω * X n ω + a*F ω := by
    by_cases h : ω ∈ A
    · have hh := (lt_gaussianStripExit_iff X x a R n ω).mpr h
      simp only [if_pos hh, F, indicator_of_mem h, gaussianDriftWalk_succ]
      ring
    · have hh : ¬ (n : WithTop ℕ) < gaussianStripExit X x a R ω :=
        fun hn => h ((lt_gaussianStripExit_iff X x a R n ω).mp hn)
      simp only [if_neg hh, F, indicator_of_notMem h, zero_mul, mul_zero, add_zero]
  rw [integral_congr_ae (Eventually.of_forall he), integral_add hprod (hF.const_mul a),
    hiF.integral_fun_mul_eq_mul_integral hF.aestronglyMeasurable hZ.aestronglyMeasurable,
    (iid_standardGaussian_mean_variance hX hG n).1, mul_zero, zero_add, integral_const_mul,
    integral_indicator hA, setIntegral_const]
  simp only [smul_eq_mul, mul_one]
  congr 2
  ext ω
  exact (lt_gaussianStripExit_iff X x a R n ω).symm

/-- Exact bounded Wald identity with no prior assertion that the exit time is finite. -/
theorem gaussianStrip_capped_position_integral
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (x a R : ℝ) (m : ℕ) :
    (∫ ω, gaussianDriftWalk X x a (capDiscreteTime (gaussianStripExit X x a R ω) m) ω ∂μ) =
      x + a * ∫ ω, (capDiscreteTime (gaussianStripExit X x a R ω) m : ℝ) ∂μ := by
  have : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hτ : Measurable[mΩ] (gaussianStripExit X x a R) :=
    (gaussianStripExit_isStoppingTime hX x a R).measurable'
  rw [integral_capDiscreteTime_potential hτ
    (fun n => (gaussianDriftWalk_memLp_two hX hG x a n).integrable (by norm_num)),
    integral_capDiscreteTime hτ]
  simp_rw [gaussianStrip_linear_step_eq hX hi hG x a R]
  simp only [gaussianDriftWalk_zero, integral_const, measureReal_def, measure_univ,
    ENNReal.toReal_one, smul_eq_mul, one_mul, Finset.mul_sum]

end SwingRepair
