import PLAStochastic.Swing.Gaussian.ZeroLadder.MinimumDecomposition

/-! # Actual stopped first and second moments at the zero ladder epoch -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

def gaussianLadderSurvivalProbability (X : ℕ → Ω → ℝ) (μ : Measure Ω) (n : ℕ) : ℝ :=
  μ.real (gaussianHalfLineSurvives X 0 0 n)

def gaussianLadderSurvivingFirstMoment (X : ℕ → Ω → ℝ) (μ : Measure Ω) (n : ℕ) : ℝ :=
  ∫ ω in gaussianHalfLineSurvives X 0 0 n, cumulativeSamples X n ω ∂μ

def gaussianLadderSurvivingSecondMoment (X : ℕ → Ω → ℝ) (μ : Measure Ω) (n : ℕ) : ℝ :=
  ∫ ω in gaussianHalfLineSurvives X 0 0 n, (cumulativeSamples X n ω)^2 ∂μ

def gaussianLadderExitedSecondMoment (X : ℕ → Ω → ℝ) (μ : Measure Ω) (n : ℕ) : ℝ :=
  ∫ ω in (gaussianHalfLineSurvives X 0 0 n)ᶜ, (gaussianHalfLineOvershoot X 0 0 ω)^2 ∂μ

theorem gaussianLadderSurvives_measurable (hX : ∀ n, Measurable (X n)) (n : ℕ) :
    MeasurableSet (gaussianHalfLineSurvives X 0 0 n) :=
  incrementIndexSpace_le hX _ _ (gaussianHalfLineSurvives_measurable_past X 0 0 n)

theorem gaussianZeroWalk_memLp_two (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (n : ℕ) :
    MemLp (cumulativeSamples X n) 2 μ := by
  let := hi.isProbabilityMeasure
  convert gaussianDriftWalk_memLp_two hX hG 0 0 n using 1
  funext ω
  simp [gaussianDriftWalk]

theorem gaussianHalfLine_zero_step_first (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (n : ℕ) :
    (∫ ω, if (n : WithTop ℕ) < gaussianHalfLineExit X 0 0 ω then
      cumulativeSamples X (n+1) ω-cumulativeSamples X n ω else 0 ∂μ) = 0 := by
  let := hi.isProbabilityMeasure
  let A := gaussianHalfLineSurvives X 0 0 n
  let F := A.indicator (fun _ => (1 : ℝ))
  have hAp := gaussianHalfLineSurvives_measurable_past X 0 0 n
  have hA := gaussianLadderSurvives_measurable hX n
  have hFp : Measurable[incrementIndexSpace X (Iio n)] F := by
    let : MeasurableSpace Ω := incrementIndexSpace X (Iio n)
    exact measurable_const.indicator hAp
  have hF : Integrable F μ := (integrable_const _).indicator hA
  have hZ := (iid_standardGaussian_hasGaussianLaw hX hG n).integrable
  have hind := past_statistic_indep_currentIncrement hX hi n hFp
  have he (ω : Ω) :
      (if (n : WithTop ℕ) < gaussianHalfLineExit X 0 0 ω then
        cumulativeSamples X (n+1) ω-cumulativeSamples X n ω else 0) = F ω*X n ω := by
    by_cases h : ω ∈ A
    · simp only [if_pos ((lt_gaussianHalfLineExit_iff X 0 0 n ω).mpr h),
        F, indicator_of_mem h, one_mul, cumulativeSamples_succ, add_sub_cancel_left]
    · simp only [if_neg (fun hh => h ((lt_gaussianHalfLineExit_iff X 0 0 n ω).mp hh)),
        F, indicator_of_notMem h, zero_mul]
  rw [integral_congr_ae (ae_of_all _ he),
    hind.integral_fun_mul_eq_mul_integral hF.aestronglyMeasurable hZ.aestronglyMeasurable,
    (iid_standardGaussian_mean_variance hX hG n).1, mul_zero]

theorem gaussianHalfLine_zero_step_second (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (n : ℕ) :
    (∫ ω, if (n : WithTop ℕ) < gaussianHalfLineExit X 0 0 ω then
      (cumulativeSamples X (n+1) ω)^2-(cumulativeSamples X n ω)^2 else 0 ∂μ) =
      gaussianLadderSurvivalProbability X μ n := by
  let := hi.isProbabilityMeasure
  let A := gaussianHalfLineSurvives X 0 0 n
  let F := A.indicator (fun ω => 2*cumulativeSamples X n ω)
  let G := A.indicator (fun _ => (1 : ℝ))
  have hAp := gaussianHalfLineSurvives_measurable_past X 0 0 n
  have hA := gaussianLadderSurvives_measurable hX n
  have hSp : Measurable[incrementIndexSpace X (Iio n)] (cumulativeSamples X n) := by
    convert gaussianDriftWalk_measurable_past X 0 0 n using 1
    funext ω
    simp [gaussianDriftWalk]
  have hFp : Measurable[incrementIndexSpace X (Iio n)] F := by
    let : MeasurableSpace Ω := incrementIndexSpace X (Iio n)
    exact (hSp.const_mul 2).indicator hAp
  have hGp : Measurable[incrementIndexSpace X (Iio n)] G := by
    let : MeasurableSpace Ω := incrementIndexSpace X (Iio n)
    exact measurable_const.indicator hAp
  have hF : Integrable F μ := ((gaussianZeroWalk_memLp_two hX hi hG n).integrable
    (by norm_num)).const_mul 2 |>.indicator hA
  have hGi : Integrable G μ := (integrable_const _).indicator hA
  have hZ := (iid_standardGaussian_hasGaussianLaw hX hG n).integrable
  have hZ2 := (iid_standardGaussian_hasGaussianLaw hX hG n).memLp_two.integrable_sq
  have hIF := past_statistic_indep_currentIncrement hX hi n hFp
  have hIG : IndepFun G (fun ω => (X n ω)^2) μ :=
    (past_statistic_indep_currentIncrement hX hi n hGp).comp measurable_id
      (show Measurable (fun z : ℝ => z^2) by fun_prop)
  have hP : Integrable (fun ω => F ω*X n ω) μ := hIF.integrable_mul hF hZ
  have hQ : Integrable (fun ω => G ω*(X n ω)^2) μ := hIG.integrable_mul hGi hZ2
  have hz2 : (∫ ω, (X n ω)^2 ∂μ) = 1 := by
    have hl : HasLaw (X n) (gaussianReal 0 1) μ := ⟨(hX n).aemeasurable, hG n⟩
    exact (hl.integral_comp (show AEStronglyMeasurable (fun z : ℝ => z^2)
      (gaussianReal 0 1) by fun_prop)).trans integral_sq_standardGaussian
  have he (ω : Ω) :
      (if (n : WithTop ℕ) < gaussianHalfLineExit X 0 0 ω then
        (cumulativeSamples X (n+1) ω)^2-(cumulativeSamples X n ω)^2 else 0) =
      F ω*X n ω+G ω*(X n ω)^2 := by
    by_cases h : ω ∈ A
    · simp only [if_pos ((lt_gaussianHalfLineExit_iff X 0 0 n ω).mpr h),
        F, G, indicator_of_mem h, one_mul, cumulativeSamples_succ]
      ring
    · simp only [if_neg (fun hh => h ((lt_gaussianHalfLineExit_iff X 0 0 n ω).mp hh)),
        F, G, indicator_of_notMem h, zero_mul, add_zero]
  rw [integral_congr_ae (ae_of_all _ he), integral_add hP hQ,
    hIF.integral_fun_mul_eq_mul_integral hF.aestronglyMeasurable hZ.aestronglyMeasurable,
    hIG.integral_fun_mul_eq_mul_integral hGi.aestronglyMeasurable hZ2.aestronglyMeasurable,
    (iid_standardGaussian_mean_variance hX hG n).1, hz2, mul_zero, zero_add, mul_one,
    integral_indicator hA, setIntegral_const]
  simp only [gaussianLadderSurvivalProbability, smul_eq_mul, mul_one]

theorem gaussianHalfLine_zero_capped_first (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (n : ℕ) :
    (∫ ω, cumulativeSamples X (capDiscreteTime (gaussianHalfLineExit X 0 0 ω) n) ω ∂μ) = 0 := by
  let := hi.isProbabilityMeasure
  rw [integral_capDiscreteTime_potential (gaussianHalfLineExit_isStoppingTime hX 0 0).measurable'
    (fun k => (gaussianZeroWalk_memLp_two hX hi hG k).integrable (by norm_num))]
  simp only [gaussianHalfLine_zero_step_first hX hi hG, cumulativeSamples_zero,
    integral_zero, Finset.sum_const_zero, add_zero]

theorem gaussianHalfLine_zero_capped_second (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (n : ℕ) :
    (∫ ω, (cumulativeSamples X (capDiscreteTime (gaussianHalfLineExit X 0 0 ω) n) ω)^2 ∂μ) =
      ∑ j ∈ Finset.range n, gaussianLadderSurvivalProbability X μ j := by
  rw [integral_capDiscreteTime_potential (gaussianHalfLineExit_isStoppingTime hX 0 0).measurable'
    (fun k => (gaussianZeroWalk_memLp_two hX hi hG k).integrable_sq)]
  simp only [gaussianHalfLine_zero_step_second hX hi hG, cumulativeSamples_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero, zero_add]

omit [MeasurableSpace Ω] in
theorem gaussianHalfLine_zero_capped_eq (n : ℕ) (ω : Ω) :
    cumulativeSamples X (capDiscreteTime (gaussianHalfLineExit X 0 0 ω) n) ω =
      if ω ∈ gaussianHalfLineSurvives X 0 0 n then cumulativeSamples X n ω
      else -gaussianHalfLineOvershoot X 0 0 ω := by
  by_cases h : ω ∈ gaussianHalfLineSurvives X 0 0 n
  · rw [if_pos h, capDiscreteTime_eq_of_lt ((lt_gaussianHalfLineExit_iff X 0 0 n ω).mpr h)]
  · have hle : gaussianHalfLineExit X 0 0 ω ≤ n :=
      le_of_not_gt (fun hh => h ((lt_gaussianHalfLineExit_iff X 0 0 n ω).mp hh))
    have ht := ne_top_of_le_ne_top WithTop.coe_ne_top hle
    rw [if_neg h, capDiscreteTime_eq_of_le hle, gaussianHalfLineOvershoot, if_neg ht]
    simp only [gaussianHalfLineExitPosition, gaussianDriftWalk, neg_neg,
      zero_add, zero_mul, add_zero]

theorem gaussianLadderSurvivingFirstMoment_eq_exited (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (n : ℕ) :
    gaussianLadderSurvivingFirstMoment X μ n =
      ∫ ω in (gaussianHalfLineSurvives X 0 0 n)ᶜ, gaussianHalfLineOvershoot X 0 0 ω ∂μ := by
  let := hi.isProbabilityMeasure
  have hA := gaussianLadderSurvives_measurable hX n
  have hS := (gaussianZeroWalk_memLp_two hX hi hG n).integrable (by norm_num)
  have hH := (gaussianHalfLineOvershoot_uniform_moments hX hi hG (le_refl (0 : ℝ)) le_rfl).1.1
  have he : (fun ω => cumulativeSamples X (capDiscreteTime (gaussianHalfLineExit X 0 0 ω) n) ω) =
      (gaussianHalfLineSurvives X 0 0 n).indicator (cumulativeSamples X n) -
      (gaussianHalfLineSurvives X 0 0 n)ᶜ.indicator (gaussianHalfLineOvershoot X 0 0) := by
    funext ω
    rw [gaussianHalfLine_zero_capped_eq]
    by_cases h : ω ∈ gaussianHalfLineSurvives X 0 0 n <;> simp [h]
  have hc := gaussianHalfLine_zero_capped_first hX hi hG n
  rw [he, integral_sub' (hS.indicator hA) (hH.indicator hA.compl),
    integral_indicator hA, integral_indicator hA.compl] at hc
  exact sub_eq_zero.mp hc

theorem gaussianLadderSurvivingSecondMoment_eq (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (n : ℕ) :
    gaussianLadderSurvivingSecondMoment X μ n =
      (∑ j ∈ Finset.range n, gaussianLadderSurvivalProbability X μ j) -
        gaussianLadderExitedSecondMoment X μ n := by
  have hA := gaussianLadderSurvives_measurable hX n
  have hS := (gaussianZeroWalk_memLp_two hX hi hG n).integrable_sq
  have hH := (gaussianHalfLineOvershoot_uniform_moments hX hi hG (le_refl (0 : ℝ)) le_rfl).2.1
  have he : (fun ω => (cumulativeSamples X (capDiscreteTime (gaussianHalfLineExit X 0 0 ω) n) ω)^2) =
      (gaussianHalfLineSurvives X 0 0 n).indicator (fun ω => (cumulativeSamples X n ω)^2) +
      (gaussianHalfLineSurvives X 0 0 n)ᶜ.indicator (fun ω => (gaussianHalfLineOvershoot X 0 0 ω)^2) := by
    funext ω
    rw [gaussianHalfLine_zero_capped_eq]
    by_cases h : ω ∈ gaussianHalfLineSurvives X 0 0 n <;> simp [h]
  have hc := gaussianHalfLine_zero_capped_second hX hi hG n
  rw [he, integral_add' (hS.indicator hA) (hH.indicator hA.compl),
    integral_indicator hA, integral_indicator hA.compl] at hc
  exact eq_sub_of_add_eq hc

end SwingRepair
