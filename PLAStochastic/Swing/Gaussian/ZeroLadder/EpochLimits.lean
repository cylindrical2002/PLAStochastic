import PLAStochastic.Swing.Gaussian.ZeroLadder.StoppedMoments
import PLAStochastic.ForMathlib.Probability.RandomWalk.Fluctuation.SymmetricLadderMeanCesaro

/-! # Limits and uniform moment bounds for the actual zero ladder epoch -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- Almost every actual path eventually leaves every zero survival event. -/
theorem gaussianLadderSurvives_eventually_not_ae
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, ω ∉ gaussianHalfLineSurvives X 0 0 n := by
  filter_upwards [gaussianHalfLineExit_zero_finite_ae hX hi hG (le_refl (0 : ℝ))]
    with ω hω
  obtain ⟨N, hN⟩ := WithTop.ne_top_iff_exists.mp hω
  filter_upwards [eventually_ge_atTop N] with n hn
  intro hs
  have ht := (lt_gaussianHalfLineExit_iff X 0 0 n ω).mpr hs
  rw [← hN] at ht
  exact (not_lt_of_ge hn) (WithTop.coe_lt_coe.mp ht)

theorem gaussianLadderSurvivalProbability_bounds (hi : iIndepFun X μ) (n : ℕ) :
    0 ≤ gaussianLadderSurvivalProbability X μ n ∧
      gaussianLadderSurvivalProbability X μ n ≤ 1 := by
  let := hi.isProbabilityMeasure
  exact ⟨measureReal_nonneg, measureReal_le_one⟩

/-- The actual survival probabilities tend to zero by finite hitting and domination. -/
theorem gaussianLadderSurvivalProbability_tendsto_zero
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    Tendsto (gaussianLadderSurvivalProbability X μ) atTop (𝓝 0) := by
  let := hi.isProbabilityMeasure
  have hd := tendsto_integral_of_dominated_convergence (fun _ : Ω => (1 : ℝ))
    (fun n => (measurable_const.indicator
      (gaussianLadderSurvives_measurable hX n)).aestronglyMeasurable)
    (integrable_const 1)
    (fun n => ae_of_all μ (fun ω => show
      ‖(gaussianHalfLineSurvives X 0 0 n).indicator (fun _ => (1 : ℝ)) ω‖ ≤ 1 from by
      by_cases h : ω ∈ gaussianHalfLineSurvives X 0 0 n <;> simp [h]))
    (by
      filter_upwards [gaussianLadderSurvives_eventually_not_ae hX hi hG] with ω hω
      show Tendsto (fun n : ℕ =>
        (gaussianHalfLineSurvives X 0 0 n).indicator (fun _ => (1 : ℝ)) ω)
        atTop (𝓝 0)
      apply tendsto_const_nhds.congr'
      filter_upwards [hω] with n hn
      simp [hn])
  change Tendsto (fun n => μ.real (gaussianHalfLineSurvives X 0 0 n)) atTop (𝓝 0)
  simpa only [integral_indicator (gaussianLadderSurvives_measurable hX _),
    setIntegral_const, smul_eq_mul, mul_one, integral_zero,
    ] using hd

/-- The stopped first moments converge to the actual renewal potential at zero. -/
theorem gaussianLadderSurvivingFirstMoment_tendsto
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    Tendsto (gaussianLadderSurvivingFirstMoment X μ) atTop
      (𝓝 (gaussianRenewalPotential X μ 0)) := by
  have hH := (gaussianHalfLineOvershoot_uniform_moments hX hi hG
    (le_refl (0 : ℝ)) le_rfl).1.1
  have hd := tendsto_integral_of_dominated_convergence (gaussianHalfLineOvershoot X 0 0)
    (fun n => ((gaussianHalfLineOvershoot_measurable hX 0 0).indicator
      (gaussianLadderSurvives_measurable hX n).compl).aestronglyMeasurable)
    hH
    (fun n => ae_of_all μ (fun ω => show
      ‖(gaussianHalfLineSurvives X 0 0 n)ᶜ.indicator (gaussianHalfLineOvershoot X 0 0) ω‖ ≤
        gaussianHalfLineOvershoot X 0 0 ω from by
      have hh := gaussianHalfLineOvershoot_nonneg X 0 0 ω
      by_cases h : ω ∈ gaussianHalfLineSurvives X 0 0 n <;>
        simp [h, Real.norm_eq_abs, abs_of_nonneg hh, hh]))
    (by
      filter_upwards [gaussianLadderSurvives_eventually_not_ae hX hi hG] with ω hω
      show Tendsto (fun n : ℕ =>
        (gaussianHalfLineSurvives X 0 0 n)ᶜ.indicator (gaussianHalfLineOvershoot X 0 0) ω)
        atTop (𝓝 (gaussianHalfLineOvershoot X 0 0 ω))
      apply tendsto_const_nhds.congr'
      filter_upwards [hω] with n hn
      simp [hn])
  simp only [integral_indicator (gaussianLadderSurvives_measurable hX _).compl] at hd
  simpa only [← gaussianLadderSurvivingFirstMoment_eq_exited hX hi hG,
    gaussianRenewalPotential, zero_add] using hd

theorem gaussianLadderSurvivingFirstMoment_bounds
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (n : ℕ) :
    0 ≤ gaussianLadderSurvivingFirstMoment X μ n ∧
      gaussianLadderSurvivingFirstMoment X μ n ≤ gaussianExcessExpMomentBound 2 := by
  rw [gaussianLadderSurvivingFirstMoment_eq_exited hX hi hG]
  have hH := (gaussianHalfLineOvershoot_uniform_moments hX hi hG
    (le_refl (0 : ℝ)) le_rfl).1
  exact ⟨integral_nonneg (gaussianHalfLineOvershoot_nonneg X 0 0),
    (setIntegral_le_integral hH.1 (ae_of_all _
      (gaussianHalfLineOvershoot_nonneg X 0 0))).trans hH.2⟩

theorem gaussianLadderExitedSecondMoment_bounds
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (n : ℕ) :
    0 ≤ gaussianLadderExitedSecondMoment X μ n ∧
      gaussianLadderExitedSecondMoment X μ n ≤ gaussianExcessExpMomentBound 2 := by
  have hH := (gaussianHalfLineOvershoot_uniform_moments hX hi hG
    (le_refl (0 : ℝ)) le_rfl).2
  exact ⟨integral_nonneg (fun ω => sq_nonneg (gaussianHalfLineOvershoot X 0 0 ω)),
    (setIntegral_le_integral hH.1 (ae_of_all _
      (fun ω => sq_nonneg (gaussianHalfLineOvershoot X 0 0 ω)))).trans hH.2⟩

theorem gaussianLadderSurvivingFirstMoment_abs_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (n : ℕ) :
    |gaussianLadderSurvivingFirstMoment X μ n| ≤ gaussianExcessExpMomentBound 2 := by
  rw [abs_of_nonneg (gaussianLadderSurvivingFirstMoment_bounds hX hi hG n).1]
  exact (gaussianLadderSurvivingFirstMoment_bounds hX hi hG n).2

theorem gaussianLadderExitedSecondMoment_abs_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (n : ℕ) :
    |gaussianLadderExitedSecondMoment X μ n| ≤ gaussianExcessExpMomentBound 2 := by
  rw [abs_of_nonneg (gaussianLadderExitedSecondMoment_bounds hX hi hG n).1]
  exact (gaussianLadderExitedSecondMoment_bounds hX hi hG n).2

end SwingRepair
