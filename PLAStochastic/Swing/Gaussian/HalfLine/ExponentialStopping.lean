import PLAStochastic.Swing.Gaussian.HalfLine.Overshoot
import PLAStochastic.Swing.Gaussian.Stopping.ExitWald
import Mathlib.Probability.StrongLaw

/-! Exponential stopping for the true first negative position. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- Fixed-time exponential integrability follows from the actual Gaussian sum law. -/
theorem gaussianDriftWalk_integrable_exp
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (x a c : ℝ) (n : ℕ) :
    Integrable (fun ω => Real.exp (c*gaussianDriftWalk X x a n ω)) μ := by
  have hs : HasGaussianLaw (cumulativeSamples X n) μ :=
    (iid_standardGaussian_isGaussianProcess hX hi hG).hasGaussianLaw_fun_sum
  have he : Integrable (fun ω => Real.exp (c*cumulativeSamples X n ω)) μ := by
    apply (integrable_map_measure (g := fun z : ℝ => Real.exp (c*z))
      (by fun_prop) hs.aemeasurable).mp
    rw [hs.map_eq_gaussianReal]
    exact integrable_exp_mul_gaussianReal c
  apply (he.const_mul (Real.exp (c*(x+a*n)))).congr
  exact ae_of_all _ (fun ω => by dsimp only; rw [← Real.exp_add]; congr 1; dsimp [gaussianDriftWalk]; ring)

/-- The one-step exponential factor has expectation one for the actual fresh Gaussian. -/
theorem gaussianDrift_exponential_factor_integral
    (hX : ∀ n, Measurable (X n))
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (a : ℝ) (n : ℕ) :
    (∫ ω, Real.exp (-2*a*(X n ω+a)) ∂μ) = 1 := by
  have hl : HasLaw (X n) (gaussianReal 0 1) μ := ⟨(hX n).aemeasurable, hG n⟩
  have he := hl.integral_comp (show AEStronglyMeasurable (fun z : ℝ => Real.exp (-2*a*(z+a)))
    (gaussianReal 0 1) by fun_prop)
  dsimp only [Function.comp_def] at he
  rw [he]
  have hg := gaussianExpShift_integral (-a) (-2*a)
  simpa only [sub_neg_eq_add, show -(-2*a)*(-a)+(-2*a)^2/2 = (0 : ℝ) by ring,
    Real.exp_zero] using hg

theorem gaussianHalfLine_exp_step_integral
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (x a : ℝ) (n : ℕ) :
    (∫ ω, if (n : WithTop ℕ) < gaussianHalfLineExit X x a ω then
      Real.exp (-2*a*gaussianDriftWalk X x a (n+1) ω) -
      Real.exp (-2*a*gaussianDriftWalk X x a n ω) else 0 ∂μ) = 0 := by
  have := hi.isProbabilityMeasure
  let A := gaussianHalfLineSurvives X x a n
  let F := A.indicator (fun ω => Real.exp (-2*a*gaussianDriftWalk X x a n ω))
  let Z := fun ω => Real.exp (-2*a*(X n ω+a))
  have hAp : MeasurableSet[incrementIndexSpace X (Iio n)] A :=
    gaussianHalfLineSurvives_measurable_past X x a n
  have hA : MeasurableSet A := incrementIndexSpace_le hX _ _ hAp
  have hFp : Measurable[incrementIndexSpace X (Iio n)] F := by
    let : MeasurableSpace Ω := incrementIndexSpace X (Iio n)
    exact ((gaussianDriftWalk_measurable_past X x a n).const_mul (-2*a)).exp.indicator hAp
  have hF : Integrable F μ := (gaussianDriftWalk_integrable_exp hX hi hG x a (-2*a) n).indicator hA
  have hZ : Integrable Z μ := by
    apply (integrable_map_measure (g := fun z : ℝ => Real.exp (-2*a*(z+a)))
      (μ := μ) (by fun_prop) (hX n).aemeasurable).mp
    rw [hG n]
    simpa only [sub_neg_eq_add] using gaussianExpShift_integrable (-a) (-2*a)
  have hiF : IndepFun F Z μ := (past_statistic_indep_currentIncrement hX hi n hFp).comp
    measurable_id (show Measurable (fun z : ℝ => Real.exp (-2*a*(z+a))) by fun_prop)
  have hp : Integrable (fun ω => F ω*Z ω) μ := hiF.integrable_mul hF hZ
  have he (ω : Ω) :
      (if (n : WithTop ℕ) < gaussianHalfLineExit X x a ω then
      Real.exp (-2*a*gaussianDriftWalk X x a (n+1) ω) -
      Real.exp (-2*a*gaussianDriftWalk X x a n ω) else 0) = F ω*Z ω-F ω := by
    by_cases h : ω ∈ A
    · have hh := (lt_gaussianHalfLineExit_iff X x a n ω).mpr h
      simp only [if_pos hh, F, indicator_of_mem h, Z, gaussianDriftWalk_succ]
      rw [← Real.exp_add]
      congr 2
      ring
    · have hh : ¬ (n : WithTop ℕ) < gaussianHalfLineExit X x a ω :=
        fun hh => h ((lt_gaussianHalfLineExit_iff X x a n ω).mp hh)
      simp only [if_neg hh, F, indicator_of_notMem h, zero_mul, sub_zero]
  rw [integral_congr_ae (ae_of_all _ he), integral_sub hp hF,
    hiF.integral_fun_mul_eq_mul_integral hF.aestronglyMeasurable hZ.aestronglyMeasurable]
  change (∫ ω, F ω ∂μ) * (∫ ω, Real.exp (-2*a*(X n ω+a)) ∂μ) - (∫ ω, F ω ∂μ) = 0
  rw [gaussianDrift_exponential_factor_integral hX hG, mul_one, sub_self]

/-- The bounded stopping identity is proved before sending the horizon to infinity. -/
theorem gaussianHalfLine_capped_exp_integral
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (x a : ℝ) (m : ℕ) :
    (∫ ω, Real.exp (-2*a*gaussianDriftWalk X x a
      (capDiscreteTime (gaussianHalfLineExit X x a ω) m) ω) ∂μ) = Real.exp (-2*a*x) := by
  have := hi.isProbabilityMeasure
  rw [integral_capDiscreteTime_potential (gaussianHalfLineExit_isStoppingTime hX x a).measurable'
    (gaussianDriftWalk_integrable_exp hX hi hG x a (-2*a))]
  simp only [gaussianHalfLine_exp_step_integral hX hi hG, Finset.sum_const_zero, add_zero,
    gaussianDriftWalk_zero, integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
    smul_eq_mul, one_mul]

/-- The actual centered Gaussian walk satisfies the strong law. -/
theorem gaussianDriftWalk_strongLaw
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (x a : ℝ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => gaussianDriftWalk X x a n ω / n) atTop (𝓝 a) := by
  have hid (n : ℕ) : IdentDistrib (X n) (X 0) μ μ :=
    (show HasLaw (X n) (gaussianReal 0 1) μ from ⟨(hX n).aemeasurable, hG n⟩).identDistrib
      ⟨(hX 0).aemeasurable, hG 0⟩
  have hs := strong_law_ae_real X (iid_standardGaussian_hasGaussianLaw hX hG 0).integrable
    (fun _ _ hne => hi.indepFun hne) hid
  rw [(iid_standardGaussian_mean_variance hX hG 0).1] at hs
  filter_upwards [hs] with ω hω
  have hc : Tendsto (fun n : ℕ => x / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have ht := (hc.add hω).add_const a
  simp only [zero_add] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  dsimp [gaussianDriftWalk, cumulativeSamples]
  field_simp


/-- Positive drift sends the true unstopped exponential to zero almost surely. -/
theorem gaussianDriftWalk_exp_tendsto_zero
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (x : ℝ) {a : ℝ} (ha : 0 < a) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => Real.exp (-2*a*gaussianDriftWalk X x a n ω))
      atTop (𝓝 0) := by
  filter_upwards [gaussianDriftWalk_strongLaw hX hi hG x a] with ω hω
  have hs : Tendsto (gaussianDriftWalk X x a · ω) atTop atTop := by
    have ht := Tendsto.atTop_mul_pos ha tendsto_natCast_atTop_atTop hω
    apply ht.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    field_simp
  have ht := Real.tendsto_exp_atBot.comp
    (tendsto_neg_atTop_atBot.comp (hs.const_mul_atTop (show 0 < 2*a by positivity)))
  simpa only [Function.comp_def, neg_mul] using ht

/-- Sending the bounded stopping horizon to infinity includes the never-hit paths explicitly. -/
theorem gaussianHalfLine_overshoot_identity
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {x a : ℝ} (hx : 0 ≤ x) (ha : 0 < a) :
    Real.exp (-2*a*x) = ∫ ω in {ω | gaussianHalfLineExit X x a ω ≠ ⊤},
      Real.exp (2*a*gaussianHalfLineOvershoot X x a ω) ∂μ := by
  have := hi.isProbabilityMeasure
  let F := fun m ω => Real.exp (-2*a*gaussianDriftWalk X x a
    (capDiscreteTime (gaussianHalfLineExit X x a ω) m) ω)
  let G := fun ω => if gaussianHalfLineExit X x a ω = ⊤ then 0
    else Real.exp (2*a*gaussianHalfLineOvershoot X x a ω)
  have hlim : Tendsto (fun m : ℕ => ∫ ω, F m ω ∂μ) atTop (𝓝 (∫ ω, G ω ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun ω => Real.exp (2*a*gaussianHalfLineOvershoot X x a ω))
    · intro m
      exact ((countableSelection_measurable (gaussianDriftWalk_measurable hX x a)
        (capDiscreteTime_measurable (gaussianHalfLineExit_isStoppingTime hX x a).measurable' m)).const_mul
          (-2*a)).exp.aestronglyMeasurable
    · exact gaussianHalfLineOvershoot_integrable_exp hX hi hG hx ha.le (by positivity)
    · intro m
      apply ae_of_all
      intro ω
      change ‖Real.exp _‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      have hb := gaussianHalfLine_capped_position_lower (X := X) (x := x) (a := a) m ω
      nlinarith [mul_le_mul_of_nonneg_left hb (show 0 ≤ 2*a by positivity)]
    · filter_upwards [gaussianDriftWalk_exp_tendsto_zero hX hi hG x ha] with ω hω
      by_cases ht : gaussianHalfLineExit X x a ω = ⊤
      · simpa only [F, G, ht, if_pos, capDiscreteTime, WithTop.untopD_top, min_self] using hω
      · apply tendsto_const_nhds.congr'
        filter_upwards [capDiscreteTime_eventually_eq ht] with m hm
        simp only [F, G, hm, gaussianHalfLineOvershoot, if_neg ht,
          gaussianHalfLineExitPosition]
        congr 1
        ring
  have he : Real.exp (-2*a*x) = ∫ ω, G ω ∂μ := by
    simp only [F, gaussianHalfLine_capped_exp_integral hX hi hG] at hlim
    exact tendsto_nhds_unique tendsto_const_nhds hlim
  rw [he]
  have hA : MeasurableSet {ω | gaussianHalfLineExit X x a ω ≠ ⊤} :=
    ((gaussianHalfLineExit_isStoppingTime hX x a).measurable' (measurableSet_singleton ⊤)).compl
  rw [← integral_indicator hA]
  apply integral_congr_ae
  apply ae_of_all
  intro ω
  by_cases ht : gaussianHalfLineExit X x a ω = ⊤ <;> simp [G, ht]

/-- Eventual ruin from a nonnegative start has its genuine exponential upper bound. -/
theorem gaussianHalfLineExit_probability_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {x a : ℝ} (hx : 0 ≤ x) (ha : 0 < a) :
    μ.real {ω | gaussianHalfLineExit X x a ω ≠ ⊤} ≤ Real.exp (-2*a*x) := by
  have := hi.isProbabilityMeasure
  have hA : MeasurableSet {ω | gaussianHalfLineExit X x a ω ≠ ⊤} :=
    ((gaussianHalfLineExit_isStoppingTime hX x a).measurable' (measurableSet_singleton ⊤)).compl
  rw [gaussianHalfLine_overshoot_identity hX hi hG hx ha]
  calc
    _ = ∫ ω in {ω | gaussianHalfLineExit X x a ω ≠ ⊤}, (1 : ℝ) ∂μ := by simp
    _ ≤ _ := by
      apply setIntegral_mono_on (integrable_const (1 : ℝ)).integrableOn
        (gaussianHalfLineOvershoot_integrable_exp hX hi hG hx ha.le (show 0 ≤ 2*a by positivity)).integrableOn hA
      intro ω _
      exact Real.one_le_exp (mul_nonneg (by positivity) (gaussianHalfLineOvershoot_nonneg X x a ω))

end SwingRepair
