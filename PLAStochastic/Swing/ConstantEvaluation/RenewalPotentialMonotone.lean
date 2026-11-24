import PLAStochastic.Swing.Gaussian.ZeroLadder.StoppedMoments
import PLAStochastic.Swing.Gaussian.HalfLine.PrefixStability
import PLAStochastic.Swing.Gaussian.Stopping.CappedExitPosition
import PLAStochastic.Swing.StationaryLimit.LeadingCoefficient.ConcreteBounds

/-! # Monotonicity of the renewal potential `V`

`V(x) = x + 𝔼 O_x` where `O_x` is the overshoot below `0` of the zero-drift walk
started at `x ≥ 0`.  Optional stopping at the capped exit time gives

  `∫_{survives n} (x + W_n) = x + ∫_{exit ≤ n} O_x → V(x)`,

and the left side is pointwise monotone in `x` (a walk started higher survives
longer and sits higher).  Hence `V` is monotone on `[0, ∞)` and the margin
reward `v(r) = 4V(r)𝟙_{r>0}` is monotone on the line: the paper's "`4V(r)𝟙_{r>0}`
is increasing".
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology Classical
namespace SwingRepair
open LeadingCoefficient

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-- One step of the stopped zero-drift walk started at `x` has mean zero. -/
theorem gaussianHalfLine_step_first (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (x : ℝ) (n : ℕ) :
    (∫ ω, if (n : WithTop ℕ) < gaussianHalfLineExit X x 0 ω then
      gaussianDriftWalk X x 0 (n + 1) ω - gaussianDriftWalk X x 0 n ω else 0 ∂μ) = 0 := by
  have := hi.isProbabilityMeasure
  let A := gaussianHalfLineSurvives X x 0 n
  let F := A.indicator (fun _ => (1 : ℝ))
  have hAp := gaussianHalfLineSurvives_measurable_past X x 0 n
  have hA : MeasurableSet A := incrementIndexSpace_le hX _ _ hAp
  have hFp : Measurable[incrementIndexSpace X (Iio n)] F := by
    let : MeasurableSpace Ω := incrementIndexSpace X (Iio n)
    exact measurable_const.indicator hAp
  have hF : Integrable F μ := (integrable_const _).indicator hA
  have hZ := (iid_standardGaussian_hasGaussianLaw hX hG n).integrable
  have hind := past_statistic_indep_currentIncrement hX hi n hFp
  have he (ω : Ω) :
      (if (n : WithTop ℕ) < gaussianHalfLineExit X x 0 ω then
        gaussianDriftWalk X x 0 (n + 1) ω - gaussianDriftWalk X x 0 n ω else 0) = F ω * X n ω := by
    by_cases h : ω ∈ A
    · simp only [if_pos ((lt_gaussianHalfLineExit_iff X x 0 n ω).mpr h),
        F, indicator_of_mem h, one_mul, gaussianDriftWalk, cumulativeSamples_succ]
      ring
    · simp only [if_neg (fun hh => h ((lt_gaussianHalfLineExit_iff X x 0 n ω).mp hh)),
        F, indicator_of_notMem h, zero_mul]
  rw [integral_congr_ae (ae_of_all _ he),
    hind.integral_fun_mul_eq_mul_integral hF.aestronglyMeasurable hZ.aestronglyMeasurable,
    (iid_standardGaussian_mean_variance hX hG n).1, mul_zero]

/-- Optional stopping: the capped stopped position has mean `x`. -/
theorem gaussianHalfLine_capped_first (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (x : ℝ) (n : ℕ) :
    (∫ ω, gaussianDriftWalk X x 0 (capDiscreteTime (gaussianHalfLineExit X x 0 ω) n) ω ∂μ) = x := by
  have := hi.isProbabilityMeasure
  rw [integral_capDiscreteTime_potential (gaussianHalfLineExit_isStoppingTime hX x 0).measurable'
    (fun k => (gaussianDriftWalk_memLp_two hX hG x 0 k).integrable (by norm_num))]
  simp only [gaussianHalfLine_step_first hX hi hG, Finset.sum_const_zero, add_zero]
  simp [gaussianDriftWalk]

omit [MeasurableSpace Ω] in
/-- The capped stopped position: the walk on survival, minus the overshoot otherwise. -/
theorem gaussianHalfLine_capped_eq (x : ℝ) (n : ℕ) (ω : Ω) :
    gaussianDriftWalk X x 0 (capDiscreteTime (gaussianHalfLineExit X x 0 ω) n) ω =
      if ω ∈ gaussianHalfLineSurvives X x 0 n then gaussianDriftWalk X x 0 n ω
      else -gaussianHalfLineOvershoot X x 0 ω := by
  by_cases h : ω ∈ gaussianHalfLineSurvives X x 0 n
  · rw [if_pos h, capDiscreteTime_eq_of_lt ((lt_gaussianHalfLineExit_iff X x 0 n ω).mpr h)]
  · have hle : gaussianHalfLineExit X x 0 ω ≤ n :=
      le_of_not_gt (fun hh => h ((lt_gaussianHalfLineExit_iff X x 0 n ω).mp hh))
    have ht := ne_top_of_le_ne_top WithTop.coe_ne_top hle
    rw [if_neg h, capDiscreteTime_eq_of_le hle, gaussianHalfLineOvershoot, if_neg ht, neg_neg]
    rfl

theorem gaussianHalfLineSurvives_measurableSet (hX : ∀ n, Measurable (X n)) (x : ℝ) (n : ℕ) :
    MeasurableSet (gaussianHalfLineSurvives X x 0 n) :=
  incrementIndexSpace_le hX _ _ (gaussianHalfLineSurvives_measurable_past X x 0 n)

theorem gaussianHalfLineOvershoot_zero_drift_integrable (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {x : ℝ} (hx : 0 ≤ x) :
    Integrable (gaussianHalfLineOvershoot X x 0) μ :=
  (gaussianHalfLineOvershoot_mean_convergence hX hi hG (x := fun _ : ℕ => x)
    (a := fun _ : ℕ => (0 : ℝ)) (w := x) (fun _ => hx) (fun _ => le_rfl) tendsto_const_nhds
    tendsto_const_nhds hx).1

/-- **Capped renewal identity**: `∫_{survives n} (x + W_n) = x + ∫_{exit ≤ n} O_x`. -/
theorem setIntegral_survives_eq (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    (∫ ω in gaussianHalfLineSurvives X x 0 n, gaussianDriftWalk X x 0 n ω ∂μ) =
      x + ∫ ω in (gaussianHalfLineSurvives X x 0 n)ᶜ, gaussianHalfLineOvershoot X x 0 ω ∂μ := by
  have := hi.isProbabilityMeasure
  have hA := gaussianHalfLineSurvives_measurableSet hX x n
  have hS : Integrable (gaussianDriftWalk X x 0 n) μ :=
    (gaussianDriftWalk_memLp_two hX hG x 0 n).integrable (by norm_num)
  have hO := gaussianHalfLineOvershoot_zero_drift_integrable hX hi hG hx
  have h := gaussianHalfLine_capped_first hX hi hG x n
  have he : (fun ω => gaussianDriftWalk X x 0 (capDiscreteTime (gaussianHalfLineExit X x 0 ω) n) ω) =
      fun ω => (gaussianHalfLineSurvives X x 0 n).indicator (gaussianDriftWalk X x 0 n) ω -
        (gaussianHalfLineSurvives X x 0 n)ᶜ.indicator (gaussianHalfLineOvershoot X x 0) ω := by
    funext ω
    rw [gaussianHalfLine_capped_eq]
    by_cases hω : ω ∈ gaussianHalfLineSurvives X x 0 n
    · rw [if_pos hω, indicator_of_mem hω, indicator_of_notMem (by simpa using hω), sub_zero]
    · rw [if_neg hω, indicator_of_notMem hω, indicator_of_mem (by simpa using hω), zero_sub]
  rw [he, integral_sub (hS.indicator hA) (hO.indicator hA.compl), integral_indicator hA,
    integral_indicator hA.compl] at h
  linarith

/-- `∫_{survives n} (x + W_n) → V(x)`. -/
theorem setIntegral_survives_tendsto (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun n => ∫ ω in gaussianHalfLineSurvives X x 0 n, gaussianDriftWalk X x 0 n ω ∂μ)
      atTop (𝓝 (gaussianRenewalPotential X μ x)) := by
  have := hi.isProbabilityMeasure
  have hO := gaussianHalfLineOvershoot_zero_drift_integrable hX hi hG hx
  simp_rw [setIntegral_survives_eq hX hi hG hx]
  unfold gaussianRenewalPotential
  refine tendsto_const_nhds.add ?_
  have hmono : Monotone fun n => (gaussianHalfLineSurvives X x 0 n)ᶜ := by
    intro m n hmn
    refine compl_subset_compl.mpr fun ω hω j hj => hω j (hj.trans hmn)
  have hmeas : ∀ n, MeasurableSet (gaussianHalfLineSurvives X x 0 n)ᶜ := fun n =>
    (gaussianHalfLineSurvives_measurableSet hX x n).compl
  have hunion : (⋃ n, (gaussianHalfLineSurvives X x 0 n)ᶜ) = {ω | gaussianHalfLineExit X x 0 ω ≠ ⊤} := by
    ext ω
    simp only [mem_iUnion, mem_compl_iff, mem_ofPred_eq, ne_eq]
    constructor
    · rintro ⟨n, hn⟩ htop
      exact hn ((lt_gaussianHalfLineExit_iff X x 0 n ω).mp (by rw [htop]; exact WithTop.coe_lt_top n))
    · intro htop
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp htop
      refine ⟨n, fun hs => ?_⟩
      have := (lt_gaussianHalfLineExit_iff X x 0 n ω).mpr hs
      rw [← hn] at this
      exact lt_irrefl _ this
  have hfull : ∫ ω in ⋃ n, (gaussianHalfLineSurvives X x 0 n)ᶜ, gaussianHalfLineOvershoot X x 0 ω ∂μ =
      ∫ ω, gaussianHalfLineOvershoot X x 0 ω ∂μ := by
    rw [hunion]
    refine setIntegral_eq_integral_of_ae_compl_eq_zero ?_
    filter_upwards [gaussianHalfLineExit_zero_finite_ae hX hi hG hx] with ω hω hnot
    exact absurd hω hnot
  rw [← hfull]
  exact tendsto_setIntegral_of_monotone hmeas hmono hO.integrableOn

omit [MeasurableSpace Ω] in
/-- Pointwise monotonicity of the survival indicator times the position. -/
theorem survives_indicator_mono {x x' : ℝ} (hxx' : x ≤ x') (n : ℕ) (ω : Ω) :
    (gaussianHalfLineSurvives X x 0 n).indicator (gaussianDriftWalk X x 0 n) ω ≤
      (gaussianHalfLineSurvives X x' 0 n).indicator (gaussianDriftWalk X x' 0 n) ω := by
  have hsub : gaussianHalfLineSurvives X x 0 n ⊆ gaussianHalfLineSurvives X x' 0 n := by
    intro ω hω j hj
    have := hω j hj
    simp only [gaussianDriftWalk] at this ⊢
    linarith
  by_cases hω : ω ∈ gaussianHalfLineSurvives X x 0 n
  · rw [indicator_of_mem hω, indicator_of_mem (hsub hω)]
    simp only [gaussianDriftWalk]
    linarith
  · rw [indicator_of_notMem hω]
    by_cases hω' : ω ∈ gaussianHalfLineSurvives X x' 0 n
    · rw [indicator_of_mem hω']
      exact hω' n le_rfl
    · rw [indicator_of_notMem hω']

/-- **`V` is monotone on `[0, ∞)`.** -/
theorem gaussianRenewalPotential_monotoneOn (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    MonotoneOn (gaussianRenewalPotential X μ) (Ici 0) := by
  have := hi.isProbabilityMeasure
  intro x hx x' hx' hxx'
  have hx0 : 0 ≤ x := mem_Ici.mp hx
  refine le_of_tendsto_of_tendsto' (setIntegral_survives_tendsto hX hi hG hx0)
    (setIntegral_survives_tendsto hX hi hG (mem_Ici.mp hx')) fun n => ?_
  rw [← integral_indicator (gaussianHalfLineSurvives_measurableSet hX x n),
    ← integral_indicator (gaussianHalfLineSurvives_measurableSet hX x' n)]
  refine integral_mono ?_ ?_ (survives_indicator_mono hxx' n)
  · exact ((gaussianDriftWalk_memLp_two hX hG x 0 n).integrable (by norm_num)).indicator
      (gaussianHalfLineSurvives_measurableSet hX x n)
  · exact ((gaussianDriftWalk_memLp_two hX hG x' 0 n).integrable (by norm_num)).indicator
      (gaussianHalfLineSurvives_measurableSet hX x' n)

/-- **The margin reward `v(r) = 4V(r)𝟙_{r>0}` is monotone.** -/
theorem marginLeadingReward_monotone (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    Monotone (marginLeadingReward X μ) := by
  intro r r' hrr'
  by_cases hr : 0 < r
  · have hr' : 0 < r' := hr.trans_le hrr'
    unfold marginLeadingReward
    rw [if_pos hr, if_pos hr']
    have := gaussianRenewalPotential_monotoneOn hX hi hG (mem_Ici.mpr hr.le) (mem_Ici.mpr hr'.le)
      hrr'
    linarith
  · have h0 : marginLeadingReward X μ r = 0 := by
      unfold marginLeadingReward; rw [if_neg hr]
    rw [h0]
    exact marginLeadingReward_nonneg hX hi hG

end SwingRepair
