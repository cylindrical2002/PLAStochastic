import PLAStochastic.Swing.Gaussian.Survival.ExponentialDividedDifference

/-! Small-drift asymptotics of the actual infinite survival probability. -/
noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Set Filter
open scoped ENNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- The probability of never reaching a negative position. -/
def gaussianInfiniteSurvival (X : ℕ → Ω → ℝ) (μ : Measure Ω) (x a : ℝ) : ℝ :=
  μ.real {ω | gaussianHalfLineExit X x a ω = ⊤}

/-- The event definition is exactly the limit of the paper's finite survival probabilities. -/
theorem gaussianSurvivalEvent_tendsto_infinite [IsFiniteMeasure μ]
    (hX : ∀ n, Measurable (X n)) {x a : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun n : ℕ => μ.real (gaussianSurvivalEvent X x a n)) atTop
      (𝓝 (gaussianInfiniteSurvival X μ x a)) := by
  have he : (⋂ n : ℕ, gaussianSurvivalEvent X x a n) =
      {ω | gaussianHalfLineExit X x a ω = ⊤} := by
    ext ω
    rw [mem_iInter]
    change (∀ n, ∀ j ∈ Icc 1 n, 0 ≤ gaussianDriftWalk X x a j ω) ↔ gaussianHalfLineExit X x a ω = ⊤
    rw [show gaussianHalfLineExit X x a ω = hittingAfter (gaussianDriftWalk X x a) (Iio 0) 0 ω from rfl,
      hittingAfter_eq_top_iff]
    constructor
    · intro h j _
      change ¬ gaussianDriftWalk X x a j ω < 0
      by_cases hj : j = 0
      · simpa [hj] using hx
      · exact not_lt_of_ge (h j j ⟨Nat.one_le_iff_ne_zero.mpr hj, le_rfl⟩)
    · intro h n j _
      exact le_of_not_gt (h j (Nat.zero_le j))
  have hm : Antitone (gaussianSurvivalEvent X x a) := by
    intro n m hnm ω hω j hj
    exact hω j ⟨hj.1, hj.2.trans hnm⟩
  have ht := tendsto_measure_iInter_atTop
    (fun n => (gaussianSurvivalEvent_measurable hX x a n).nullMeasurableSet) hm
    ⟨0, measure_ne_top μ _⟩
  rw [he] at ht
  exact (ENNReal.continuousAt_toReal (measure_ne_top μ _)).tendsto.comp ht

/-- The transformed actual overshoots have a common second moment. -/
theorem gaussianExpSlope_overshoot_uniformIntegrable
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {ι : Type*} {x a : ι → ℝ} (hx : ∀ i, 0 ≤ x i)
    (ha : ∀ i, 0 ≤ a i) (ha' : ∀ i, a i ≤ 1/2) :
    UniformIntegrable (fun i ω => gaussianExpSlope (2*a i)
      (gaussianHalfLineOvershoot X (x i) (a i) ω)) 1 μ := by
  have := hi.isProbabilityMeasure
  have hf (i : ι) : Measurable (fun u => gaussianExpSlope (2*a i) u) :=
    (continuous_gaussianExpSlope.comp (continuous_const.prodMk continuous_id)).measurable
  apply uniformIntegrable_of_uniform_second_moment
    (fun i => ((hf i).comp (gaussianHalfLineOvershoot_measurable hX (x i) (a i))).aestronglyMeasurable)
    (gaussianExcessExpMomentBound_pos 4).le
  intro i
  apply gaussianHalfLineOvershoot_lintegral_le hX hi hG (hx i) (ha i)
    (f := fun u => ENNReal.ofReal ((gaussianExpSlope (2*a i) u)^2))
    ((hf i).pow_const 2).ennreal_ofReal (by simp) ENNReal.ofReal_ne_top
  intro r hr
  calc
    _ ≤ ∫⁻ u, ENNReal.ofReal (Real.exp (4*u)) ∂gaussianExcessLaw r := by
      apply lintegral_mono_ae
      filter_upwards [gaussianExcessLaw_positive_ae r] with u hu
      exact ENNReal.ofReal_le_ofReal (gaussianExpSlope_sq_le_exp (mul_nonneg (by norm_num) (ha i)) (by linarith [ha' i]) hu.le)
    _ = ENNReal.ofReal (∫ u, Real.exp (4*u) ∂gaussianExcessLaw r) :=
      (ofReal_integral_eq_lintegral_ofReal (gaussianExcessLaw_integrable_exp r 4)
        (ae_of_all _ (fun _ => (Real.exp_pos _).le))).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (gaussianExcessLaw_exp_moment_le hr (by norm_num))

theorem gaussianExpSlope_overshoot_mean_convergence
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {x a : ℕ → ℝ} {w : ℝ} (hx : ∀ n, 0 ≤ x n)
    (ha : ∀ n, 0 ≤ a n) (ha' : ∀ n, a n ≤ 1/2)
    (hxlim : Tendsto x atTop (𝓝 w)) (halim : Tendsto a atTop (𝓝 0)) (hw : 0 ≤ w) :
    Tendsto (fun n => ∫ ω, gaussianExpSlope (2*a n)
      (gaussianHalfLineOvershoot X (x n) (a n) ω) ∂μ) atTop
      (𝓝 (∫ ω, gaussianHalfLineOvershoot X w 0 ω ∂μ)) := by
  have := hi.isProbabilityMeasure
  have hui := gaussianExpSlope_overshoot_uniformIntegrable hX hi hG hx ha ha'
  have ha2lim : Tendsto (fun n => 2*a n) atTop (𝓝 0) := by simpa using halim.const_mul 2
  have hc : ∀ᵐ ω ∂μ, Tendsto (fun n => gaussianExpSlope (2*a n)
      (gaussianHalfLineOvershoot X (x n) (a n) ω)) atTop
      (𝓝 (gaussianHalfLineOvershoot X w 0 ω)) := by
    filter_upwards [gaussianHalfLine_small_drift_ae hX hi hG hxlim halim (Eventually.of_forall hx) hw] with ω hω
    have ht := (continuous_gaussianExpSlope.tendsto (0, gaussianHalfLineOvershoot X w 0 ω)).comp
      (ha2lim.prodMk_nhds hω.2)
    simpa only [mul_zero, gaussianExpSlope_zero, Function.comp_def] using! ht
  have hg := hui.integrable_of_ae_tendsto hc
  apply tendsto_integral_of_L1' _ hg.aestronglyMeasurable
    (Eventually.of_forall (fun n => (hui.memLp n).integrable le_rfl))
  exact tendsto_Lp_finite_of_tendsto_ae le_rfl (by norm_num) hui.1
    (hui.memLp_of_ae_tendsto hc) hui.2.1 hc

/-- Exact algebraic form of exponential stopping, with the no-hit probability retained. -/
theorem gaussianInfiniteSurvival_div_eq
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {x a : ℝ} (hx : 0 ≤ x) (ha : 0 < a) :
    gaussianInfiniteSurvival X μ x a / (2*a) = -gaussianExpSlope (2*a) (-x) +
      ∫ ω, gaussianExpSlope (2*a) (gaussianHalfLineOvershoot X x a ω) ∂μ := by
  have := hi.isProbabilityMeasure
  let A := {ω | gaussianHalfLineExit X x a ω ≠ ⊤}
  have hA : MeasurableSet A :=
    ((gaussianHalfLineExit_isStoppingTime hX x a).measurable' (measurableSet_singleton ⊤)).compl
  have hE := gaussianHalfLineOvershoot_integrable_exp hX hi hG hx ha.le (show 0 ≤ 2*a by positivity)
  have hAc : (∫ ω in Aᶜ, Real.exp (2*a*gaussianHalfLineOvershoot X x a ω) ∂μ) =
      gaussianInfiniteSurvival X μ x a := by
    calc
      _ = ∫ ω in Aᶜ, (1 : ℝ) ∂μ := by
        apply setIntegral_congr_fun hA.compl
        intro ω hω
        have ht : gaussianHalfLineExit X x a ω = ⊤ := by simpa [A] using hω
        simp [gaussianHalfLineOvershoot, ht]
      _ = _ := by
        simp only [setIntegral_const, smul_eq_mul, mul_one, gaussianInfiniteSurvival]
        congr 1
        ext ω
        simp [A]
  have he : (∫ ω, Real.exp (2*a*gaussianHalfLineOvershoot X x a ω) ∂μ) =
      Real.exp (-2*a*x) + gaussianInfiniteSurvival X μ x a := by
    rw [← integral_add_compl hA hE, hAc]
    congr 1
    exact (gaussianHalfLine_overshoot_identity hX hi hG hx ha).symm
  have h2a : 2*a ≠ 0 := by positivity
  have hGint : Integrable (fun ω => gaussianExpSlope (2*a) (gaussianHalfLineOvershoot X x a ω)) μ := by
    apply ((hE.sub (integrable_const (1 : ℝ))).div_const (2*a)).congr
    exact ae_of_all _ (fun ω => (gaussianExpSlope_eq_div h2a _).symm)
  have hm : (2*a) * ∫ ω, gaussianExpSlope (2*a) (gaussianHalfLineOvershoot X x a ω) ∂μ =
      Real.exp (-2*a*x) + gaussianInfiniteSurvival X μ x a - 1 := by
    rw [← integral_const_mul]
    simp_rw [gaussianExpSlope_mul]
    rw [integral_sub hE (integrable_const _), he]
    simp
  rw [gaussianExpSlope_eq_div h2a]
  have harg : 2*a*(-x) = -2*a*x := by ring
  rw [harg]
  field_simp
  simp only [neg_mul] at hm ⊢
  nlinarith

/-- The actual infinite-survival coefficient along every convergent small positive drift sequence. -/
theorem gaussianInfiniteSurvival_small_drift
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {x a : ℕ → ℝ} {w : ℝ} (hx : ∀ n, 0 ≤ x n)
    (ha : ∀ n, 0 < a n) (ha' : ∀ n, a n ≤ 1/2)
    (hxlim : Tendsto x atTop (𝓝 w)) (halim : Tendsto a atTop (𝓝 0)) (hw : 0 ≤ w) :
    Tendsto (fun n => gaussianInfiniteSurvival X μ (x n) (a n)/(2*a n)) atTop
      (𝓝 (gaussianRenewalPotential X μ w)) := by
  have he := gaussianExpSlope_overshoot_mean_convergence hX hi hG hx (fun n => (ha n).le) ha' hxlim halim hw
  have ha2lim : Tendsto (fun n => 2*a n) atTop (𝓝 0) := by simpa using halim.const_mul 2
  have hs : Tendsto (fun n => -gaussianExpSlope (2*a n) (-x n)) atTop (𝓝 w) := by
    have ht := ((continuous_gaussianExpSlope.tendsto (0, -w)).comp
      (ha2lim.prodMk_nhds hxlim.neg)).neg
    simpa only [mul_zero, gaussianExpSlope_zero, neg_neg, Function.comp_def] using! ht
  have ht := hs.add he
  simpa only [gaussianRenewalPotential, ← gaussianInfiniteSurvival_div_eq hX hi hG (hx _) (ha _)] using! ht

end SwingRepair
