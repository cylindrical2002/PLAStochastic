import PLAStochastic.Swing.Gaussian.StripExit.Walk
import PLAStochastic.ForMathlib.Probability.Process.CappedStopping.Identities
import PLAStochastic.Swing.Gaussian.Tail.QuadraticDrift

/-! # Actual quadratic drift stopped at the Gaussian strip exit -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- Every fixed-time walk position has an actual finite second moment. -/
theorem gaussianDriftWalk_memLp_two [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (x a : ℝ) (n : ℕ) : MemLp (gaussianDriftWalk X x a n) 2 μ := by
  have hs : MemLp (cumulativeSamples X n) 2 μ :=
    memLp_finsetSum (Finset.range n) (fun k _ => (iid_standardGaussian_hasGaussianLaw hX hG k).memLp_two)
  exact ((memLp_const x).add hs).add (memLp_const (a*(n : ℝ)))

theorem gaussianDriftWalk_potential_integrable [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (x a R : ℝ) (n : ℕ) : Integrable (fun ω => stripPotential R (gaussianDriftWalk X x a n ω)) μ := by
  have hs := gaussianDriftWalk_memLp_two hX hG x a n
  have hi := (hs.integrable (by norm_num)).mul_const R
  apply (hi.sub hs.integrable_sq).congr
  exact Eventually.of_forall (fun ω => by dsimp [stripPotential]; ring)

/-- Independence is derived from the original increment history. -/
theorem past_statistic_indep_currentIncrement
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ) (n : ℕ)
    {f : Ω → ℝ} (hf : Measurable[incrementIndexSpace X (Iio n)] f) :
    IndepFun f (X n) μ :=
  (indep_of_indep_of_le_right (currentIncrement_indep_past hX hi n) hf.comap_le).symm

/-- The actual stopped one-step quadratic potential has drift at most minus one half
of the true probability that the walk has not exited. -/
theorem gaussianStrip_potential_step_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (x : ℝ) {a R : ℝ} (ha : 0 ≤ a) (haR : a*R ≤ 1/2) (n : ℕ) :
    (∫ ω, if (n : WithTop ℕ) < gaussianStripExit X x a R ω then
      stripPotential R (gaussianDriftWalk X x a (n+1) ω) -
        stripPotential R (gaussianDriftWalk X x a n ω) else 0 ∂μ) ≤
      -(1/2 : ℝ) * μ.real {ω | (n : WithTop ℕ) < gaussianStripExit X x a R ω} := by
  have : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  let S := gaussianDriftWalk X x a n
  let A := gaussianStripSurvives X x a R n
  have hAp : MeasurableSet[incrementIndexSpace X (Iio n)] A :=
    gaussianStripSurvives_measurable_past X x a R n
  have hAm : MeasurableSet A := (incrementIndexSpace_le hX _ _ hAp)
  have hSp : Measurable[incrementIndexSpace X (Iio n)] S := gaussianDriftWalk_measurable_past X x a n
  have hS : Integrable S μ := (gaussianDriftWalk_memLp_two hX hG x a n).integrable (by norm_num)
  let F₀ := A.indicator (fun ω => a*(R-2*S ω)-a^2)
  let F₁ := A.indicator (fun ω => R-2*S ω-2*a)
  let F₂ := A.indicator (fun _ => (1 : ℝ))
  have h₀ : Integrable F₀ μ := ((((integrable_const R).sub (hS.const_mul 2)).const_mul a).sub (integrable_const _)).indicator hAm
  have h₁ : Integrable F₁ μ := (((integrable_const R).sub (hS.const_mul 2)).sub (integrable_const _)).indicator hAm
  have h₂ : Integrable F₂ μ := (integrable_const _).indicator hAm
  have h₁p : Measurable[incrementIndexSpace X (Iio n)] F₁ := by
    let : MeasurableSpace Ω := incrementIndexSpace X (Iio n)
    exact ((measurable_const.sub (measurable_const.mul hSp)).sub measurable_const).indicator hAp
  have h₂p : Measurable[incrementIndexSpace X (Iio n)] F₂ := by
    let : MeasurableSpace Ω := incrementIndexSpace X (Iio n)
    exact measurable_const.indicator hAp
  have i₁ := past_statistic_indep_currentIncrement hX hi n h₁p
  have i₂ : IndepFun F₂ (fun ω => (X n ω)^2) μ := (past_statistic_indep_currentIncrement hX hi n h₂p).comp
    measurable_id (show Measurable (fun z : ℝ => z^2) by fun_prop)
  have hZ := (iid_standardGaussian_hasGaussianLaw hX hG n).integrable
  have hZ₂ := (iid_standardGaussian_hasGaussianLaw hX hG n).memLp_two.integrable_sq
  have hmul₁ : Integrable (fun ω => F₁ ω * X n ω) μ := i₁.integrable_mul h₁ hZ
  have hmul₂ : Integrable (fun ω => F₂ ω * (X n ω)^2) μ := i₂.integrable_mul h₂ hZ₂
  have iz : (∫ ω, X n ω ∂μ) = 0 := (iid_standardGaussian_mean_variance hX hG n).1
  have iz₂ : (∫ ω, (X n ω)^2 ∂μ) = 1 := by
    have hl : HasLaw (X n) (gaussianReal 0 1) μ := ⟨(hX n).aemeasurable, hG n⟩
    exact (hl.integral_comp (show AEStronglyMeasurable (fun z : ℝ => z^2) (gaussianReal 0 1) by fun_prop)).trans integral_sq_standardGaussian
  have imul₁ : (∫ ω, F₁ ω * X n ω ∂μ) = 0 := by
    rw [i₁.integral_fun_mul_eq_mul_integral h₁.aestronglyMeasurable hZ.aestronglyMeasurable, iz, mul_zero]
  have imul₂ : (∫ ω, F₂ ω * (X n ω)^2 ∂μ) = ∫ ω, F₂ ω ∂μ := by
    rw [i₂.integral_fun_mul_eq_mul_integral h₂.aestronglyMeasurable hZ₂.aestronglyMeasurable, iz₂, mul_one]
  have hrepl (ω : Ω) :
      (if (n : WithTop ℕ) < gaussianStripExit X x a R ω then
      stripPotential R (gaussianDriftWalk X x a (n+1) ω) -
        stripPotential R (gaussianDriftWalk X x a n ω) else 0) =
      F₀ ω + F₁ ω * X n ω - F₂ ω * (X n ω)^2 := by
    by_cases h : ω ∈ A
    · have he := (lt_gaussianStripExit_iff X x a R n ω).mpr h
      simp only [if_pos he, F₀, F₁, F₂, indicator_of_mem h, gaussianDriftWalk_succ]
      dsimp [S, stripPotential]
      ring
    · have he : ¬ (n : WithTop ℕ) < gaussianStripExit X x a R ω := fun hh => h ((lt_gaussianStripExit_iff X x a R n ω).mp hh)
      simp only [if_neg he, F₀, F₁, F₂, indicator_of_notMem h, zero_mul, add_zero, sub_zero]
  have hsum : Integrable (fun ω => F₀ ω + F₁ ω * X n ω) μ := h₀.add hmul₁
  rw [integral_congr_ae (Eventually.of_forall hrepl), integral_sub hsum hmul₂,
    integral_add h₀ hmul₁, imul₁, imul₂, add_zero, ← integral_sub h₀ h₂]
  have hb : (∫ ω, F₀ ω-F₂ ω ∂μ) ≤ ∫ ω, -(1/2 : ℝ)*F₂ ω ∂μ := by
    apply integral_mono (h₀.sub h₂) (h₂.const_mul _)
    intro ω
    by_cases h : ω ∈ A
    · have hu : S ω ∈ Icc 0 R := h n le_rfl
      simp only [Pi.sub_apply, F₀, F₂, indicator_of_mem h]
      nlinarith [mul_nonneg ha hu.1, sq_nonneg a]
    · simp only [Pi.sub_apply, F₀, F₂, indicator_of_notMem h, sub_self, mul_zero, le_refl]
  refine hb.trans_eq ?_
  rw [integral_const_mul, integral_indicator hAm, setIntegral_const]
  simp only [smul_eq_mul, mul_one]
  congr 2
  ext ω
  exact (lt_gaussianStripExit_iff X x a R n ω).symm

/-- The complete bounded-stopping inequality for the actual Gaussian walk. -/
theorem gaussianStrip_capped_potential_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (x : ℝ) {a R : ℝ} (ha : 0 ≤ a) (haR : a*R ≤ 1/2) (m : ℕ) :
    (∫ ω, stripPotential R (gaussianDriftWalk X x a
      (capDiscreteTime (gaussianStripExit X x a R ω) m) ω) ∂μ) ≤
      stripPotential R x - (1/2 : ℝ) * ∫ ω, (capDiscreteTime (gaussianStripExit X x a R ω) m : ℝ) ∂μ := by
  have : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hτ : Measurable[mΩ] (gaussianStripExit X x a R) :=
    (gaussianStripExit_isStoppingTime hX x a R).measurable'
  rw [integral_capDiscreteTime_potential hτ (gaussianDriftWalk_potential_integrable hX hG x a R),
    integral_capDiscreteTime hτ]
  have hs := Finset.sum_le_sum (s := Finset.range m)
    (fun n _ => gaussianStrip_potential_step_le hX hi hG x ha haR n)
  simp only [← Finset.mul_sum, measureReal_def] at hs
  simp only [gaussianDriftWalk_zero, integral_const, measureReal_def, measure_univ,
    ENNReal.toReal_one, smul_eq_mul, one_mul]
  linarith

end SwingRepair
