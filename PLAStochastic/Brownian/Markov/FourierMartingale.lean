import PLAStochastic.Brownian.Markov.ExponentialFamily

/-! Fourier martingales derived from the actual Gaussian increment law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

def gaussianPhase (c x : ℝ) : ℂ := Complex.exp (((c * x : ℝ) : ℂ) * Complex.I)

theorem continuous_gaussianPhase (c : ℝ) : Continuous (gaussianPhase c) := by
  unfold gaussianPhase
  fun_prop

theorem norm_gaussianPhase (c x : ℝ) : ‖gaussianPhase c x‖ = 1 := by
  simp [gaussianPhase, Complex.norm_exp]

theorem gaussianPhase_add (c x y : ℝ) :
    gaussianPhase c (x + y) = gaussianPhase c x * gaussianPhase c y := by
  simp only [gaussianPhase, mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]

theorem integrable_gaussianPhase [IsFiniteMeasure μ] (c : ℝ) {X : Ω → ℝ}
    (hX : AEMeasurable X μ) : Integrable (fun ω => gaussianPhase c (X ω)) μ := by
  exact Integrable.of_bound ((continuous_gaussianPhase c).measurable.comp_aemeasurable hX).aestronglyMeasurable
    1 (Eventually.of_forall fun ω => (norm_gaussianPhase c (X ω)).le)

theorem integral_gaussianPhase (c : ℝ) {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) μ) :
    (∫ ω, gaussianPhase c (X ω) ∂μ) = (Real.exp (-((v : ℝ) * c ^ 2 / 2)) : ℂ) := by
  change (∫ ω, (gaussianPhase c ∘ X) ω ∂μ) = _
  rw [hX.integral_comp (continuous_gaussianPhase c).aestronglyMeasurable]
  have heq : (fun x : ℝ => gaussianPhase c x) =
      (fun x : ℝ => Complex.exp ((c : ℂ) * x * Complex.I)) := by
    funext x
    simp [gaussianPhase]
  rw [heq, ← charFun_apply_real, charFun_gaussianReal]
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_sub, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

def brownianFourier (hB : IsPreBrownianReal B μ) (c : ℝ) (t : ℝ≥0) (ω : Ω) : ℂ :=
  (Real.exp (c ^ 2 * (t : ℝ) / 2) : ℂ) * gaussianPhase c (measurableBrownian hB t ω)

theorem integrable_brownianFourier (hB : IsPreBrownianReal B μ) (c : ℝ) (t : ℝ≥0) :
    Integrable (brownianFourier hB c t) μ := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  exact (integrable_gaussianPhase c (measurable_measurableBrownian hB t).aemeasurable).const_mul _

theorem integral_brownianFourier (hB : IsPreBrownianReal B μ) (c : ℝ) (t : ℝ≥0) :
    (∫ ω, brownianFourier hB c t ω ∂μ) = 1 := by
  unfold brownianFourier
  rw [integral_const_mul, integral_gaussianPhase c ((isPreBrownianReal_measurableBrownian hB).hasLaw_eval t),
    ← Complex.ofReal_mul, ← Real.exp_add]
  have he : c ^ 2 * (t : ℝ) / 2 + -((t : ℝ) * c ^ 2 / 2) = 0 := by ring
  rw [he]
  simp

theorem stronglyAdapted_brownianFourier (hB : IsPreBrownianReal B μ) (c : ℝ) :
    StronglyAdapted (brownianNaturalFiltration hB) (brownianFourier hB c) := by
  intro t
  have h := Filtration.stronglyAdapted_natural
    (fun t => (measurable_measurableBrownian hB t).stronglyMeasurable) t
  exact ((continuous_gaussianPhase c).comp_stronglyMeasurable h).const_mul _

def brownianFourierIncrement (hB : IsPreBrownianReal B μ) (c : ℝ) (s t : ℝ≥0) (ω : Ω) : ℂ :=
  (Real.exp (c ^ 2 * ((t - s : ℝ≥0) : ℝ) / 2) : ℂ) *
    gaussianPhase c (measurableBrownian hB t ω - measurableBrownian hB s ω)

theorem measurable_brownianFourierIncrement (hB : IsPreBrownianReal B μ) (c : ℝ) (s t : ℝ≥0) :
    Measurable (brownianFourierIncrement hB c s t) :=
  ((continuous_gaussianPhase c).measurable.comp
    ((measurable_measurableBrownian hB t).sub (measurable_measurableBrownian hB s))).const_mul _

theorem integrable_brownianFourierIncrement (hB : IsPreBrownianReal B μ) (c : ℝ) (s t : ℝ≥0) :
    Integrable (brownianFourierIncrement hB c s t) μ := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  exact (integrable_gaussianPhase c
    (((measurable_measurableBrownian hB t).sub (measurable_measurableBrownian hB s)).aemeasurable)).const_mul _

theorem integral_brownianFourierIncrement (hB : IsPreBrownianReal B μ) (c : ℝ)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ ω, brownianFourierIncrement hB c s t ω ∂μ) = 1 := by
  unfold brownianFourierIncrement
  rw [integral_const_mul, integral_gaussianPhase c (brownianIncrement_hasLaw hB hst),
    ← Complex.ofReal_mul, ← Real.exp_add]
  have he : c ^ 2 * ((t - s : ℝ≥0) : ℝ) / 2 +
      -(((t - s : ℝ≥0) : ℝ) * c ^ 2 / 2) = 0 := by ring
  rw [he]
  simp

theorem brownianFourier_factor (hB : IsPreBrownianReal B μ) (c : ℝ)
    {s t : ℝ≥0} (hst : s ≤ t) :
    brownianFourier hB c t = brownianFourier hB c s * brownianFourierIncrement hB c s t := by
  funext ω
  simp only [brownianFourier, brownianFourierIncrement, Pi.mul_apply]
  rw [mul_mul_mul_comm, ← gaussianPhase_add, add_sub_cancel,
    ← Complex.ofReal_mul, ← Real.exp_add, NNReal.coe_sub hst]
  congr 2
  ring

theorem indep_brownianFourierIncrement (hB : IsPreBrownianReal B μ) (c : ℝ)
    {s t : ℝ≥0} (hst : s ≤ t) :
    Indep (MeasurableSpace.comap (brownianFourierIncrement hB c s t) inferInstance)
      (brownianNaturalFiltration hB s) μ := by
  have hi := (isPreBrownianReal_measurableBrownian hB).indepFun_shift s
  have hc := hi.comp
    (((continuous_gaussianPhase c).measurable.comp (measurable_pi_apply (t - s))).const_mul
      (Real.exp (c ^ 2 * ((t - s : ℝ≥0) : ℝ) / 2) : ℂ)) measurable_id
  rw [brownianNaturalFiltration, Filtration.natural_eq_comap]
  change IndepFun (brownianFourierIncrement hB c s t)
    (fun ω (u : Set.Iic s) => measurableBrownian hB u.1 ω) μ
  simpa only [Function.comp_def, id_eq, add_tsub_cancel_of_le hst,
    brownianFourierIncrement] using! hc

/-- The Fourier martingale is proved from Gaussian independent increments. -/
theorem martingale_brownianFourier (hB : IsPreBrownianReal B μ) (c : ℝ) :
    Martingale (brownianFourier hB c) (brownianNaturalFiltration hB) μ := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  refine ⟨stronglyAdapted_brownianFourier hB c, fun s t hst => ?_⟩
  have hi := condExp_indep_eq
    (measurable_brownianFourierIncrement hB c s t).comap_le
    ((brownianNaturalFiltration hB).le s)
    (comap_measurable (brownianFourierIncrement hB c s t)).stronglyMeasurable
    (indep_brownianFourierIncrement hB c hst)
  have hp := condExp_bilin_of_stronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℂ)
    (stronglyAdapted_brownianFourier hB c s)
    (by
      change Integrable (brownianFourier hB c s * brownianFourierIncrement hB c s t) μ
      rw [← brownianFourier_factor hB c hst]
      exact integrable_brownianFourier hB c t)
    (integrable_brownianFourierIncrement hB c s t)
  change μ[brownianFourier hB c s * brownianFourierIncrement hB c s t |
    brownianNaturalFiltration hB s] =ᵐ[μ]
      brownianFourier hB c s * μ[brownianFourierIncrement hB c s t | brownianNaturalFiltration hB s] at hp
  rw [brownianFourier_factor hB c hst]
  filter_upwards [hp, hi] with ω hpω hiω
  rw [hpω, Pi.mul_apply, hiω, integral_brownianFourierIncrement hB c hst, mul_one]

/-- Countable bounded stopping times preserve the Fourier expectation. -/
theorem brownianFourier_stopped_eq_condExp (hB : IsPreBrownianReal B μ) (c : ℝ)
    {τ : Ω → WithTop ℝ≥0} {T : ℝ≥0}
    (hτ : IsStoppingTime (brownianNaturalFiltration hB) τ)
    (hbound : ∀ ω, τ ω ≤ T) (hcount : (Set.range τ).Countable) :
    stoppedValue (brownianFourier hB c) τ =ᵐ[μ]
      μ[brownianFourier hB c T | hτ.measurableSpace] := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  exact (martingale_brownianFourier hB c).stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
    hτ hbound hcount

theorem integral_brownianFourier_stopped (hB : IsPreBrownianReal B μ) (c : ℝ)
    {τ : Ω → WithTop ℝ≥0} {T : ℝ≥0}
    (hτ : IsStoppingTime (brownianNaturalFiltration hB) τ)
    (hbound : ∀ ω, τ ω ≤ T) (hcount : (Set.range τ).Countable) :
    (∫ ω, stoppedValue (brownianFourier hB c) τ ω ∂μ) = 1 := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  rw [integral_congr_ae (brownianFourier_stopped_eq_condExp hB c hτ hbound hcount),
    integral_condExp hτ.measurableSpace_le, integral_brownianFourier hB c T]

def actualBrownianFourier (B : ℝ≥0 → Ω → ℝ) (c : ℝ) (t : ℝ≥0) (ω : Ω) : ℂ :=
  (Real.exp (c ^ 2 * (t : ℝ) / 2) : ℂ) * gaussianPhase c (B t ω)

theorem norm_brownianFourier (hB : IsPreBrownianReal B μ) (c : ℝ) (t : ℝ≥0) (ω : Ω) :
    ‖brownianFourier hB c t ω‖ = Real.exp (c ^ 2 * (t : ℝ) / 2) := by
  simp only [brownianFourier, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), norm_gaussianPhase, mul_one]

theorem brownianFourier_stopped_ae_eq_actual (hB : IsPreBrownianReal B μ) (c : ℝ)
    {τ : Ω → WithTop ℝ≥0} (hcount : (Set.range τ).Countable) :
    stoppedValue (brownianFourier hB c) τ =ᵐ[μ]
      stoppedValue (actualBrownianFourier B c) τ := by
  let S : Set ℝ≥0 := Set.range (fun ω => (τ ω).untopA)
  have hS : S.Countable := by
    simpa only [S, ← Set.range_comp, Function.comp_def] using hcount.image WithTop.untopA
  have : Countable S := hS.to_subtype
  filter_upwards [measurableBrownian_countable_ae_eq hB (fun q : S => q.1)] with ω hω
  exact congrArg (fun x : ℝ => (Real.exp (c ^ 2 * ((τ ω).untopA : ℝ) / 2) : ℂ) * gaussianPhase c x)
    (hω ⟨(τ ω).untopA, ⟨ω, rfl⟩⟩)

/-- Actual continuous stopping limits are justified by a deterministic norm bound. -/
theorem integral_actualBrownianFourier_stopping_limit (hB : IsBrownianReal B μ) (c : ℝ)
    {τ : ℕ → Ω → WithTop ℝ≥0} {ρ : Ω → ℝ≥0} {T : ℝ≥0}
    (hτ : ∀ n, IsStoppingTime (brownianNaturalFiltration hB.toIsPreBrownianReal) (τ n))
    (hbound : ∀ n ω, τ n ω ≤ T) (hcount : ∀ n, (Set.range (τ n)).Countable)
    (hconv : ∀ᵐ ω ∂μ, Tendsto (fun n => (τ n ω).untopA) atTop (𝓝 (ρ ω))) :
    Integrable (fun ω => actualBrownianFourier B c (ρ ω) ω) μ ∧
      (∫ ω, actualBrownianFourier B c (ρ ω) ω ∂μ) = 1 := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  let F : ℕ → Ω → ℂ := fun n => stoppedValue (brownianFourier hB.toIsPreBrownianReal c) (τ n)
  have hmeas (n : ℕ) : AEStronglyMeasurable (F n) μ :=
    integrable_condExp.aestronglyMeasurable.congr
      (brownianFourier_stopped_eq_condExp hB.toIsPreBrownianReal c (hτ n) (hbound n) (hcount n)).symm
  have hbd (n : ℕ) : ∀ᵐ ω ∂μ, ‖F n ω‖ ≤ Real.exp (c ^ 2 * (T : ℝ) / 2) := by
    apply Eventually.of_forall
    intro ω
    change ‖brownianFourier hB.toIsPreBrownianReal c (τ n ω).untopA ω‖ ≤ _
    rw [norm_brownianFourier]
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (show ((τ n ω).untopA : ℝ) ≤ T by exact_mod_cast WithTop.untopA_le (hbound n ω))
      (sq_nonneg c)) (by norm_num)
  have hae : ∀ᵐ ω ∂μ, ∀ n, F n ω = stoppedValue (actualBrownianFourier B c) (τ n) ω :=
    ae_all_iff.mpr (fun n => brownianFourier_stopped_ae_eq_actual hB.toIsPreBrownianReal c (hcount n))
  have hfg : ∀ᵐ ω ∂μ, Tendsto (fun n => F n ω) atTop (𝓝 (actualBrownianFourier B c (ρ ω) ω)) := by
    filter_upwards [hB.cont, hconv, hae] with ω hω hρ heq
    have hc : Continuous (fun t : ℝ≥0 => actualBrownianFourier B c t ω) := by
      unfold actualBrownianFourier
      exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
        ((continuous_subtype_val.const_mul (c ^ 2)).div_const 2))).mul
          ((continuous_gaussianPhase c).comp hω)
    exact ((hc.tendsto (ρ ω)).comp hρ).congr (fun n => (heq n).symm)
  have hgmeas := aestronglyMeasurable_of_tendsto_ae atTop hmeas hfg
  have hgbd : ∀ᵐ ω ∂μ, ‖actualBrownianFourier B c (ρ ω) ω‖ ≤ Real.exp (c ^ 2 * (T : ℝ) / 2) := by
    filter_upwards [hfg, ae_all_iff.mpr hbd] with ω hω hbω
    exact le_of_tendsto hω.norm (Eventually.of_forall hbω)
  refine ⟨Integrable.of_bound hgmeas _ hgbd, ?_⟩
  have hint := tendsto_integral_of_dominated_convergence
    (fun _ : Ω => Real.exp (c ^ 2 * (T : ℝ) / 2)) hmeas (integrable_const _) hbd hfg
  have hc : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop
      (𝓝 (∫ ω, actualBrownianFourier B c (ρ ω) ω ∂μ)) := by
    convert hint using 1
    funext n
    exact (integral_brownianFourier_stopped hB.toIsPreBrownianReal c (hτ n) (hbound n) (hcount n)).symm
  exact tendsto_nhds_unique hc tendsto_const_nhds

end BrownianAffine
