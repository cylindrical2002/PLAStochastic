import PLAStochastic.Brownian.Markov.ExponentialMartingale

/-!
# Brownian exponential martingales with arbitrary real parameter

The Gaussian moment generating function proves the martingale and all bounded
continuous stopping limits for exp(c B_t - c^2 t / 2).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace BrownianAffine

set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

def brownianExponentialWith (hB : IsPreBrownianReal B μ) (c : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (c * measurableBrownian hB t ω - (c ^ 2 / 2) * (t : ℝ))

theorem gaussian_exponentialWith_integrable (c : ℝ) {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) μ) (hm : Measurable X) :
    Integrable (fun ω => Real.exp (c * X ω - (c ^ 2 / 2) * (v : ℝ))) μ := by
  have h := (hX.measurePreserving hm).integrable_comp_of_integrable
    (integrable_exp_mul_gaussianReal (μ := 0) (v := v) c)
  convert h.mul_const (Real.exp (-(c ^ 2 / 2) * (v : ℝ))) using 1
  funext ω
  dsimp only [Function.comp_def]
  rw [← Real.exp_add]
  congr 1
  ring

theorem gaussian_exponentialWith_integral (c : ℝ) {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) μ) :
    (∫ ω, Real.exp (c * X ω - (c ^ 2 / 2) * (v : ℝ)) ∂μ) = 1 := by
  have heq : (fun ω => Real.exp (c * X ω - (c ^ 2 / 2) * (v : ℝ))) =
      (fun ω => Real.exp (c * X ω) * Real.exp (-(c ^ 2 / 2) * (v : ℝ))) := by
    funext ω
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq, integral_mul_const]
  change mgf X μ c * Real.exp (-(c ^ 2 / 2) * (v : ℝ)) = 1
  rw [mgf_gaussianReal hX.map_eq, ← Real.exp_add]
  convert Real.exp_zero using 1
  congr 1
  ring

theorem integrable_brownianExponentialWith (hB : IsPreBrownianReal B μ) (c : ℝ) (t : ℝ≥0) :
    Integrable (brownianExponentialWith hB c t) μ :=
  gaussian_exponentialWith_integrable c ((isPreBrownianReal_measurableBrownian hB).hasLaw_eval t)
    (measurable_measurableBrownian hB t)

theorem integral_brownianExponentialWith (hB : IsPreBrownianReal B μ) (c : ℝ) (t : ℝ≥0) :
    (∫ ω, brownianExponentialWith hB c t ω ∂μ) = 1 :=
  gaussian_exponentialWith_integral c ((isPreBrownianReal_measurableBrownian hB).hasLaw_eval t)

theorem stronglyAdapted_brownianExponentialWith (hB : IsPreBrownianReal B μ) (c : ℝ) :
    StronglyAdapted (brownianNaturalFiltration hB) (brownianExponentialWith hB c) := by
  intro t
  have h := Filtration.stronglyAdapted_natural
    (fun t => (measurable_measurableBrownian hB t).stronglyMeasurable) t
  exact Real.continuous_exp.comp_stronglyMeasurable ((h.const_mul c).sub stronglyMeasurable_const)

def brownianExponentialWithIncrement (hB : IsPreBrownianReal B μ) (c : ℝ) (s t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (c * (measurableBrownian hB t ω - measurableBrownian hB s ω) -
    (c ^ 2 / 2) * ((t - s : ℝ≥0) : ℝ))

theorem measurable_brownianExponentialWithIncrement (hB : IsPreBrownianReal B μ) (c : ℝ) (s t : ℝ≥0) :
    Measurable (brownianExponentialWithIncrement hB c s t) :=
  Real.measurable_exp.comp
    (((measurable_measurableBrownian hB t).sub (measurable_measurableBrownian hB s)).const_mul c
      |>.sub_const ((c ^ 2 / 2) * ((t - s : ℝ≥0) : ℝ)))

theorem integrable_brownianExponentialWithIncrement (hB : IsPreBrownianReal B μ) (c : ℝ)
    {s t : ℝ≥0} (hst : s ≤ t) : Integrable (brownianExponentialWithIncrement hB c s t) μ :=
  gaussian_exponentialWith_integrable c (brownianIncrement_hasLaw hB hst)
    ((measurable_measurableBrownian hB t).sub (measurable_measurableBrownian hB s))

theorem integral_brownianExponentialWithIncrement (hB : IsPreBrownianReal B μ) (c : ℝ)
    {s t : ℝ≥0} (hst : s ≤ t) : (∫ ω, brownianExponentialWithIncrement hB c s t ω ∂μ) = 1 :=
  gaussian_exponentialWith_integral c (brownianIncrement_hasLaw hB hst)

theorem brownianExponentialWith_factor (hB : IsPreBrownianReal B μ) (c : ℝ)
    {s t : ℝ≥0} (hst : s ≤ t) :
    brownianExponentialWith hB c t = brownianExponentialWith hB c s * brownianExponentialWithIncrement hB c s t := by
  funext ω
  change Real.exp _ = Real.exp _ * Real.exp _
  rw [← Real.exp_add]
  congr 1
  rw [NNReal.coe_sub hst]
  ring

theorem indep_brownianExponentialWithIncrement (hB : IsPreBrownianReal B μ) (c : ℝ)
    {s t : ℝ≥0} (hst : s ≤ t) :
    Indep (MeasurableSpace.comap (brownianExponentialWithIncrement hB c s t) inferInstance)
      (brownianNaturalFiltration hB s) μ := by
  have hi := (isPreBrownianReal_measurableBrownian hB).indepFun_shift s
  have hc := hi.comp
    (Real.measurable_exp.comp
      (((measurable_pi_apply (t - s)).const_mul c).sub_const ((c ^ 2 / 2) * ((t - s : ℝ≥0) : ℝ))))
    measurable_id
  rw [brownianNaturalFiltration, Filtration.natural_eq_comap]
  change IndepFun (brownianExponentialWithIncrement hB c s t)
    (fun ω (u : Set.Iic s) => measurableBrownian hB u.1 ω) μ
  simpa only [Function.comp_def, id_eq, add_tsub_cancel_of_le hst,
    brownianExponentialWithIncrement] using! hc

theorem martingale_brownianExponentialWith (hB : IsPreBrownianReal B μ) (c : ℝ) :
    Martingale (brownianExponentialWith hB c) (brownianNaturalFiltration hB) μ := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  refine ⟨stronglyAdapted_brownianExponentialWith hB c, fun s t hst => ?_⟩
  have hi := condExp_indep_eq
    (measurable_brownianExponentialWithIncrement hB c s t).comap_le
    ((brownianNaturalFiltration hB).le s)
    (comap_measurable (brownianExponentialWithIncrement hB c s t)).stronglyMeasurable
    (indep_brownianExponentialWithIncrement hB c hst)
  have hp := condExp_mul_of_stronglyMeasurable_left (stronglyAdapted_brownianExponentialWith hB c s)
    ((brownianExponentialWith_factor hB c hst) ▸ integrable_brownianExponentialWith hB c t)
    (integrable_brownianExponentialWithIncrement hB c hst)
  rw [brownianExponentialWith_factor hB c hst]
  filter_upwards [hp, hi] with ω hpω hiω
  rw [hpω, Pi.mul_apply, hiω, integral_brownianExponentialWithIncrement hB c hst, mul_one]

theorem brownianExponentialWith_condExp_endpoint (hB : IsPreBrownianReal B μ) (c : ℝ)
    {s T : ℝ≥0} (hs : s ≤ T) :
    μ[brownianExponentialWith hB c T | brownianNaturalFiltration hB s] =ᵐ[μ]
      brownianExponentialWith hB c s := (martingale_brownianExponentialWith hB c).condExp_ae_eq hs

theorem uniformIntegrable_brownianExponentialWith_bounded (hB : IsPreBrownianReal B μ) (c : ℝ) (T : ℝ≥0) :
    UniformIntegrable (fun s : Set.Iic T => brownianExponentialWith hB c s.1) 1 μ := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  apply ((integrable_brownianExponentialWith hB c T).uniformIntegrable_condExp
    (fun s : Set.Iic T => (brownianNaturalFiltration hB).le s.1)).ae_eq
  intro s
  exact brownianExponentialWith_condExp_endpoint hB c s.property

theorem brownianExponentialWith_stopped_eq_condExp (hB : IsPreBrownianReal B μ) (c : ℝ)
    {τ : Ω → WithTop ℝ≥0} {T : ℝ≥0}
    (hτ : IsStoppingTime (brownianNaturalFiltration hB) τ)
    (hbound : ∀ ω, τ ω ≤ T) (hcount : (Set.range τ).Countable) :
    stoppedValue (brownianExponentialWith hB c) τ =ᵐ[μ]
      μ[brownianExponentialWith hB c T | hτ.measurableSpace] := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  exact (martingale_brownianExponentialWith hB c).stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
    hτ hbound hcount

/-- All countable-range stopping times below one fixed deterministic endpoint
form a uniformly integrable family, providing the continuous-limit input. -/
theorem uniformIntegrable_brownianExponentialWith_stopped (hB : IsPreBrownianReal B μ) (c : ℝ)
    {ι : Type*} {τ : ι → Ω → WithTop ℝ≥0} {T : ℝ≥0}
    (hτ : ∀ i, IsStoppingTime (brownianNaturalFiltration hB) (τ i))
    (hbound : ∀ i ω, τ i ω ≤ T) (hcount : ∀ i, (Set.range (τ i)).Countable) :
    UniformIntegrable (fun i => stoppedValue (brownianExponentialWith hB c) (τ i)) 1 μ := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  apply ((integrable_brownianExponentialWith hB c T).uniformIntegrable_condExp
    (fun i => (hτ i).measurableSpace_le)).ae_eq
  intro i
  exact (brownianExponentialWith_stopped_eq_condExp hB c (hτ i) (hbound i) (hcount i)).symm

theorem integral_brownianExponentialWith_stopped (hB : IsPreBrownianReal B μ) (c : ℝ)
    {τ : Ω → WithTop ℝ≥0} {T : ℝ≥0}
    (hτ : IsStoppingTime (brownianNaturalFiltration hB) τ)
    (hbound : ∀ ω, τ ω ≤ T) (hcount : (Set.range τ).Countable) :
    (∫ ω, stoppedValue (brownianExponentialWith hB c) τ ω ∂μ) = 1 := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  rw [integral_congr_ae (brownianExponentialWith_stopped_eq_condExp hB c hτ hbound hcount),
    integral_condExp hτ.measurableSpace_le, integral_brownianExponentialWith hB c T]

def actualBrownianExponentialWith (B : ℝ≥0 → Ω → ℝ) (c : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (c * B t ω - (c ^ 2 / 2) * (t : ℝ))

/-- The measurable modification agrees with the original process at every
countable-range random time, on one null-set complement for that random time. -/
theorem brownianExponentialWith_stopped_ae_eq_actual (hB : IsPreBrownianReal B μ) (c : ℝ)
    {τ : Ω → WithTop ℝ≥0} (hcount : (Set.range τ).Countable) :
    stoppedValue (brownianExponentialWith hB c) τ =ᵐ[μ]
      stoppedValue (actualBrownianExponentialWith B c) τ := by
  let S : Set ℝ≥0 := Set.range (fun ω => (τ ω).untopA)
  have hS : S.Countable := by
    simpa only [S, ← Set.range_comp, Function.comp_def] using hcount.image WithTop.untopA
  have : Countable S := hS.to_subtype
  filter_upwards [measurableBrownian_countable_ae_eq hB (fun q : S => q.1)] with ω hω
  exact congrArg (fun x : ℝ => Real.exp (c * x - (c ^ 2 / 2) * ((τ ω).untopA : ℝ)))
    (hω ⟨(τ ω).untopA, ⟨ω, rfl⟩⟩)

/-- A continuous-time limit of bounded countable-range stopping times preserves
the exponential expectation. Both integrability and expectation are conclusions;
no optional-sampling property of the limiting random time is assumed. -/
theorem integral_actualBrownianExponentialWith_stopping_limit (hB : IsBrownianReal B μ) (c : ℝ)
    {τ : ℕ → Ω → WithTop ℝ≥0} {ρ : Ω → ℝ≥0} {T : ℝ≥0}
    (hτ : ∀ n, IsStoppingTime (brownianNaturalFiltration hB.toIsPreBrownianReal) (τ n))
    (hbound : ∀ n ω, τ n ω ≤ T) (hcount : ∀ n, (Set.range (τ n)).Countable)
    (hconv : ∀ᵐ ω ∂μ, Tendsto (fun n => (τ n ω).untopA) atTop (𝓝 (ρ ω))) :
    Integrable (fun ω => actualBrownianExponentialWith B c (ρ ω) ω) μ ∧
      (∫ ω, actualBrownianExponentialWith B c (ρ ω) ω ∂μ) = 1 := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hui := uniformIntegrable_brownianExponentialWith_stopped hB.toIsPreBrownianReal c hτ hbound hcount
  have hae : ∀ᵐ ω ∂μ, ∀ n,
      stoppedValue (brownianExponentialWith hB.toIsPreBrownianReal c) (τ n) ω =
        stoppedValue (actualBrownianExponentialWith B c) (τ n) ω :=
    ae_all_iff.mpr (fun n => brownianExponentialWith_stopped_ae_eq_actual
      hB.toIsPreBrownianReal c (hcount n))
  have hfg : ∀ᵐ ω ∂μ,
      Tendsto (fun n => stoppedValue (brownianExponentialWith hB.toIsPreBrownianReal c) (τ n) ω)
        atTop (𝓝 (actualBrownianExponentialWith B c (ρ ω) ω)) := by
    filter_upwards [hB.cont, hconv, hae] with ω hω hρ heq
    have hc : Continuous (fun t : ℝ≥0 => actualBrownianExponentialWith B c t ω) := by
      exact Real.continuous_exp.comp ((hω.const_mul c).sub (continuous_subtype_val.const_mul (c ^ 2 / 2)))
    have ht := (hc.tendsto (ρ ω)).comp hρ
    exact ht.congr (fun n => (heq n).symm)
  have hg := hui.memLp_of_ae_tendsto hfg
  refine ⟨memLp_one_iff_integrable.mp hg, ?_⟩
  have hLp := tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top hui.1 hg hui.2.1 hfg
  have hint := tendsto_integral_of_L1' (fun ω => actualBrownianExponentialWith B c (ρ ω) ω) hg.1
    (Eventually.of_forall (fun n => memLp_one_iff_integrable.mp (hui.memLp n))) hLp
  have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop
      (𝓝 (∫ ω, actualBrownianExponentialWith B c (ρ ω) ω ∂μ)) := by
    convert hint using 1
    funext n
    exact (integral_brownianExponentialWith_stopped hB.toIsPreBrownianReal c
      (hτ n) (hbound n) (hcount n)).symm
  exact tendsto_nhds_unique hc tendsto_const_nhds

end BrownianAffine
