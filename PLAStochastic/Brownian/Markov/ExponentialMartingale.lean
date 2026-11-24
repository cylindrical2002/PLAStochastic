import PLAStochastic.Brownian.PathLaw.TimeInversion
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.ConditionalExpectation

/-!
# The Brownian exponential martingale on a measurable modification

The modification has measurable coordinates and the exact Brownian finite laws.
It agrees with the original process simultaneously on every countable set of
times. Continuity is only used on the original Brownian process in later limits.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace BrownianAffine

set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

def measurableBrownian (hB : IsPreBrownianReal B μ) (t : ℝ≥0) : Ω → ℝ :=
  (hB.aemeasurable t).mk (B t)

theorem measurable_measurableBrownian (hB : IsPreBrownianReal B μ) (t : ℝ≥0) :
    Measurable (measurableBrownian hB t) := (hB.aemeasurable t).measurable_mk

theorem measurableBrownian_ae_eq (hB : IsPreBrownianReal B μ) (t : ℝ≥0) :
    measurableBrownian hB t =ᵐ[μ] B t := (hB.aemeasurable t).ae_eq_mk.symm

theorem measurableBrownian_countable_ae_eq (hB : IsPreBrownianReal B μ)
    {ι : Type*} [Countable ι] (t : ι → ℝ≥0) :
    ∀ᵐ ω ∂μ, ∀ i, measurableBrownian hB (t i) ω = B (t i) ω :=
  ae_all_iff.mpr (fun i => measurableBrownian_ae_eq hB (t i))

theorem isPreBrownianReal_measurableBrownian (hB : IsPreBrownianReal B μ) :
    IsPreBrownianReal (measurableBrownian hB) μ :=
  hB.congr (fun t => (measurableBrownian_ae_eq hB t).symm)

def brownianNaturalFiltration (hB : IsPreBrownianReal B μ) : Filtration ℝ≥0 ‹MeasurableSpace Ω› :=
  Filtration.natural (measurableBrownian hB)
    (fun t => (measurable_measurableBrownian hB t).stronglyMeasurable)

def brownianExponential (hB : IsPreBrownianReal B μ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (2 * measurableBrownian hB t ω - 2 * (t : ℝ))

theorem gaussian_exponential_integrable {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) μ) (hm : Measurable X) :
    Integrable (fun ω => Real.exp (2 * X ω - 2 * (v : ℝ))) μ := by
  have h := (hX.measurePreserving hm).integrable_comp_of_integrable
    (integrable_exp_mul_gaussianReal (μ := 0) (v := v) 2)
  convert h.mul_const (Real.exp (-2 * (v : ℝ))) using 1
  funext ω
  dsimp only [Function.comp_def]
  rw [← Real.exp_add]
  congr 1
  ring

theorem gaussian_exponential_integral {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) μ) :
    (∫ ω, Real.exp (2 * X ω - 2 * (v : ℝ)) ∂μ) = 1 := by
  have heq : (fun ω => Real.exp (2 * X ω - 2 * (v : ℝ))) =
      (fun ω => Real.exp (2 * X ω) * Real.exp (-2 * (v : ℝ))) := by
    funext ω
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq, integral_mul_const]
  change mgf X μ 2 * Real.exp (-2 * (v : ℝ)) = 1
  rw [mgf_gaussianReal hX.map_eq, ← Real.exp_add]
  convert Real.exp_zero using 1
  congr 1
  ring

theorem integrable_brownianExponential (hB : IsPreBrownianReal B μ) (t : ℝ≥0) :
    Integrable (brownianExponential hB t) μ :=
  gaussian_exponential_integrable ((isPreBrownianReal_measurableBrownian hB).hasLaw_eval t)
    (measurable_measurableBrownian hB t)

theorem integral_brownianExponential (hB : IsPreBrownianReal B μ) (t : ℝ≥0) :
    (∫ ω, brownianExponential hB t ω ∂μ) = 1 :=
  gaussian_exponential_integral ((isPreBrownianReal_measurableBrownian hB).hasLaw_eval t)

theorem stronglyAdapted_brownianExponential (hB : IsPreBrownianReal B μ) :
    StronglyAdapted (brownianNaturalFiltration hB) (brownianExponential hB) := by
  intro t
  have h := Filtration.stronglyAdapted_natural
    (fun t => (measurable_measurableBrownian hB t).stronglyMeasurable) t
  exact Real.continuous_exp.comp_stronglyMeasurable ((h.const_mul 2).sub stronglyMeasurable_const)

def brownianExponentialIncrement (hB : IsPreBrownianReal B μ) (s t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (2 * (measurableBrownian hB t ω - measurableBrownian hB s ω) -
    2 * ((t - s : ℝ≥0) : ℝ))

theorem measurable_brownianExponentialIncrement (hB : IsPreBrownianReal B μ) (s t : ℝ≥0) :
    Measurable (brownianExponentialIncrement hB s t) :=
  Real.measurable_exp.comp
    (((measurable_measurableBrownian hB t).sub (measurable_measurableBrownian hB s)).const_mul 2
      |>.sub_const (2 * ((t - s : ℝ≥0) : ℝ)))

theorem brownianIncrement_hasLaw (hB : IsPreBrownianReal B μ) {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω => measurableBrownian hB t ω - measurableBrownian hB s ω)
      (gaussianReal 0 (t - s)) μ := by
  simpa only [add_tsub_cancel_of_le hst] using
    ((isPreBrownianReal_measurableBrownian hB).shift s).hasLaw_eval (t - s)

theorem integrable_brownianExponentialIncrement (hB : IsPreBrownianReal B μ)
    {s t : ℝ≥0} (hst : s ≤ t) : Integrable (brownianExponentialIncrement hB s t) μ :=
  gaussian_exponential_integrable (brownianIncrement_hasLaw hB hst)
    ((measurable_measurableBrownian hB t).sub (measurable_measurableBrownian hB s))

theorem integral_brownianExponentialIncrement (hB : IsPreBrownianReal B μ)
    {s t : ℝ≥0} (hst : s ≤ t) : (∫ ω, brownianExponentialIncrement hB s t ω ∂μ) = 1 :=
  gaussian_exponential_integral (brownianIncrement_hasLaw hB hst)

theorem brownianExponential_factor (hB : IsPreBrownianReal B μ)
    {s t : ℝ≥0} (hst : s ≤ t) :
    brownianExponential hB t = brownianExponential hB s * brownianExponentialIncrement hB s t := by
  funext ω
  change Real.exp _ = Real.exp _ * Real.exp _
  rw [← Real.exp_add]
  congr 1
  rw [NNReal.coe_sub hst]
  ring

theorem indep_brownianExponentialIncrement (hB : IsPreBrownianReal B μ)
    {s t : ℝ≥0} (hst : s ≤ t) :
    Indep (MeasurableSpace.comap (brownianExponentialIncrement hB s t) inferInstance)
      (brownianNaturalFiltration hB s) μ := by
  have hi := (isPreBrownianReal_measurableBrownian hB).indepFun_shift s
  have hc := hi.comp
    (Real.measurable_exp.comp
      (((measurable_pi_apply (t - s)).const_mul 2).sub_const (2 * ((t - s : ℝ≥0) : ℝ))))
    measurable_id
  rw [brownianNaturalFiltration, Filtration.natural_eq_comap]
  change IndepFun (brownianExponentialIncrement hB s t)
    (fun ω (u : Set.Iic s) => measurableBrownian hB u.1 ω) μ
  simpa only [Function.comp_def, id_eq, add_tsub_cancel_of_le hst,
    brownianExponentialIncrement] using! hc

theorem martingale_brownianExponential (hB : IsPreBrownianReal B μ) :
    Martingale (brownianExponential hB) (brownianNaturalFiltration hB) μ := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  refine ⟨stronglyAdapted_brownianExponential hB, fun s t hst => ?_⟩
  have hi := condExp_indep_eq
    (measurable_brownianExponentialIncrement hB s t).comap_le
    ((brownianNaturalFiltration hB).le s)
    (comap_measurable (brownianExponentialIncrement hB s t)).stronglyMeasurable
    (indep_brownianExponentialIncrement hB hst)
  have hp := condExp_mul_of_stronglyMeasurable_left (stronglyAdapted_brownianExponential hB s)
    ((brownianExponential_factor hB hst) ▸ integrable_brownianExponential hB t)
    (integrable_brownianExponentialIncrement hB hst)
  rw [brownianExponential_factor hB hst]
  filter_upwards [hp, hi] with ω hpω hiω
  rw [hpω, Pi.mul_apply, hiω, integral_brownianExponentialIncrement hB hst, mul_one]

theorem brownianExponential_condExp_endpoint (hB : IsPreBrownianReal B μ)
    {s T : ℝ≥0} (hs : s ≤ T) :
    μ[brownianExponential hB T | brownianNaturalFiltration hB s] =ᵐ[μ]
      brownianExponential hB s := (martingale_brownianExponential hB).condExp_ae_eq hs

theorem uniformIntegrable_brownianExponential_bounded (hB : IsPreBrownianReal B μ) (T : ℝ≥0) :
    UniformIntegrable (fun s : Set.Iic T => brownianExponential hB s.1) 1 μ := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  apply ((integrable_brownianExponential hB T).uniformIntegrable_condExp
    (fun s : Set.Iic T => (brownianNaturalFiltration hB).le s.1)).ae_eq
  intro s
  exact brownianExponential_condExp_endpoint hB s.property

theorem brownianExponential_stopped_eq_condExp (hB : IsPreBrownianReal B μ)
    {τ : Ω → WithTop ℝ≥0} {T : ℝ≥0}
    (hτ : IsStoppingTime (brownianNaturalFiltration hB) τ)
    (hbound : ∀ ω, τ ω ≤ T) (hcount : (Set.range τ).Countable) :
    stoppedValue (brownianExponential hB) τ =ᵐ[μ]
      μ[brownianExponential hB T | hτ.measurableSpace] := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  exact (martingale_brownianExponential hB).stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
    hτ hbound hcount

/-- All countable-range stopping times below one fixed deterministic endpoint
form a uniformly integrable family, providing the continuous-limit input. -/
theorem uniformIntegrable_brownianExponential_stopped (hB : IsPreBrownianReal B μ)
    {ι : Type*} {τ : ι → Ω → WithTop ℝ≥0} {T : ℝ≥0}
    (hτ : ∀ i, IsStoppingTime (brownianNaturalFiltration hB) (τ i))
    (hbound : ∀ i ω, τ i ω ≤ T) (hcount : ∀ i, (Set.range (τ i)).Countable) :
    UniformIntegrable (fun i => stoppedValue (brownianExponential hB) (τ i)) 1 μ := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  apply ((integrable_brownianExponential hB T).uniformIntegrable_condExp
    (fun i => (hτ i).measurableSpace_le)).ae_eq
  intro i
  exact (brownianExponential_stopped_eq_condExp hB (hτ i) (hbound i) (hcount i)).symm

theorem integral_brownianExponential_stopped (hB : IsPreBrownianReal B μ)
    {τ : Ω → WithTop ℝ≥0} {T : ℝ≥0}
    (hτ : IsStoppingTime (brownianNaturalFiltration hB) τ)
    (hbound : ∀ ω, τ ω ≤ T) (hcount : (Set.range τ).Countable) :
    (∫ ω, stoppedValue (brownianExponential hB) τ ω ∂μ) = 1 := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  rw [integral_congr_ae (brownianExponential_stopped_eq_condExp hB hτ hbound hcount),
    integral_condExp hτ.measurableSpace_le, integral_brownianExponential hB T]

def actualBrownianExponential (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (2 * B t ω - 2 * (t : ℝ))

/-- The measurable modification agrees with the original process at every
countable-range random time, on one null-set complement for that random time. -/
theorem brownianExponential_stopped_ae_eq_actual (hB : IsPreBrownianReal B μ)
    {τ : Ω → WithTop ℝ≥0} (hcount : (Set.range τ).Countable) :
    stoppedValue (brownianExponential hB) τ =ᵐ[μ]
      stoppedValue (actualBrownianExponential B) τ := by
  let S : Set ℝ≥0 := Set.range (fun ω => (τ ω).untopA)
  have hS : S.Countable := by
    simpa only [S, ← Set.range_comp, Function.comp_def] using hcount.image WithTop.untopA
  have : Countable S := hS.to_subtype
  filter_upwards [measurableBrownian_countable_ae_eq hB (fun q : S => q.1)] with ω hω
  exact congrArg (fun x : ℝ => Real.exp (2 * x - 2 * ((τ ω).untopA : ℝ)))
    (hω ⟨(τ ω).untopA, ⟨ω, rfl⟩⟩)

/-- A continuous-time limit of bounded countable-range stopping times preserves
the exponential expectation. Both integrability and expectation are conclusions;
no optional-sampling property of the limiting random time is assumed. -/
theorem integral_actualBrownianExponential_stopping_limit (hB : IsBrownianReal B μ)
    {τ : ℕ → Ω → WithTop ℝ≥0} {ρ : Ω → ℝ≥0} {T : ℝ≥0}
    (hτ : ∀ n, IsStoppingTime (brownianNaturalFiltration hB.toIsPreBrownianReal) (τ n))
    (hbound : ∀ n ω, τ n ω ≤ T) (hcount : ∀ n, (Set.range (τ n)).Countable)
    (hconv : ∀ᵐ ω ∂μ, Tendsto (fun n => (τ n ω).untopA) atTop (𝓝 (ρ ω))) :
    Integrable (fun ω => actualBrownianExponential B (ρ ω) ω) μ ∧
      (∫ ω, actualBrownianExponential B (ρ ω) ω ∂μ) = 1 := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hui := uniformIntegrable_brownianExponential_stopped hB.toIsPreBrownianReal hτ hbound hcount
  have hae : ∀ᵐ ω ∂μ, ∀ n,
      stoppedValue (brownianExponential hB.toIsPreBrownianReal) (τ n) ω =
        stoppedValue (actualBrownianExponential B) (τ n) ω :=
    ae_all_iff.mpr (fun n => brownianExponential_stopped_ae_eq_actual
      hB.toIsPreBrownianReal (hcount n))
  have hfg : ∀ᵐ ω ∂μ,
      Tendsto (fun n => stoppedValue (brownianExponential hB.toIsPreBrownianReal) (τ n) ω)
        atTop (𝓝 (actualBrownianExponential B (ρ ω) ω)) := by
    filter_upwards [hB.cont, hconv, hae] with ω hω hρ heq
    have hc : Continuous (fun t : ℝ≥0 => actualBrownianExponential B t ω) := by
      exact Real.continuous_exp.comp ((hω.const_mul 2).sub (continuous_subtype_val.const_mul 2))
    have ht := (hc.tendsto (ρ ω)).comp hρ
    exact ht.congr (fun n => (heq n).symm)
  have hg := hui.memLp_of_ae_tendsto hfg
  refine ⟨memLp_one_iff_integrable.mp hg, ?_⟩
  have hLp := tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top hui.1 hg hui.2.1 hfg
  have hint := tendsto_integral_of_L1' (fun ω => actualBrownianExponential B (ρ ω) ω) hg.1
    (Eventually.of_forall (fun n => memLp_one_iff_integrable.mp (hui.memLp n))) hLp
  have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop
      (𝓝 (∫ ω, actualBrownianExponential B (ρ ω) ω ∂μ)) := by
    convert hint using 1
    funext n
    exact (integral_brownianExponential_stopped hB.toIsPreBrownianReal
      (hτ n) (hbound n) (hcount n)).symm
  exact tendsto_nhds_unique hc tendsto_const_nhds

end BrownianAffine
