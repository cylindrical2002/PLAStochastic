import PLAStochastic.Swing.Gaussian.Stopping.CappedExitPosition
import PLAStochastic.Swing.Gaussian.Stopping.StoppedLinearDrift

/-! # Actual unbounded linear stopping, justified by selected overshoot domination -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- A finite exit is eventually unchanged by capping, path by path. -/
theorem capDiscreteTime_eventually_eq {τ : WithTop ℕ} (hτ : τ ≠ ⊤) :
    ∀ᶠ m : ℕ in atTop, capDiscreteTime τ m = τ.untopD 0 := by
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hτ
  filter_upwards [eventually_ge_atTop k] with m hm
  apply capDiscreteTime_eq_of_le
  rw [← hk]
  exact WithTop.coe_le_coe.mpr hm

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- The actual stopped exit position is dominated almost surely by R plus its overshoot. -/
theorem gaussianStrip_exitPosition_integrable_of_overshoot [IsFiniteMeasure μ]
    (hX : ∀ n, Measurable (X n)) {x a R : ℝ} (hR : 0 ≤ R)
    (hτ : ∀ᵐ ω ∂μ, gaussianStripExit X x a R ω ≠ ⊤)
    (hO : Integrable (gaussianStripOvershoot X x a R) μ) :
    Integrable (gaussianStripExitPosition X x a R) μ := by
  apply ((integrable_const R).add hO).mono'
    (gaussianStripExitPosition_measurable hX x a R).aestronglyMeasurable
  filter_upwards [hτ] with ω hω
  obtain ⟨m, hm⟩ := (capDiscreteTime_eventually_eq hω).exists
  have hb := gaussianStrip_capped_position_norm_le (X := X) (x := x) (a := a) hR m ω
  rw [hm] at hb
  exact hb

/-- Dominated convergence passes bounded stopping to the actual exit position. -/
theorem gaussianStrip_capped_position_integral_tendsto [IsFiniteMeasure μ]
    (hX : ∀ n, Measurable (X n)) {x a R : ℝ} (hR : 0 ≤ R)
    (hτ : ∀ᵐ ω ∂μ, gaussianStripExit X x a R ω ≠ ⊤)
    (hO : Integrable (gaussianStripOvershoot X x a R) μ) :
    Tendsto (fun m : ℕ => ∫ ω,
      gaussianDriftWalk X x a (capDiscreteTime (gaussianStripExit X x a R ω) m) ω ∂μ)
      atTop (𝓝 (∫ ω, gaussianStripExitPosition X x a R ω ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun ω => R + gaussianStripOvershoot X x a R ω)
  · intro m
    exact (countableSelection_measurable (gaussianDriftWalk_measurable hX x a)
      (capDiscreteTime_measurable (gaussianStripExit_isStoppingTime hX x a R).measurable' m)).aestronglyMeasurable
  · exact (integrable_const R).add hO
  · intro m
    exact Eventually.of_forall (gaussianStrip_capped_position_norm_le hR m)
  · filter_upwards [hτ] with ω hω
    apply tendsto_const_nhds.congr'
    filter_upwards [capDiscreteTime_eventually_eq hω] with m hm
    rw [hm]
    rfl

/-- The capped time expectations converge to the actual integrable exit time. -/
theorem capDiscreteTime_integral_tendsto [IsFiniteMeasure μ]
    {τ : Ω → WithTop ℕ} (hτ : Measurable[mΩ] τ) (hf : ∀ᵐ ω ∂μ, τ ω ≠ ⊤)
    (hi : Integrable (fun ω => (((τ ω).untopD 0 : ℕ) : ℝ)) μ) :
    Tendsto (fun m : ℕ => ∫ ω, (capDiscreteTime (τ ω) m : ℝ) ∂μ) atTop
      (𝓝 (∫ ω, (((τ ω).untopD 0 : ℕ) : ℝ) ∂μ)) := by
  apply integral_tendsto_of_tendsto_of_monotone (capDiscreteTime_integrable hτ) hi
  · exact Eventually.of_forall (fun ω i j hij => by dsimp only; exact_mod_cast capDiscreteTime_monotone (τ ω) hij)
  · filter_upwards [hf] with ω hω
    apply tendsto_const_nhds.congr'
    filter_upwards [capDiscreteTime_eventually_eq hω] with m hm
    rw [hm]

/-- Actual Wald identity; integrability and convergence are proved before the limit is taken. -/
theorem gaussianStrip_exitPosition_integral_eq
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {x a R : ℝ} (hR : 0 ≤ R)
    (hf : ∀ᵐ ω ∂μ, gaussianStripExit X x a R ω ≠ ⊤)
    (ht : Integrable (fun ω => (((gaussianStripExit X x a R ω).untopD 0 : ℕ) : ℝ)) μ)
    (hO : Integrable (gaussianStripOvershoot X x a R) μ) :
    (∫ ω, gaussianStripExitPosition X x a R ω ∂μ) =
      x + a * ∫ ω, (((gaussianStripExit X x a R ω).untopD 0 : ℕ) : ℝ) ∂μ := by
  have : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hleft := gaussianStrip_capped_position_integral_tendsto hX hR hf hO
  have hright := (capDiscreteTime_integral_tendsto
    (gaussianStripExit_isStoppingTime hX x a R).measurable' hf ht).const_mul a |>.const_add x
  simp_rw [gaussianStrip_capped_position_integral hX hi hG x a R] at hleft
  exact tendsto_nhds_unique hleft hright

/-- Upper exit is controlled by the actual stopped position and actual overshoot. -/
theorem gaussianStrip_upperExit_mul_le
    [IsFiniteMeasure μ] (hX : ∀ n, Measurable (X n)) {x a R : ℝ} (hR : 0 ≤ R)
    (hf : ∀ᵐ ω ∂μ, gaussianStripExit X x a R ω ≠ ⊤)
    (hO : Integrable (gaussianStripOvershoot X x a R) μ) :
    R * μ.real (gaussianStripUpperExit X x a R) ≤
      (∫ ω, gaussianStripExitPosition X x a R ω ∂μ) +
        ∫ ω, gaussianStripOvershoot X x a R ω ∂μ := by
  have hs := gaussianStripUpperExit_measurable hX x a R
  have hp := gaussianStrip_exitPosition_integrable_of_overshoot hX hR hf hO
  have hl := integral_mono_ae ((integrable_const R).indicator hs) (hp.add hO) ?_
  · simp only [Pi.add_apply] at hl
    rw [integral_indicator hs, setIntegral_const, integral_add hp hO] at hl
    simpa only [smul_eq_mul, mul_comm] using hl
  · filter_upwards [hf] with ω hω
    by_cases hu : ω ∈ gaussianStripUpperExit X x a R
    · simp only [indicator_of_mem hu, Pi.add_apply]
      have ho := gaussianStripOvershoot_nonneg X x a R ω
      linarith [hu.2]
    · simp only [indicator_of_notMem hu, Pi.add_apply]
      have ho : -gaussianStripExitPosition X x a R ω ≤ gaussianStripOvershoot X x a R ω := by
        rw [gaussianStripOvershoot, if_neg hω]
        exact (le_max_left _ _).trans (le_max_right _ _)
      linarith

end SwingRepair
