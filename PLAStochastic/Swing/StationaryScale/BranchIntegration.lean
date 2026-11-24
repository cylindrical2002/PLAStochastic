import PLAStochastic.Swing.StationaryScale.AbsorptionArithmetic
import PLAStochastic.Swing.StationaryScale.RestartInvariantLaw

/-! # Stationary `π_E` branch integration and absorption

This file closes the measure-theoretic bookkeeping after the favourable and
unfavourable branch estimates have been proved.  A pointwise branch estimate is
integrated against an invariant probability law, then the scalar residual is
absorbed by `stationary_absorb_E_log`.  The branch estimate itself remains an
explicit hypothesis: this keeps the exact probabilistic charging obligation
visible instead of replacing it by an opaque axiom.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-- Integrating a one-step branch inequality against a probability law. -/
theorem stationary_branch_integral_le
    {S : Type*} [MeasurableSpace S] {π : Measure S} [IsProbabilityMeasure π]
    {F B : S → ℝ} {b : ℝ}
    (hF : Integrable F π) (hB : Integrable B π)
    (hpoint : ∀ᵐ s ∂π, F s ≤ B s + b * F s) :
    (∫ s, F s ∂π) ≤ (∫ s, B s ∂π) + b * (∫ s, F s ∂π) := by
  have hmul : Integrable (fun s => b * F s) π := hF.const_mul b
  have hsum : Integrable (fun s => B s + b * F s) π := hB.add hmul
  have hmono := integral_mono_ae hF hsum hpoint
  rw [integral_add hB hmul, integral_const_mul] at hmono
  exact hmono

/-- The stationary `π_E` absorption step used in Theorem 4.2.

`hpoint` is the favourable/unfavourable branch estimate before integration;
`hBint` is its integrated main term.  Thus the theorem is a concrete,
checkable interface for the final `π_E` calculation and yields the advertised
`2 K E log E` bound whenever the residual coefficient is at most one half.
-/
theorem nativeRestart_stationary_pi_E_absorb
    (hX : ∀ k, Measurable (X k)) (hi : iIndepFun X μ)
    (hG : ∀ k, μ.map (X k) = gaussianReal 0 1)
    {E K b : ℝ} (hE : 0 < E) (hE1 : 1 ≤ E)
    {π : Measure ℝ} [IsProbabilityMeasure π]
    (_hπ : (nativeRestartKernel X μ E).Invariant π)
    (hK : 0 ≤ K) (hb : 0 ≤ b) (hbhalf : b ≤ (1/2 : ℝ))
    (hcoef : b = K*(Real.log E)^(3/2)/E)
    (hB : ℝ → ℝ) (_hBmeas : Measurable hB) (hBint : Integrable hB π)
    (hBbound : (∫ x, hB x ∂π) ≤ K*E*Real.log E)
    (hpoint : ∀ᵐ x ∂π,
      nativeRestartMean X μ E x ≤ hB x + b * nativeRestartMean X μ E x) :
    (∫ x, nativeRestartMean X μ E x ∂π) ≤ 2*(K*E*Real.log E) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  let : IsFiniteMeasure π := inferInstance
  have hmean_meas : Measurable (nativeRestartMean X μ E) :=
    nativeRestartMean_measurable hX E
  have hbounds := nativeRestartMean_bounds hX hi hG hE
  have hmean_nonneg : ∀ x, 0 ≤ nativeRestartMean X μ E x :=
    fun x => (by exact (by norm_num : (0 : ℝ) ≤ 1).trans (hbounds x).1)
  have hmean_upper : ∀ x, nativeRestartMean X μ E x ≤ nativeRestartMeanBound E :=
    fun x => (hbounds x).2
  have hmean_int : Integrable (nativeRestartMean X μ E) π :=
    Doeblin.integrable_bounded_reward π hmean_meas hmean_nonneg hmean_upper
  have hbranch := stationary_branch_integral_le hmean_int hBint hpoint
  have hC : 0 ≤ (∫ x, nativeRestartMean X μ E x ∂π) :=
    integral_nonneg hmean_nonneg
  have hA : 0 ≤ K*E*Real.log E := by
    have hlog : 0 ≤ Real.log E := Real.log_nonneg hE1
    positivity
  have hcoef_nonneg : 0 ≤ K*(Real.log E)^(3/2)/E := by
    rw [← hcoef]
    exact hb
  have hres : b ≤ (1/2 : ℝ) := hbhalf
  have hineq : (∫ x, nativeRestartMean X μ E x ∂π) ≤
      K*E*Real.log E + b*(∫ x, nativeRestartMean X μ E x ∂π) := by
    have htemp : (∫ x, hB x ∂π) + b * (∫ x, nativeRestartMean X μ E x ∂π) ≤
        K*E*Real.log E + b * (∫ x, nativeRestartMean X μ E x ∂π) :=
      by
        simpa [add_comm, add_left_comm, add_assoc] using
          (add_le_add_right hBbound (b * (∫ x, nativeRestartMean X μ E x ∂π)))
    exact hbranch.trans htemp
  exact stationary_absorb_half hC hA hb hres hineq

/-- Convenience specialization with the residual coefficient in its explicit
`K (log E)^(3/2) / E` form. -/
theorem nativeRestart_stationary_pi_E_absorb_explicit
    (hX : ∀ k, Measurable (X k)) (hi : iIndepFun X μ)
    (hG : ∀ k, μ.map (X k) = gaussianReal 0 1)
    {E K : ℝ} (hE : 0 < E) (hE1 : 1 ≤ E)
    {π : Measure ℝ} [IsProbabilityMeasure π]
    (_hπ : (nativeRestartKernel X μ E).Invariant π)
    (hK : 0 ≤ K)
    (hcoef : K*(Real.log E)^(3/2)/E ≤ (1/2 : ℝ))
    (hB : ℝ → ℝ) (_hBmeas : Measurable hB) (hBint : Integrable hB π)
    (hBbound : (∫ x, hB x ∂π) ≤ K*E*Real.log E)
    (hpoint : ∀ᵐ x ∂π,
      nativeRestartMean X μ E x ≤
        hB x + (K*(Real.log E)^(3/2)/E) * nativeRestartMean X μ E x) :
    (∫ x, nativeRestartMean X μ E x ∂π) ≤ 2*(K*E*Real.log E) := by
  have hb : 0 ≤ K*(Real.log E)^(3/2)/E := by
    have hlog : 0 ≤ Real.log E := Real.log_nonneg hE1
    positivity
  apply nativeRestart_stationary_pi_E_absorb (b := K*(Real.log E)^(3/2)/E)
    hX hi hG hE hE1 _hπ hK hb hcoef rfl hB _hBmeas hBint hBbound
  exact hpoint

/-! ### Invariant-law disintegration

The next identity turns a stationary `π_E` integral into the integral over
the current state and a fresh increment sequence.  It is the precise
measure-theoretic bridge needed to insert the stopped-sum and charging
estimates into the stationary calculation.
-/

theorem nativeRestart_invariant_integral_eq_fresh
    (hX : ∀ k, Measurable (X k))
    {E : ℝ} {π : Measure ℝ} [IsProbabilityMeasure π]
    [SFinite μ]
    (hπ : (nativeRestartKernel X μ E).Invariant π)
    {f : ℝ → ℝ} (hf : Measurable f)
    (hint : Integrable f π) :
    (∫ y, f y ∂π) =
      ∫ x, ∫ ω, f (nativeRestartNext X E x ω) ∂μ ∂π := by
  let : IsFiniteMeasure π := inferInstance
  have hμfin : SFinite μ := by infer_instance
  have hπfin : SFinite π := by infer_instance
  have hnext : Measurable (fun p : ℝ × Ω => nativeRestartNext X E p.1 p.2) :=
    nativeRestartNext_measurable X hX E
  have hprod : nativeRestartKernel X μ E ∘ₘ π =
      (π.prod μ).map (fun p : ℝ × Ω => nativeRestartNext X E p.1 p.2) :=
    nativeRestartKernel_comp_eq_map_prod hX E
  have hcomp : Measurable (fun p : ℝ × Ω => f (nativeRestartNext X E p.1 p.2)) :=
    hf.comp hnext
  have hmap : Measure.map (fun p : ℝ × Ω => nativeRestartNext X E p.1 p.2) (π.prod μ) = π := by
    rw [← hprod, hπ]
  have hintmap : Integrable f
      (Measure.map (fun p : ℝ × Ω => nativeRestartNext X E p.1 p.2) (π.prod μ)) := by
    simpa [hmap] using hint
  have hcomp_int : Integrable (fun p : ℝ × Ω => f (nativeRestartNext X E p.1 p.2))
      (π.prod μ) := hintmap.comp_measurable hnext
  calc
    (∫ y, f y ∂π) = ∫ y, f y ∂(nativeRestartKernel X μ E ∘ₘ π) := by rw [hπ]
    _ = ∫ p, f (nativeRestartNext X E p.1 p.2) ∂(π.prod μ) := by
      rw [hprod]
      exact MeasureTheory.integral_map hnext.aemeasurable hf.aestronglyMeasurable
    _ = ∫ x, ∫ ω, f (nativeRestartNext X E x ω) ∂μ ∂π :=
      MeasureTheory.integral_prod _ hcomp_int

end SwingRepair
