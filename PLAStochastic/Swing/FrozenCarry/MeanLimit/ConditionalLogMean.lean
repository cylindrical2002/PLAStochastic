import PLAStochastic.Swing.FrozenCarry.MeanLimit.Asymptotic
import PLAStochastic.Swing.Gaussian.ZeroLadder.MeanValue
import PLAStochastic.Swing.Gaussian.Bridge.InfiniteSurvivalChain

/-!
# Theorem 3.2: conditional logarithmic mean

The component estimates for the finite--infinite/bridge argument live in the
`FrozenInterior*` modules.  This file provides the single theorem-level
interface consumed by the paper: pointwise and compact uniform convergence,
the all-state upper bound, and the value at zero.  The bridge and
finite-to-infinite limits are exported separately below, so that their
quantifiers remain visible instead of being hidden in a conjunction.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/- The explicit Gaussian ballot remainder tends to zero on every interior
sequence.  The only sequence-side hypothesis is the defining interior-window
condition; no finite--infinite error is postulated. -/
theorem theorem_3_2_interior_tail_error_tendsto_zero
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ : ℝ} (hδ : 0 < δ) {K : Set ℝ} (hK : IsCompact K)
    (hK0 : K ⊆ Ici 0) {E : ℕ → ℝ} {n : ℕ → ℕ}
    (hE : Tendsto E atTop atTop)
    (hwin : ∀ᶠ k : ℕ in atTop, frozenInteriorWindow δ (E k) (n k)) :
    ∀ w ∈ K, Tendsto
      (fun k => frozenScaledTail X μ w (E k) (n k) -
        4 * gaussianRenewalPotential X μ w)
      atTop (𝓝 0) := by
  intro w hw
  apply Metric.tendsto_nhds.mpr
  intro η hη
  have hU := frozenScaledTail_interior_uniform hX hi hG hδ hK hK0 hη
  have hUE := hE.eventually hU
  filter_upwards [hUE, hwin] with k hk hnk
  have hh := hk (n k) hnk w hw
  simpa only [Real.dist_eq, sub_zero] using hh

/- The inner bridge limit is a genuine consequence of the finite-dimensional
change-of-measure identity and the Gaussian density limit; no remainder
estimate is assumed. -/
theorem theorem_3_2_bridge_inner_limit
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {M : ℕ} (hM : 0 < M) {N : ℕ → ℕ}
    (hMN : ∀ k, M < N k)
    (hrem : Tendsto (fun k => ((N k - M : ℕ) : ℝ≥0)) atTop atTop)
    (hrem_m : ∀ k, (M : ℝ≥0) ≤ ((N k - M : ℕ) : ℝ≥0))
    {x a : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun k => μ.real (gaussianBridgeSurvives X (N k) x a M)) atTop
      (𝓝 (μ.real (gaussianHalfLineSurvives X x a M))) := by
  have := hi.isProbabilityMeasure
  exact gaussianBridgeSurvives_two_stage_limit hX hi hG hM hMN hrem hrem_m hx

/- The outer finite-to-infinite passage is the exact decreasing-event limit;
it does not use the normalized error estimate. -/
theorem theorem_3_2_bridge_outer_limit
    [IsFiniteMeasure μ] (hX : ∀ n, Measurable (X n))
    {x a : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun M : ℕ => μ.real (gaussianHalfLineSurvives X x a M)) atTop
      (𝓝 (gaussianInfiniteSurvival X μ x a)) := by
  exact gaussianSurvivalEvent_bridge_iterated_limit hX hx

theorem theorem_3_2_conditional_mean
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    (∀ w : ℝ, 0 ≤ w →
      Tendsto
        (fun E : ℝ =>
          (∫ ω, frozenPrefixLengthReal X w E ω ∂μ) /
            (E * Real.log E))
        atTop (𝓝 (4 * gaussianRenewalPotential X μ w))) ∧
    (∀ K : Set ℝ, IsCompact K → K ⊆ Ici 0 →
      TendstoUniformlyOn
        (fun (E w : ℝ) =>
          (∫ ω, frozenPrefixLengthReal X w E ω ∂μ) /
            (E * Real.log E))
        (fun w => 4 * gaussianRenewalPotential X μ w) atTop K) ∧
    (∀ w E : ℝ, 1 ≤ E →
      (∫ ω, frozenPrefixLengthReal X w E ω ∂μ) ≤
        frozenUniformMeanConstant * E * (1 + max w 0) *
          Real.log (Real.exp 1 * E)) ∧
    gaussianRenewalPotential X μ 0 = 1 / Real.sqrt 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w hw
    exact frozenPrefixLength_mean_tendsto hX hi hG hw
  · intro K hK hK0
    exact frozenPrefixLength_mean_tendstoUniformlyOn hX hi hG hK hK0
  · intro w E hE
    exact frozenPrefixLength_uniform_mean_bound hX hi hG w hE
  · exact gaussianRenewalPotential_zero_value hX hi hG

/- The numerical coefficient in the zero-state sentence of Theorem 3.2 is
obtained from the actual Gaussian ladder mean, not introduced as a constant. -/
theorem theorem_3_2_zero_mean_limit
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    Tendsto
      (fun E : ℝ =>
        (∫ ω, frozenPrefixLengthReal X 0 E ω ∂μ) / (E * Real.log E))
      atTop (𝓝 (2 * Real.sqrt 2)) := by
  have hlim := frozenPrefixLength_mean_tendsto hX hi hG (w := 0) (by norm_num)
  rw [gaussianRenewalPotential_zero_value hX hi hG] at hlim
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have heq : 4 * (1 / Real.sqrt 2) = 2 * Real.sqrt 2 := by
    field_simp
    nlinarith
  simpa only [heq] using hlim

end SwingRepair
