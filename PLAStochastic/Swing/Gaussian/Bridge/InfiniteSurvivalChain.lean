import PLAStochastic.Swing.Gaussian.Bridge.HorizonLimit
import PLAStochastic.Swing.Gaussian.Bridge.Ballot
import PLAStochastic.Swing.Gaussian.Survival.FiniteToInfinite

/-! C.3 bridge-to-infinite survival chain.

This file connects the finite-dimensional bridge change of measure to the
ordinary finite survival event and then to the infinite survival event.  The
statements are deliberately split into an inner (bridge horizon) limit and an
outer (survival horizon) limit; this is the mathematically valid order used in
C.3 and avoids silently assuming a two-parameter uniformity estimate.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {X : ℕ → Ω → ℝ}

/-- For a fixed prefix length, a Gaussian bridge with diverging remainder
variance has the same survival probability as the unconditioned Gaussian
prefix. -/
theorem gaussianBridgeSurvives_tendsto_finite_survival
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {M : ℕ} (_hM : 0 < M) {N : ℕ → ℕ}
    (hMN : ∀ k, M < N k)
    (hrem : Tendsto (fun k => ((N k - M : ℕ) : ℝ≥0)) atTop atTop)
    (hrem_m : ∀ k, (M : ℝ≥0) ≤ ((N k - M : ℕ) : ℝ≥0))
    {x a : ℝ} (_hx : 0 ≤ x) :
    Tendsto (fun k => μ (gaussianBridgeSurvives X (N k) x a M)) atTop
      (𝓝 (μ (gaussianHalfLineSurvives X x a M))) := by
  let A : Set (Fin M → ℝ) :=
    gaussianHalfLineSurvives (gaussianFiniteSamples M) x a M
  have hA : MeasurableSet A := gaussianFiniteSamples_survives_measurable M x a
  have hbridge := gaussianBridgePrefix_actual_event_tendsto_unconditioned
    (μ := μ) hX hi hG hMN hrem hrem_m hA
  have heq : ∀ k, gaussianBridgeSurvives X (N k) x a M =
      (gaussianBridgeIncrementPrefix X (N k) M) ⁻¹' A := by
    intro k
    exact gaussianBridgeSurvives_eq_preimage (X := X) (N k) M x a
  have htarget : (Measure.pi (fun _ : Fin M => gaussianReal 0 1)) A =
      μ (gaussianHalfLineSurvives X x a M) := by
    have hlaw := gaussianFiniteSamples_hasLaw hX hi hG M
    have hm := hlaw.measure_eq hA
    have hset : {ω : Ω | (fun i : Fin M => X i.val ω) ∈ A} =
        gaussianHalfLineSurvives X x a M := by
      ext ω
      exact gaussianFiniteSamples_actual_survives M x a ω
    change μ {ω : Ω | (fun i : Fin M => X i.val ω) ∈ A} =
      (Measure.pi (fun _ : Fin M => gaussianReal 0 1)) A at hm
    rw [hset] at hm
    exact hm.symm
  have hseq : (fun k => μ (gaussianBridgeSurvives X (N k) x a M)) =ᶠ[atTop]
      (fun k => μ ((gaussianBridgeIncrementPrefix X (N k) M) ⁻¹' A)) :=
    Eventually.of_forall (fun k => by simpa only using congrArg μ (heq k))
  have hnew := Filter.Tendsto.congr' hseq.symm hbridge
  rw [htarget] at hnew
  exact hnew

/-- The outer finite-survival limit closes the C.3 chain.  In particular, the
iterated bridge limit (first remainder horizon, then prefix horizon) equals the
actual infinite-survival probability. -/
theorem gaussianSurvivalEvent_bridge_iterated_limit
    [IsFiniteMeasure μ]
    (hX : ∀ n, Measurable (X n))
    {x a : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun M : ℕ => μ.real (gaussianHalfLineSurvives X x a M)) atTop
      (𝓝 (gaussianInfiniteSurvival X μ x a)) := by
  simpa [gaussianHalfLineSurvives_eq_survivalEvent hx] using
    (gaussianSurvivalEvent_tendsto_infinite (μ := μ) (X := X) hX hx)

/-- Sequential C.3 chain with a fixed prefix: after taking the bridge
remainder to infinity, the remaining finite survival error vanishes along any
prefix sequence tending to infinity. -/
theorem gaussianBridgeSurvives_two_stage_limit
    [IsFiniteMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {M : ℕ} (_hM : 0 < M) {N : ℕ → ℕ}
    (hMN : ∀ k, M < N k)
    (hrem : Tendsto (fun k => ((N k - M : ℕ) : ℝ≥0)) atTop atTop)
    (hrem_m : ∀ k, (M : ℝ≥0) ≤ ((N k - M : ℕ) : ℝ≥0))
    {x a : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun k => μ.real (gaussianBridgeSurvives X (N k) x a M)) atTop
      (𝓝 (μ.real (gaussianHalfLineSurvives X x a M))) := by
  have h := gaussianBridgeSurvives_tendsto_finite_survival
    (μ := μ) (x := x) (a := a) hX hi hG _hM hMN hrem hrem_m hx
  have htarget : μ (gaussianHalfLineSurvives X x a M) ≠ ∞ := measure_ne_top μ _
  have htoReal := (ENNReal.continuousAt_toReal htarget).tendsto.comp h
  change Tendsto (fun k => ENNReal.toReal (μ (gaussianBridgeSurvives X (N k) x a M))) atTop
      (𝓝 (ENNReal.toReal (μ (gaussianHalfLineSurvives X x a M))))
  exact htoReal

end SwingRepair
