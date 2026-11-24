import PLAStochastic.Swing.Restart.Chain.CommonComponent
import PLAStochastic.ForMathlib.Probability.Kernel.Doeblin.BoundedReward

/-! # The unique fixed-tolerance stationary law of the actual SSE restart kernel

The common component, uniform duration bound, invariant measure, and quantitative
convergence are all derived from the original measurable Gaussian increments.
The connection to the successive recordings of the finite stream is maintained
separately in NativeRestartStream and NativeRestartRecursion.
-/
noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped ENNReal ProbabilityTheory Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

def nativeRestartMeanBound (E : ℝ) : ℝ :=
  2*(⌈8*E^2⌉₊ : ℝ)/(1-gaussianBlockPass.toReal)

/-- The kernel part of Theorem 4.1, including the sharp bounded-reward rate.
The probability law is for the actual update, not a substitute transition rule. -/
theorem nativeRestart_stationary
    (hX : ∀ k, Measurable (X k)) (hi : iIndepFun X μ)
    (hG : ∀ k, μ.map (X k) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E) :
    ∃ π : Measure ℝ, ∃ α : ℝ≥0∞,
      IsProbabilityMeasure π ∧ 0 < α ∧ α < 1 ∧
      (nativeRestartKernel X μ E).Invariant π ∧
      (∀ ν : Measure ℝ, IsProbabilityMeasure ν →
        (nativeRestartKernel X μ E).Invariant ν → ν = π) ∧
      (∀ ν : Measure ℝ, IsProbabilityMeasure ν → ∀ n : ℕ,
        Doeblin.totalVariation (Doeblin.iterate (nativeRestartKernel X μ E) n ν) π ≤
          (1-α)^(n/2)) ∧
      (∀ ν : Measure ℝ, IsProbabilityMeasure ν → ∀ n : ℕ,
        |(∫ x, nativeRestartMean X μ E x ∂Doeblin.iterate (nativeRestartKernel X μ E) n ν)-
          (∫ x, nativeRestartMean X μ E x ∂π)| ≤
            nativeRestartMeanBound E*(1-α).toReal^(n/2)) ∧
      1 ≤ (∫ x, nativeRestartMean X μ E x ∂π) ∧
        (∫ x, nativeRestartMean X μ E x ∂π) ≤ nativeRestartMeanBound E := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  let : IsMarkovKernel (nativeRestartKernel X μ E) := nativeRestartKernel_isMarkov hX E
  obtain ⟨ν, hν, α, hα, hα1, hminor⟩ := nativeRestartKernel_two_step_common hX (hG 0) hE
  let := hν
  obtain ⟨π, hπprob, hπ, huniq, hmix⟩ :=
    Doeblin.exists_unique_invariant_of_two_step_minorization
      (nativeRestartKernel X μ E) ν hα hα1.le hminor
  let := hπprob
  have hbound := nativeRestartMean_bounds hX hi hG hE
  have hnonneg : ∀ x, 0 ≤ nativeRestartMean X μ E x := fun x => (by norm_num : (0 : ℝ) ≤ 1).trans (hbound x).1
  have hupper : ∀ x, nativeRestartMean X μ E x ≤ nativeRestartMeanBound E := fun x => (hbound x).2
  have hmeas := nativeRestartMean_measurable hX E (μ := μ)
  have hαfin : α ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hα1.le
  let : IsFiniteMeasure (α • ν) := ⟨by simp [Measure.smul_apply, hαfin.lt_top]⟩
  have hmass : (α • ν) univ = α := by simp
  refine ⟨π, α, hπprob, hα, hα1, hπ, huniq, hmix, ?_, ?_, ?_⟩
  · intro ρ hρ n
    let := hρ
    simpa only [hmass] using Doeblin.invariant_reward_bound_two_step
      (nativeRestartKernel X μ E) (α • ν) hminor ρ π hπ hmeas hnonneg hupper n
  · simpa using
      integral_mono (integrable_const (1 : ℝ))
        (Doeblin.integrable_bounded_reward π hmeas hnonneg hupper) (fun x => (hbound x).1)
  · simpa only [measure_univ, ENNReal.toReal_one, mul_one] using
      (Doeblin.integral_bounded_reward π hmeas hnonneg hupper).2

end SwingRepair
