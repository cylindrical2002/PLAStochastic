import PLAStochastic.ForMathlib.Probability.Kernel.Doeblin.TwoStep
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Geometric convergence of bounded nonnegative rewards

The common measure cancels from the two expectations.  Each residual has mass
q^n and a reward in [0,H], so the sharp probability-convention factor is H.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal ProbabilityTheory Topology
namespace SwingRepair.Doeblin
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {S : Type*} [MeasurableSpace S]

theorem integrable_bounded_reward (μ : Measure S) [IsFiniteMeasure μ]
    {f : S → ℝ} (hf : Measurable f) {H : ℝ} (hfn : ∀ x, 0 ≤ f x)
    (hfH : ∀ x, f x ≤ H) : Integrable f μ := by
  apply (integrable_const H).mono' hf.aestronglyMeasurable
  exact ae_of_all _ fun x => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hfn x)] using hfH x

theorem integral_bounded_reward (μ : Measure S) [IsFiniteMeasure μ]
    {f : S → ℝ} (hf : Measurable f) {H : ℝ} (hfn : ∀ x, 0 ≤ f x)
    (hfH : ∀ x, f x ≤ H) :
    0 ≤ ∫ x, f x ∂μ ∧ (∫ x, f x ∂μ) ≤ H*(μ univ).toReal := by
  refine ⟨integral_nonneg hfn, ?_⟩
  simpa only [integral_const, smul_eq_mul, measureReal_def, mul_comm] using
    integral_mono (integrable_bounded_reward μ hf hfn hfH) (integrable_const H) hfH

theorem iterate_reward_bound (P : Kernel S S) [IsMarkovKernel P]
    (β : Measure S) [IsFiniteMeasure β] (hminor : ∀ x, β ≤ P x)
    (μ η : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    {f : S → ℝ} (hf : Measurable f) {H : ℝ} (hfn : ∀ x, 0 ≤ f x)
    (hfH : ∀ x, f x ≤ H) (n : ℕ) :
    |(∫ x, f x ∂iterate P n μ)-(∫ x, f x ∂iterate P n η)| ≤
      H*(1-β univ).toReal^n := by
  obtain ⟨C, hCμ, hCη⟩ := iterate_common_part P β hminor μ η n
  let R := residual P β hminor
  have hmμ : iterate R n μ univ = (1-β univ)^n := by
    simp only [iterate_mass R (residual_mass P β hminor), measure_univ, mul_one]
  have hmη : iterate R n η univ = (1-β univ)^n := by
    simp only [iterate_mass R (residual_mass P β hminor), measure_univ, mul_one]
  have hq : (1-β univ)^n < ⊤ :=
    (ENNReal.pow_ne_top (ENNReal.sub_ne_top ENNReal.one_ne_top)).lt_top
  let : IsFiniteMeasure (iterate R n μ) := ⟨by rwa [hmμ]⟩
  let : IsFiniteMeasure (iterate R n η) := ⟨by rwa [hmη]⟩
  let : IsFiniteMeasure C := isFiniteMeasure_of_le (iterate P n μ) (by
    rw [hCμ]
    apply Measure.le_iff.mpr
    intro s _
    rw [Measure.add_apply]
    exact le_add_right le_rfl)
  have hfC := integrable_bounded_reward C hf hfn hfH
  have hfμ := integrable_bounded_reward (iterate R n μ) hf hfn hfH
  have hfη := integrable_bounded_reward (iterate R n η) hf hfn hfH
  have hbμ := integral_bounded_reward (iterate R n μ) hf hfn hfH
  have hbη := integral_bounded_reward (iterate R n η) hf hfn hfH
  rw [hmμ, ENNReal.toReal_pow] at hbμ
  rw [hmη, ENNReal.toReal_pow] at hbη
  rw [hCμ, hCη, integral_add_measure hfC hfμ, integral_add_measure hfC hfη, abs_le]
  constructor <;> linarith [hbμ.1, hbμ.2, hbη.1, hbη.2]

theorem invariant_reward_bound_two_step (P : Kernel S S) [IsMarkovKernel P]
    (β : Measure S) [IsFiniteMeasure β] (hminor : ∀ x, β ≤ (P ∘ₖ P) x)
    (μ π : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hπ : P.Invariant π) {f : S → ℝ} (hf : Measurable f) {H : ℝ}
    (hfn : ∀ x, 0 ≤ f x) (hfH : ∀ x, f x ≤ H) (n : ℕ) :
    |(∫ x, f x ∂iterate P n μ)-(∫ x, f x ∂π)| ≤ H*(1-β univ).toReal^(n/2) := by
  have hh := iterate_reward_bound (P ∘ₖ P) β hminor (iterate P (n%2) μ) π
    hf hfn hfH (n/2)
  rw [iterate_of_invariant _ π (hπ.comp hπ)] at hh
  rwa [← iterate_two_step_remainder] at hh

end SwingRepair.Doeblin
