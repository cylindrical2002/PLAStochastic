import PLAStochastic.Swing.StationaryLimit.Slope.Limiting
import Mathlib.Probability.Kernel.Composition.Prod

/-! # The actual margin-to-slope probability kernel

This is the first stage of the limiting Swing kernel.  Its continuity estimate
comes from coupling all incoming margins with the same original Gaussian walk.
The equilibrium-overshoot second stage is not assumed here.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

def swingSlopeKernel (X : ℕ → Ω → ℝ) (μ : Measure Ω) : Kernel ℝ ℝ :=
  (Kernel.id ×ₖ Kernel.const ℝ μ).map (fun p : ℝ × Ω => swingLimitingSlope X p.1 p.2)

theorem swingSlopeKernel_apply [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (r : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    swingSlopeKernel X μ r A = μ {ω | swingLimitingSlope X r ω ∈ A} := by
  rw [swingSlopeKernel, Kernel.map_apply' _ (swingLimitingSlope_joint_measurable hX) _ hA,
    Kernel.id_prod_apply' _ _ ((swingLimitingSlope_joint_measurable hX) hA)]
  rfl

theorem swingSlopeKernel_eq_law [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (r : ℝ) :
    swingSlopeKernel X μ r = swingLimitingSlopeLaw X μ r := by
  ext A hA
  rw [swingSlopeKernel_apply hX r hA, swingLimitingSlopeLaw,
    Measure.map_apply (swingLimitingSlope_measurable hX r) hA]
  rfl

theorem swingSlopeKernel_isMarkov [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) : IsMarkovKernel (swingSlopeKernel X μ) :=
  Kernel.IsMarkovKernel.map _ (swingLimitingSlope_joint_measurable hX)

theorem swingSlopeKernel_positive_ae
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (r : ℝ) :
    ∀ᵐ a ∂swingSlopeKernel X μ r, 0 < a := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  rw [swingSlopeKernel_eq_law hX r, swingLimitingSlopeLaw,
    ae_map_iff (swingLimitingSlope_measurable hX r).aemeasurable measurableSet_Ioi]
  exact swingLimitingSlope_pos_ae hX hi hG r

theorem swingSlopeKernel_integral [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (r : ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    (∫ a, f a ∂swingSlopeKernel X μ r) =
      ∫ ω, f (swingLimitingSlope X r ω) ∂μ := by
  rw [swingSlopeKernel_eq_law hX r, swingLimitingSlopeLaw]
  exact integral_map (swingLimitingSlope_measurable hX r).aemeasurable hf.aestronglyMeasurable

/-- Lipschitz test integrals of the actual first-stage kernel are Lipschitz in
the incoming margin, with the same constant. -/
theorem swingSlopeKernel_lipschitz_test
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (hint : ∀ r, Integrable (fun ω => f (swingLimitingSlope X r ω)) μ) :
    LipschitzWith L (fun r => ∫ a, f a ∂swingSlopeKernel X μ r) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  apply LipschitzWith.of_dist_le_mul
  intro r c
  rw [swingSlopeKernel_integral hX r hf.continuous.measurable,
    swingSlopeKernel_integral hX c hf.continuous.measurable]
  simpa only [Real.dist_eq] using
    swingLimitingSlope_integral_test_bound hX hi hG hf r c (hint r) (hint c)

end SwingRepair
