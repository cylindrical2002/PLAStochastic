import PLAStochastic.Swing.Transient.Brackets.SmallDriftLadder
import PLAStochastic.Swing.ConstantEvaluation.GaussianEvaluation

/-! # The zero-drift row `𝖡(0)`, `T(0, ·)`

At drift `0` the library objects are still defined:
`𝖡(0) = Law(-O_0)` with `O_0` the equilibrium residual of the zero-drift strict
ladder height `H_0`, and `T(0, ·) = 𝖡(0)𝖠`.  This file proves their basic
properties directly from `𝔼H_0 = 1/√2` and `𝔼H_0² < ∞`:

* `equilibriumOvershootLaw_zero_integrable_id`, `swingOvershootMeasure_zero_isProbability`,
  `swingOvershootMeasure_zero_integrable_id`: `O_0` has a first moment and `𝖡(0)` is a
  probability measure with a first moment;
* `swingSlopeChainKernel_zero_isProbability`, `swingSlopeChainKernel_zero_compl`,
  `swingSlopeChainKernel_zero_integrable_id`: `T(0, ·)` is a probability measure on
  `(0, ∞)` with a first moment;
* `swingSlopeChainKernel_zero_integrable_test`: every Lipschitz test function on `(0, ∞)`
  is `T(0, ·)`-integrable.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SwingRepair
open SlopeEvaluation
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-- The ladder mean of the ladder law is the `ℝ≥0∞` mean of the ladder height. -/
theorem ladderMeanENN_gaussianAscendingLadderLaw (hX : ∀ n, Measurable (X n)) (a : ℝ) :
    ladderMeanENN (gaussianAscendingLadderLaw X μ a) = ladderMeanLIntegral X μ a := by
  rw [ladderMeanENN, gaussianAscendingLadderLaw,
    lintegral_map ENNReal.measurable_ofReal (gaussianAscendingLadderHeight_measurable hX a)]
  rfl

theorem ladderMeanLIntegral_zero_ne_zero (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    ladderMeanLIntegral X μ 0 ≠ 0 := by
  rw [ladderMeanLIntegral_zero hX hi hG]
  exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'

theorem ladderMeanLIntegral_zero_ne_top (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    ladderMeanLIntegral X μ 0 ≠ ⊤ := by
  rw [ladderMeanLIntegral_zero hX hi hG]
  exact ENNReal.ofReal_ne_top

/-- The zero-drift equilibrium overshoot law `O_0` is a probability measure. -/
theorem equilibriumOvershootLaw_zero_isProbability (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    IsProbabilityMeasure (equilibriumOvershootLaw (gaussianAscendingLadderLaw X μ 0)) := by
  have := gaussianAscendingLadderLaw_isProbabilityMeasure hX hi 0
  refine equilibriumOvershootLaw_isProbabilityMeasure _ (gaussianAscendingLadderLaw_nonneg_ae hX 0)
    ?_ ?_
  · rw [ladderMeanENN_gaussianAscendingLadderLaw hX]
    exact ladderMeanLIntegral_zero_ne_zero hX hi hG
  · rw [ladderMeanENN_gaussianAscendingLadderLaw hX]
    exact ladderMeanLIntegral_zero_ne_top hX hi hG

/-- **`𝖡(0)` is a probability measure.** -/
theorem swingOvershootMeasure_zero_isProbability (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    IsProbabilityMeasure (swingOvershootMeasure X μ 0) := by
  have := equilibriumOvershootLaw_zero_isProbability hX hi hG
  exact Measure.isProbabilityMeasure_map (measurable_const_sub_self 0).aemeasurable

/-- `𝔼O_0 = 𝔼H_0² / (2𝔼H_0) < ∞`. -/
theorem lintegral_equilibriumOvershootLaw_zero_id_lt_top (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    (∫⁻ o, ENNReal.ofReal o ∂equilibriumOvershootLaw (gaussianAscendingLadderLaw X μ 0)) < ⊤ := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  set ν := gaussianAscendingLadderLaw X μ 0 with hν
  have hνp : IsProbabilityMeasure ν := gaussianAscendingLadderLaw_isProbabilityMeasure hX hi 0
  have hmeas := gaussianAscendingLadderHeight_measurable hX 0
  rw [lintegral_equilibriumOvershootLaw_id ν (gaussianAscendingLadderLaw_nonneg_ae hX 0)]
  refine ENNReal.mul_lt_top ?_ ?_
  · rw [hν, ladderMeanENN_gaussianAscendingLadderLaw hX]
    exact ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr (ladderMeanLIntegral_zero_ne_zero hX hi hG))
  · have hsq := gaussianAscendingLadderHeight_sq_integrable_of_le hX hi hG (a := 0) (by norm_num)
    rw [hν, gaussianAscendingLadderLaw,
      lintegral_map (f := fun x : ℝ => ENNReal.ofReal (x ^ 2 / 2))
        (ENNReal.measurable_ofReal.comp ((measurable_id.pow_const 2).div_const 2)) hmeas]
    exact (hsq.div_const 2).lintegral_lt_top

/-- The zero-drift equilibrium overshoot `O_0` has a first moment. -/
theorem equilibriumOvershootLaw_zero_integrable_id (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    Integrable (fun o : ℝ => o) (equilibriumOvershootLaw (gaussianAscendingLadderLaw X μ 0)) := by
  have hnn : ∀ᵐ o ∂equilibriumOvershootLaw (gaussianAscendingLadderLaw X μ 0), 0 ≤ o := by
    rw [ae_iff]
    convert equilibriumOvershootLaw_Iio_zero (gaussianAscendingLadderLaw X μ 0) using 2
    ext o
    simp [not_le]
  refine ⟨aestronglyMeasurable_id, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal hnn]
  exact lintegral_equilibriumOvershootLaw_zero_id_lt_top hX hi hG

/-- **`𝖡(0)` has a first moment.** -/
theorem swingOvershootMeasure_zero_integrable_id (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    Integrable (fun r : ℝ => r) (swingOvershootMeasure X μ 0) := by
  have := equilibriumOvershootLaw_zero_isProbability hX hi hG
  rw [swingOvershootMeasure]
  refine (integrable_map_measure (g := fun r : ℝ => r) aestronglyMeasurable_id
    (measurable_const_sub_self 0).aemeasurable).mpr ?_
  exact (integrable_const 0).sub (equilibriumOvershootLaw_zero_integrable_id hX hi hG)

/-! ### The row `T(0, ·)` -/

/-- **`T(0, ·)` is a probability measure.** -/
theorem swingSlopeChainKernel_zero_isProbability [SFinite μ] (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    IsProbabilityMeasure (swingSlopeChainKernel X μ 0) := by
  have : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have := swingOvershootMeasure_zero_isProbability hX hi hG
  have hA := swingSlopeKernel_isMarkov (μ := μ) hX
  refine ⟨?_⟩
  rw [swingSlopeChainKernel_apply hX 0, Measure.comp_apply_univ]
  exact measure_univ

/-- **`T(0, ·)` is carried by `(0, ∞)`.** -/
theorem swingSlopeChainKernel_zero_compl [SFinite μ] (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    swingSlopeChainKernel X μ 0 (Ioi 0)ᶜ = 0 := by
  rw [compl_Ioi]
  exact swingSlopeChainKernel_Iic_zero hX hi hG 0

/-- **`T(0, ·)` has a first moment.** -/
theorem swingSlopeChainKernel_zero_integrable_id [SFinite μ] (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    Integrable (fun b : ℝ => b) (swingSlopeChainKernel X μ 0) := by
  have := swingOvershootMeasure_zero_isProbability hX hi hG
  rw [swingSlopeChainKernel_apply hX 0]
  exact slopeStationaryLaw_first_moment_integrable hX hi hG (ν := swingOvershootMeasure X μ 0)
    (swingOvershootMeasure_zero_integrable_id hX hi hG).abs

/-- Every Lipschitz test function on `(0, ∞)` is integrable under `T(0, ·)`. -/
theorem swingSlopeChainKernel_zero_integrable_test [SFinite μ] (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {L : ℝ≥0} {f : ℝ → ℝ} (hf : IsTest (Ioi 0) L f) :
    Integrable f (swingSlopeChainKernel X μ 0) := by
  have := swingSlopeChainKernel_zero_isProbability hX hi hG
  exact hf.integrable_of_moment (swingSlopeChainKernel_zero_compl hX hi hG)
    (swingSlopeChainKernel_zero_integrable_id hX hi hG) (a₀ := 1) (mem_Ioi.mpr one_pos)

end SwingRepair
