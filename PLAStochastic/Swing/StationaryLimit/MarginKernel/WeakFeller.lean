import PLAStochastic.Swing.Ladder.Drift.EquilibriumContinuity
import PLAStochastic.Swing.StationaryLimit.MarginKernel.MarkovProperties
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! # `K` is weakly Feller

The invariant-law passage of `app:limit` needs `Kf` to be continuous for every
bounded Lipschitz `f`.  Writing `Kf(r)` as the expectation of the second-stage
reward at the random slope `A_r`, this follows from the pathwise continuity of
`r ↦ A_r`, the almost sure positivity of `A_r`, and the drift continuity of the
equilibrium overshoot.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-! ### The overshoot kernel is a finite kernel -/

theorem equilibriumOvershootLaw_univ_le_one (ν : Measure ℝ) [SFinite ν]
    (hnn : 0 ≤ᵐ[ν] fun x : ℝ => x) : equilibriumOvershootLaw ν univ ≤ 1 := by
  have hmassform : equilibriumOvershootLaw ν univ =
      ∫⁻ o in Ici (0 : ℝ), ν (Ioi o) / ladderMeanENN ν := by
    rw [equilibriumOvershootLaw, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_restrict MeasurableSet.univ, univ_inter]
  have hIci : (volume.restrict (Ici (0 : ℝ))) = volume.restrict (Ioi (0 : ℝ)) :=
    Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ))).symm
  rcases eq_or_ne (ladderMeanENN ν) 0 with h0 | h0
  · have hlc := ladderMeanENN_eq_lintegral_tail ν hnn
    rw [h0] at hlc
    have hae : (fun o : ℝ => ν (Ioi o)) =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 :=
      (lintegral_eq_zero_iff (measurable_ladderTail ν)).mp hlc.symm
    have hzero : (∫⁻ o in Ici (0 : ℝ), ν (Ioi o) / ladderMeanENN ν) = 0 := by
      rw [hIci]
      refine (lintegral_eq_zero_iff ?_).mpr ?_
      · exact (measurable_ladderTail ν).div measurable_const
      · filter_upwards [hae] with o ho
        have ho' : ν (Ioi o) = 0 := ho
        rw [ho']
        simp
    rw [hmassform, hzero]
    exact zero_le_one
  · rcases eq_or_ne (ladderMeanENN ν) ⊤ with htop | htop
    · have hzero : (∫⁻ o in Ici (0 : ℝ), ν (Ioi o) / ladderMeanENN ν) = 0 := by
        refine (lintegral_eq_zero_iff ?_).mpr ?_
        · exact (measurable_ladderTail ν).div measurable_const
        · filter_upwards with o
          rw [htop, ENNReal.div_top]
          rfl
      rw [hmassform, hzero]
      exact zero_le_one
    · have := equilibriumOvershootLaw_isProbabilityMeasure ν hnn h0 htop
      rw [measure_univ]

theorem swingOvershootMeasure_univ_le_one (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (a : ℝ) : swingOvershootMeasure X μ a univ ≤ 1 := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hlprob := gaussianAscendingLadderLaw_isProbabilityMeasure hX hi a
  rw [swingOvershootMeasure, Measure.map_apply (measurable_const_sub_self a)
    MeasurableSet.univ, preimage_univ]
  exact equilibriumOvershootLaw_univ_le_one _ (gaussianAscendingLadderLaw_nonneg_ae hX a)

theorem swingOvershootKernel_isFinite [SFinite μ] (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) : IsFiniteKernel (swingOvershootKernel X μ) := by
  refine ⟨1, by norm_num, fun a => ?_⟩
  rw [swingOvershootKernel_apply hX a]
  exact swingOvershootMeasure_univ_le_one hX hi a

/-- The second-stage reward: the test function integrated against the reflected
equilibrium overshoot at drift `a`. -/
def swingOvershootReward (X : ℕ → Ω → ℝ) (μ : Measure Ω) (f : ℝ → ℝ) (a : ℝ) : ℝ :=
  ∫ y, f y ∂(swingOvershootMeasure X μ a)

theorem swingOvershootReward_measurable [SFinite μ] (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (swingOvershootReward X μ f) := by
  have : IsFiniteKernel (swingOvershootKernel X μ) := swingOvershootKernel_isFinite hX hi
  have hsm : StronglyMeasurable (fun p : ℝ × ℝ => f p.2) :=
    (hf.comp measurable_snd).stronglyMeasurable
  have h := (hsm.integral_kernel_prod_right' (κ := swingOvershootKernel X μ)).measurable
  have heq : (fun a : ℝ => ∫ y, f y ∂((swingOvershootKernel X μ) a)) =
      swingOvershootReward X μ f := by
    funext a
    show (∫ y, f y ∂((swingOvershootKernel X μ) a)) =
      ∫ y, f y ∂(swingOvershootMeasure X μ a)
    rw [swingOvershootKernel_apply hX a]
  rw [← heq]
  exact h

theorem integrable_of_bounded {ν : Measure ℝ} [IsProbabilityMeasure ν] {f : ℝ → ℝ} {B : ℝ}
    (hf : Measurable f) (hfB : ∀ x, |f x| ≤ B) : Integrable f ν := by
  refine Integrable.mono' (integrable_const B) hf.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs]
  exact hfB x

theorem abs_swingOvershootReward_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a)
    {f : ℝ → ℝ} {B : ℝ} (hf : Measurable f) (hfB : ∀ x, |f x| ≤ B) :
    |swingOvershootReward X μ f a| ≤ B := by
  have hp : IsProbabilityMeasure (swingOvershootMeasure X μ a) :=
    swingOvershootMeasure_isProbability hX hi hG ha
  have hint : Integrable f (swingOvershootMeasure X μ a) := integrable_of_bounded hf hfB
  show |∫ y, f y ∂(swingOvershootMeasure X μ a)| ≤ B
  calc |∫ y, f y ∂(swingOvershootMeasure X μ a)| ≤ ∫ y, |f y| ∂(swingOvershootMeasure X μ a) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _y, B ∂(swingOvershootMeasure X μ a) :=
        integral_mono hint.abs (integrable_const B) hfB
    _ = B := by simp

/-- `Kf(r)` is the expectation of the second-stage reward at the random slope. -/
theorem swingMarginKernel_integral_eq [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (r : ℝ)
    {f : ℝ → ℝ} {B : ℝ} (hf : Measurable f) (hfB : ∀ x, |f x| ≤ B) :
    (∫ y, f y ∂(swingMarginKernel X μ r)) =
      ∫ ω, swingOvershootReward X μ f (swingLimitingSlope X r ω) ∂μ := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hmk : IsMarkovKernel (swingMarginKernel X μ) := swingMarginKernel_isMarkov hX hi hG
  have hpr : IsProbabilityMeasure (swingMarginKernel X μ r) :=
    IsMarkovKernel.isProbabilityMeasure r
  have hint : Integrable f (swingMarginKernel X μ r) := integrable_of_bounded hf hfB
  have hcomp : (∫ y, f y ∂(swingMarginKernel X μ r)) =
      ∫ a, (∫ y, f y ∂((swingOvershootKernel X μ) a)) ∂(swingSlopeKernel X μ r) :=
    ProbabilityTheory.Kernel.integral_comp
      (κ := swingSlopeKernel X μ) (η := swingOvershootKernel X μ) (a := r) hint
  rw [hcomp]
  have hcongr : (∫ a, (∫ y, f y ∂((swingOvershootKernel X μ) a)) ∂(swingSlopeKernel X μ r)) =
      ∫ a, swingOvershootReward X μ f a ∂(swingSlopeKernel X μ r) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    show (∫ y, f y ∂((swingOvershootKernel X μ) a)) =
      ∫ y, f y ∂(swingOvershootMeasure X μ a)
    rw [swingOvershootKernel_apply hX a]
  rw [hcongr]
  exact swingSlopeKernel_integral hX r (swingOvershootReward_measurable hX hi hf)

/-- The second-stage reward is continuous at every positive drift. -/
theorem swingOvershootReward_continuousAt [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a)
    {f : ℝ → ℝ} {L B : ℝ} (hf : Measurable f)
    (hlip : ∀ x y : ℝ, |f x - f y| ≤ L*|x - y|) (hfB : ∀ x, |f x| ≤ B) :
    ContinuousAt (swingOvershootReward X μ f) a :=
  swingOvershootMeasure_integral_tendsto hX hi hG ha hf hlip hfB

/-- Weak Feller property: `Kf` is continuous for every bounded Lipschitz `f`. -/
theorem swingMarginKernel_integral_continuous [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {f : ℝ → ℝ} {L B : ℝ} (hf : Measurable f)
    (hlip : ∀ x y : ℝ, |f x - f y| ≤ L*|x - y|) (hfB : ∀ x, |f x| ≤ B) :
    Continuous (fun r : ℝ => ∫ y, f y ∂(swingMarginKernel X μ r)) := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hΨmeas := swingOvershootReward_measurable (X := X) (μ := μ) hX hi hf
  have hrep : ∀ r : ℝ, (∫ y, f y ∂(swingMarginKernel X μ r)) =
      ∫ ω, swingOvershootReward X μ f (swingLimitingSlope X r ω) ∂μ :=
    fun r => swingMarginKernel_integral_eq hX hi hG r hf hfB
  rw [continuous_iff_continuousAt]
  intro r
  rw [ContinuousAt]
  simp_rw [hrep]
  refine tendsto_integral_filter_of_dominated_convergence (bound := fun _ : Ω => B) ?_ ?_ ?_ ?_
  · filter_upwards with r'
    exact (hΨmeas.comp (swingLimitingSlope_measurable hX r')).aestronglyMeasurable
  · filter_upwards with r'
    filter_upwards [swingLimitingSlope_all_margins_ae hX hi hG] with ω hω
    rw [Real.norm_eq_abs]
    exact abs_swingOvershootReward_le hX hi hG (hω.1 r') hf hfB
  · exact integrable_const B
  · filter_upwards [swingLimitingSlope_all_margins_ae hX hi hG] with ω hω
    have hcont : Tendsto (fun r' : ℝ => swingLimitingSlope X r' ω) (𝓝 r)
        (𝓝 (swingLimitingSlope X r ω)) :=
      (hω.2.1.continuous.continuousAt : ContinuousAt _ r)
    have hΨ := swingOvershootReward_continuousAt hX hi hG (hω.1 r) hf hlip hfB
    exact hΨ.tendsto.comp hcont

end SwingRepair
