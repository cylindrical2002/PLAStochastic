import PLAStochastic.Swing.StationaryLimit.MarginKernel.LebesgueEquivalence

/-! # `K` is a Markov kernel equivalent to Lebesgue measure

This assembles the two one-step estimates into the statements Theorem 4.3 makes
about the limiting margin kernel itself: it is a probability kernel, each
transition is absolutely continuous with respect to Lebesgue measure, and
conversely Lebesgue measure is absolutely continuous with respect to each
transition.  The second direction uses that the limiting slope is unbounded
above in distribution, so that the half-lines `Iic a` exhaust the line.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-- A property holding almost everywhere is realised on every set of positive measure. -/
theorem exists_mem_of_measure_pos_of_ae {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {P : α → Prop} (hP : ∀ᵐ a ∂ν, P a) {A : Set α} (hA : 0 < ν A) :
    ∃ a ∈ A, P a := by
  by_contra hc
  push Not at hc
  have hnull : ν {a | ¬ P a} = 0 := by
    rw [← ae_iff]
    exact hP
  have hsub : A ⊆ {a | ¬ P a} := fun a ha => hc a ha
  exact absurd (measure_mono_null hsub hnull) hA.ne'

/-- `K` is a probability kernel: the limiting slope is positive almost surely, and
at a positive drift the equilibrium overshoot law is a probability measure. -/
theorem swingMarginKernel_isMarkov [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    IsMarkovKernel (swingMarginKernel X μ) := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  refine ⟨fun r => ⟨?_⟩⟩
  rw [swingMarginKernel_apply hX r MeasurableSet.univ]
  have hae : ∀ᵐ a ∂swingSlopeKernel X μ r, swingOvershootMeasure X μ a univ = 1 := by
    filter_upwards [swingSlopeKernel_positive_ae hX hi hG r] with a ha
    have := swingOvershootMeasure_isProbability hX hi hG ha
    exact measure_univ
  rw [lintegral_congr_ae hae, lintegral_one]
  have : IsMarkovKernel (swingSlopeKernel X μ) := swingSlopeKernel_isMarkov hX
  exact measure_univ

/-- Every transition of `K` has a Lebesgue density. -/
theorem swingMarginKernel_absolutelyContinuous [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (r : ℝ) :
    swingMarginKernel X μ r ≪ volume := by
  refine Measure.AbsolutelyContinuous.mk (fun s hs hzero => ?_)
  rw [swingMarginKernel_apply hX r hs]
  have hzero' : ∀ a : ℝ, swingOvershootMeasure X μ a s = 0 :=
    fun a => swingOvershootMeasure_absolutelyContinuous X μ a hzero
  simp only [hzero']
  exact lintegral_zero

/-- Conversely every transition of `K` dominates Lebesgue measure.  A null
transition forces the target to be Lebesgue-null below arbitrarily large
levels, and those levels exhaust the line. -/
theorem volume_absolutelyContinuous_swingMarginKernel [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (r : ℝ) :
    (volume : Measure ℝ) ≪ swingMarginKernel X μ r := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  refine Measure.AbsolutelyContinuous.mk (fun s hs hzero => ?_)
  rw [swingMarginKernel_apply hX r hs] at hzero
  have hmeasfun : Measurable (fun a : ℝ => swingOvershootMeasure X μ a s) := by
    have := swingOvershootMeasure_measurable (X := X) (μ := μ) hX
    exact Measure.measurable_coe hs |>.comp this
  have hae0 : ∀ᵐ a ∂swingSlopeKernel X μ r, swingOvershootMeasure X μ a s = 0 := by
    have := (lintegral_eq_zero_iff hmeasfun).mp hzero
    rw [Filter.EventuallyEq] at this
    simpa using this
  have hae : ∀ᵐ a ∂swingSlopeKernel X μ r, volume (s ∩ Iic a) = 0 := by
    filter_upwards [hae0, swingSlopeKernel_positive_ae hX hi hG r] with a h0 hpos
    exact volume_inter_Iic_eq_zero_of_swingOvershootMeasure_eq_zero hX hi hG hpos hs h0
  have hslab : ∀ n : ℕ, volume (s ∩ Iic (n : ℝ)) = 0 := by
    intro n
    obtain ⟨a, haI, ha0⟩ := exists_mem_of_measure_pos_of_ae hae
      (swingSlopeKernel_Ioi_pos hX hi hG r (n : ℝ))
    have hsub : s ∩ Iic (n : ℝ) ⊆ s ∩ Iic a :=
      inter_subset_inter_right _ (Iic_subset_Iic.mpr (le_of_lt haI))
    exact measure_mono_null hsub ha0
  have hcover : s = ⋃ n : ℕ, s ∩ Iic (n : ℝ) := by
    ext y
    simp only [mem_iUnion, mem_inter_iff, mem_Iic]
    constructor
    · intro hy
      obtain ⟨n, hn⟩ := exists_nat_ge y
      exact ⟨n, hy, hn⟩
    · rintro ⟨n, hy, -⟩
      exact hy
  rw [hcover]
  exact measure_iUnion_null hslab

end SwingRepair
