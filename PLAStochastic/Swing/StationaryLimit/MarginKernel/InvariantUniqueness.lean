import PLAStochastic.Swing.StationaryLimit.MarginKernel.MarkovProperties
import PLAStochastic.ForMathlib.Probability.Kernel.Invariant.UniqueOfCommonMeasure

/-! # Theorem 4.3: the invariant law of `K`

Everything the paper asserts about the limiting margin kernel itself is proved
here: it has at most one invariant probability, and any invariant probability is
absolutely continuous with respect to Lebesgue measure and equivalent to it.
Existence is not proved here; the paper obtains it as the limit of the invariant
laws `ν_E`, which needs the uniform renewal expansion.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-- An invariant law of `K` has a Lebesgue density. -/
theorem swingMarginKernel_invariant_absolutelyContinuous [SFinite μ]
    (hX : ∀ n, Measurable (X n)) {ν : Measure ℝ}
    (hν : (swingMarginKernel X μ).Invariant ν) :
    ν ≪ volume := by
  refine Measure.AbsolutelyContinuous.mk (fun A hA hzero => ?_)
  have hbind : ν A = ∫⁻ x, swingMarginKernel X μ x A ∂ν := by
    conv_lhs => rw [← hν.def]
    rw [Measure.bind_apply hA (Kernel.aemeasurable _)]
  have hpoint : ∀ x : ℝ, swingMarginKernel X μ x A = 0 :=
    fun x => swingMarginKernel_absolutelyContinuous hX x hzero
  rw [hbind]
  simp only [hpoint]
  exact lintegral_zero

/-- An invariant law of `K` is equivalent to Lebesgue measure. -/
theorem volume_absolutelyContinuous_swingMarginKernel_invariant [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {ν : Measure ℝ} (hne : ν ≠ 0)
    (hν : (swingMarginKernel X μ).Invariant ν) :
    (volume : Measure ℝ) ≪ ν := by
  refine Measure.AbsolutelyContinuous.mk (fun A hA hzero => ?_)
  have hbind : ν A = ∫⁻ x, swingMarginKernel X μ x A ∂ν := by
    conv_lhs => rw [← hν.def]
    rw [Measure.bind_apply hA (Kernel.aemeasurable _)]
  rw [hzero] at hbind
  have hmeas : Measurable (fun x : ℝ => swingMarginKernel X μ x A) :=
    Kernel.measurable_coe _ hA
  have hae : ∀ᵐ x ∂ν, swingMarginKernel X μ x A = 0 := by
    have := (lintegral_eq_zero_iff hmeas).mp hbind.symm
    rw [Filter.EventuallyEq] at this
    simpa using this
  have : (ae ν).NeBot := ae_neBot.mpr hne
  obtain ⟨x, hx⟩ := hae.exists
  exact volume_absolutelyContinuous_swingMarginKernel hX hi hG x hx

/-- Theorem 4.3, first sentence apart from existence: `K` has at most one
invariant probability measure. -/
theorem swingMarginKernel_invariant_unique [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {ν₁ ν₂ : Measure ℝ} [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (h₁ : (swingMarginKernel X μ).Invariant ν₁)
    (h₂ : (swingMarginKernel X μ).Invariant ν₂) :
    ν₁ = ν₂ := by
  have hmk : IsMarkovKernel (swingMarginKernel X μ) := swingMarginKernel_isMarkov hX hi hG
  have hvol : (volume : Measure ℝ) ≠ 0 := by
    intro hc
    have : (volume : Measure ℝ) (Ioo (0 : ℝ) 1) = 0 := by rw [hc]; rfl
    rw [Real.volume_Ioo] at this
    simp at this
  exact KernelUnique.invariant_subsingleton hvol
    (fun x => volume_absolutelyContinuous_swingMarginKernel hX hi hG x) h₁ h₂

/-- The packaged statement: at most one invariant probability, and any invariant
probability is equivalent to Lebesgue measure. -/
theorem theorem_4_3_limiting_kernel [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    IsMarkovKernel (swingMarginKernel X μ) ∧
      (∀ r : ℝ, swingMarginKernel X μ r ≪ volume ∧
        (volume : Measure ℝ) ≪ swingMarginKernel X μ r) ∧
      (∀ ν : Measure ℝ, IsProbabilityMeasure ν →
        (swingMarginKernel X μ).Invariant ν → ν ≪ volume ∧ (volume : Measure ℝ) ≪ ν) ∧
      (∀ ν₁ ν₂ : Measure ℝ, IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ →
        (swingMarginKernel X μ).Invariant ν₁ → (swingMarginKernel X μ).Invariant ν₂ →
          ν₁ = ν₂) := by
  refine ⟨swingMarginKernel_isMarkov hX hi hG, fun r => ⟨?_, ?_⟩, ?_, ?_⟩
  · exact swingMarginKernel_absolutelyContinuous hX r
  · exact volume_absolutelyContinuous_swingMarginKernel hX hi hG r
  · intro ν hp hν
    let : IsProbabilityMeasure ν := hp
    refine ⟨swingMarginKernel_invariant_absolutelyContinuous hX hν, ?_⟩
    refine volume_absolutelyContinuous_swingMarginKernel_invariant hX hi hG ?_ hν
    intro hc
    have := hp.measure_univ
    rw [hc] at this
    simp at this
  · intro ν₁ ν₂ hp₁ hp₂ h₁ h₂
    let : IsProbabilityMeasure ν₁ := hp₁
    let : IsProbabilityMeasure ν₂ := hp₂
    exact swingMarginKernel_invariant_unique hX hi hG h₁ h₂

end SwingRepair
