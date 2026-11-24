import PLAStochastic.Swing.Transient.Coefficients.Limit

/-! # Slope laws of a margin pair

For a pair `(U, O)` with `U ≥ 0`, the margin `-(U + O)` lies below `-O`. Since the slope kernel
`𝖠` reverses the order of margins against monotone slope tests
(`swingSlopeKernel_integral_antitone_test`), the slope law of `-O` lies below the slope law of
`-(U + O)`:

`Law(-O)𝖠 ≤ Law(-(U + O))𝖠`

against every Lipschitz test monotone on `(0, ∞)`. This is the order used to place the
entrance slope law `α₂ = ρ𝖠` above the boundary row `T(0, ·) = Law(-O)𝖠`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SwingRepair
open LeadingCoefficient KernelLimit SlopeEvaluation

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-- A margin law pushed from a pair law has a first absolute moment. -/
theorem integrable_abs_map_pair {π : Measure (ℝ × ℝ)} {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    (hfi : Integrable f π) : Integrable (fun r : ℝ => |r|) (π.map f) :=
  (integrable_map_measure continuous_abs.aestronglyMeasurable hf.aemeasurable).mpr hfi.abs

/-- Integrals of a test against a slope law are integrals of `r ↦ ∫ g d𝖠(r)` against the
margin law. -/
theorem integral_slopeStationaryLaw_eq [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : Integrable (fun r : ℝ => |r|) ν)
    {L : ℝ≥0} {g : ℝ → ℝ} (hg : IsTest (Ioi 0) L g) :
    Integrable (fun r => ∫ a, g a ∂swingSlopeKernel X μ r) ν ∧
      ∫ a, g a ∂slopeStationaryLaw X μ ν = ∫ r, (∫ a, g a ∂swingSlopeKernel X μ r) ∂ν := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hA : IsMarkovKernel (swingSlopeKernel X μ) := swingSlopeKernel_isMarkov hX
  have : IsProbabilityMeasure (slopeStationaryLaw X μ ν) := slopeStationaryLaw_isProbability hX ν
  have hm := slopeStationaryLaw_first_moment_integrable hX hi hG hν
  have hS : slopeStationaryLaw X μ ν (Ioi 0)ᶜ = 0 := by
    rw [compl_Ioi]; exact slopeStationaryLaw_Iic_zero hX hi hG ν
  have hgi : Integrable g (slopeStationaryLaw X μ ν) :=
    hg.integrable_of_moment hS hm (a₀ := 1) (mem_Ioi.mpr one_pos)
  refine ⟨?_, integral_comp_eq hgi⟩
  have hgi' := hgi
  rw [slopeStationaryLaw, Measure.comp_eq_comp_const_apply] at hgi'
  simpa only [Kernel.const_apply] using hgi'.integral_comp

/-- **Pair order.**  If `U ≥ 0` almost surely under a pair law `π` with integrable coordinates,
then `Law(-O)𝖠 ≤ Law(-(U + O))𝖠` against monotone slope tests. -/
theorem slopeTestLE_slopeStationaryLaw_pair [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {π : Measure (ℝ × ℝ)} [IsProbabilityMeasure π] (hπ : ∀ᵐ p ∂π, 0 ≤ p.1)
    (h₁ : Integrable (fun p : ℝ × ℝ => p.1) π) (h₂ : Integrable (fun p : ℝ × ℝ => p.2) π) :
    SlopeTestLE (slopeStationaryLaw X μ (π.map fun p => -p.2))
      (slopeStationaryLaw X μ (π.map fun p => -(p.1 + p.2))) := by
  have hm₁ : Measurable fun p : ℝ × ℝ => -p.2 := measurable_snd.neg
  have hm₂ : Measurable fun p : ℝ × ℝ => -(p.1 + p.2) := (measurable_fst.add measurable_snd).neg
  have : IsProbabilityMeasure (π.map fun p => -p.2) :=
    Measure.isProbabilityMeasure_map hm₁.aemeasurable
  have : IsProbabilityMeasure (π.map fun p => -(p.1 + p.2)) :=
    Measure.isProbabilityMeasure_map hm₂.aemeasurable
  have ha₁ := integrable_abs_map_pair hm₁ h₂.neg
  have ha₂ := integrable_abs_map_pair hm₂ (h₁.add h₂).neg
  intro L g hg hmono
  obtain ⟨hφ₁, e₁⟩ := integral_slopeStationaryLaw_eq hX hi hG ha₁ hg
  obtain ⟨hφ₂, e₂⟩ := integral_slopeStationaryLaw_eq hX hi hG ha₂ hg
  have hanti := swingSlopeKernel_integral_antitone_test hX hi hG hg hmono
  set φ : ℝ → ℝ := fun r => ∫ a, g a ∂swingSlopeKernel X μ r
  rw [e₁, e₂, integral_map hm₁.aemeasurable hφ₁.aestronglyMeasurable,
    integral_map hm₂.aemeasurable hφ₂.aestronglyMeasurable]
  refine integral_mono_ae
    ((integrable_map_measure hφ₁.aestronglyMeasurable hm₁.aemeasurable).mp hφ₁)
    ((integrable_map_measure hφ₂.aestronglyMeasurable hm₂.aemeasurable).mp hφ₂) ?_
  filter_upwards [hπ] with p hp
  exact hanti (by linarith)

end SwingRepair
