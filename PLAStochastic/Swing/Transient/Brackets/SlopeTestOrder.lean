import PLAStochastic.Swing.Transient.Brackets.BoundaryOrder
import PLAStochastic.Swing.Transient.SlopeAlgebra

/-! # The test-function order on slope laws

`SlopeTestLE ν ν'` says `∫ g dν ≤ ∫ g dν'` for every measurable test function `g` that is
Lipschitz and monotone on `(0, ∞)`; on laws carried by `(0, ∞)` this is the stochastic
order tested by the class of functions the slope chain `T` preserves.

For a slope law `ν` (a probability measure on `(0, ∞)` with a first moment):

* `integral_comp_eq_act`: `∫ g d(νT) = ∫ Tg dν` for every Lipschitz test `g`
  (abstract, for any contraction);
* `slopeTestLE_comp_zero`: `νT ≤ T(0, ·)` — average the boundary order
  `T(a, ·) ≤ T(0, ·)` over `a ∼ ν`;
* `SlopeTestLE.comp_comp`: `T²` preserves the order, because `T²g` is again a monotone
  Lipschitz test (`T` reverses order twice);
* `slopeTestLE_mixture`: if `T(0, ·) ≤ νᵢ` then `T(0, ·) ≤ θν₁ + (1 - θ)ν₂`,
  and the mixture is again a slope law.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

namespace SlopeEvaluation

variable {T : Kernel ℝ ℝ} {S : Set ℝ} {q : ℝ≥0}

/-- The norm of a test function is a test function with the same constant. -/
theorem IsTest.norm {L : ℝ≥0} {f : ℝ → ℝ} (hf : IsTest S L f) :
    IsTest S L (fun x => ‖f x‖) :=
  ⟨hf.meas.norm, by
    have h := lipschitzWith_one_norm.comp_lipschitzOnWith hf.lip
    rw [one_mul] at h
    exact h⟩

/-- A transition from a law concentrated on `S` is a probability measure. -/
theorem comp_isProbability (h : Contraction T S q) {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hνS : ν Sᶜ = 0) : IsProbabilityMeasure (T ∘ₘ ν) := by
  constructor
  rw [Measure.bind_apply MeasurableSet.univ (Kernel.aemeasurable _)]
  have hae : (fun a => T a univ) =ᵐ[ν] fun _ => (1 : ℝ≥0∞) := by
    filter_upwards [ae_mem_of_compl_eq_zero hνS] with a ha
    have := h.prob a ha
    exact measure_univ
  rw [lintegral_congr_ae hae, lintegral_const, measure_univ, one_mul]

/-- Lipschitz tests are integrable after one transition from a law on `S` with a
first moment. -/
theorem IsTest.integrable_comp [IsSFiniteKernel T] (h : Contraction T S q)
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hνS : ν Sᶜ = 0)
    (hνm : Integrable (fun a : ℝ => a) ν) {L : ℝ≥0} {f : ℝ → ℝ} (hf : IsTest S L f) :
    Integrable f (T ∘ₘ ν) := by
  obtain ⟨a₀, ha₀⟩ := (ae_mem_of_compl_eq_zero hνS).exists
  rw [Measure.integrable_comp_iff hf.meas.aestronglyMeasurable]
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_mem_of_compl_eq_zero hνS] with a ha
    exact h.integrable L f hf a ha
  · exact (hf.norm.map h).integrable_of_moment hνS hνm ha₀

/-- `∫ f d(νT) = ∫ Tf dν` for a Lipschitz test `f` and a law `ν` on `S` with a first moment. -/
theorem integral_comp_eq_act [IsSFiniteKernel T] (h : Contraction T S q)
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hνS : ν Sᶜ = 0)
    (hνm : Integrable (fun a : ℝ => a) ν) {L : ℝ≥0} {f : ℝ → ℝ} (hf : IsTest S L f) :
    ∫ x, f x ∂(T ∘ₘ ν) = ∫ a, act T f a ∂ν :=
  KernelLimit.integral_comp_eq (hf.integrable_comp h hνS hνm)

/-- One transition keeps a first moment. -/
theorem comp_integrable_id [IsSFiniteKernel T] (h : Contraction T S q)
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hνS : ν Sᶜ = 0)
    (hνm : Integrable (fun a : ℝ => a) ν) : Integrable (fun b : ℝ => b) (T ∘ₘ ν) :=
  IsTest.integrable_comp h hνS hνm
    (⟨measurable_id, (LipschitzWith.id (α := ℝ)).lipschitzOnWith⟩ : IsTest S 1 (fun b : ℝ => b))

end SlopeEvaluation

open SlopeEvaluation

/-- `ν ≤ ν'` against every measurable test function Lipschitz and monotone on `(0, ∞)`. -/
def SlopeTestLE (ν ν' : Measure ℝ) : Prop :=
  ∀ (L : ℝ≥0) (g : ℝ → ℝ), IsTest (Set.Ioi 0) L g → MonotoneOn g (Set.Ioi 0) →
    ∫ x, g x ∂ν ≤ ∫ x, g x ∂ν'

theorem SlopeTestLE.refl (ν : Measure ℝ) : SlopeTestLE ν ν := fun _ _ _ _ => le_rfl

theorem SlopeTestLE.trans {ν₁ ν₂ ν₃ : Measure ℝ} (h₁₂ : SlopeTestLE ν₁ ν₂)
    (h₂₃ : SlopeTestLE ν₂ ν₃) : SlopeTestLE ν₁ ν₃ :=
  fun L g hg hm => (h₁₂ L g hg hm).trans (h₂₃ L g hg hm)

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-- `T` is s-finite. -/
theorem swingSlopeChainKernel_isSFiniteKernel [SFinite μ] (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) : IsSFiniteKernel (swingSlopeChainKernel X μ) := by
  have := swingSlopeChainKernel_isFiniteKernel hX hi
  infer_instance

/-! ### One transition stays below the boundary row -/

/-- **`νT ≤ T(0, ·)`** for every probability `ν` on `(0, ∞)` with a first moment. -/
theorem slopeTestLE_comp_zero [SFinite μ] (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hνS : ν (Ioi 0)ᶜ = 0)
    (hνm : Integrable (fun a : ℝ => a) ν) :
    SlopeTestLE (swingSlopeChainKernel X μ ∘ₘ ν) (swingSlopeChainKernel X μ 0) := by
  have := swingSlopeChainKernel_isSFiniteKernel hX hi
  have hc := slopeChain_contraction hX hi hG
  intro L g hg hmono
  obtain ⟨a₀, ha₀⟩ := (ae_mem_of_compl_eq_zero hνS).exists
  rw [integral_comp_eq_act hc hνS hνm hg]
  have hint : Integrable (act (swingSlopeChainKernel X μ) g) ν :=
    (hg.map hc).integrable_of_moment hνS hνm ha₀
  calc ∫ a, act (swingSlopeChainKernel X μ) g a ∂ν
      ≤ ∫ _a, (∫ x, g x ∂swingSlopeChainKernel X μ 0) ∂ν := by
        refine integral_mono_ae hint (integrable_const _) ?_
        filter_upwards [ae_mem_of_compl_eq_zero hνS] with a ha
        exact swingSlopeChainKernel_integral_le_zero hX hi hG ha hg hmono
    _ = ∫ x, g x ∂swingSlopeChainKernel X μ 0 := by simp

/-! ### `T²` preserves the order -/

/-! ### Mixtures -/

theorem mixtureWeights_toReal_add {θ : ℝ≥0∞} (hθ : θ ≤ 1) : θ.toReal + (1 - θ).toReal = 1 := by
  have hθt : θ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hθ
  rw [← ENNReal.toReal_add hθt (ENNReal.sub_ne_top ENNReal.one_ne_top), add_tsub_cancel_of_le hθ,
    ENNReal.toReal_one]

/-- **Mixtures stay above the boundary row**: if `ν ≤ ν₁` and `ν ≤ ν₂` then
`ν ≤ θν₁ + (1 - θ)ν₂` for `θ ∈ [0, 1]` (for any `ν`; the `νᵢ` are finite measures on
`(0, ∞)` with first moments). -/
theorem slopeTestLE_mixture {ν ν₁ ν₂ : Measure ℝ} [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    (hν₁S : ν₁ (Ioi 0)ᶜ = 0) (hν₁m : Integrable (fun a : ℝ => a) ν₁)
    (hν₂S : ν₂ (Ioi 0)ᶜ = 0) (hν₂m : Integrable (fun a : ℝ => a) ν₂)
    {θ : ℝ≥0∞} (hθ : θ ≤ 1) (h₁ : SlopeTestLE ν ν₁) (h₂ : SlopeTestLE ν ν₂) :
    SlopeTestLE ν (θ • ν₁ + (1 - θ) • ν₂) := by
  have hθt : θ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hθ
  intro L g hg hmono
  have hg₁ : Integrable g ν₁ := hg.integrable_of_moment hν₁S hν₁m (a₀ := 1) (mem_Ioi.mpr one_pos)
  have hg₂ : Integrable g ν₂ := hg.integrable_of_moment hν₂S hν₂m (a₀ := 1) (mem_Ioi.mpr one_pos)
  rw [integral_add_measure (hg₁.smul_measure hθt)
      (hg₂.smul_measure (ENNReal.sub_ne_top ENNReal.one_ne_top)),
    integral_smul_measure, integral_smul_measure, smul_eq_mul, smul_eq_mul]
  have e := mixtureWeights_toReal_add hθ
  have i₁ := h₁ L g hg hmono
  have i₂ := h₂ L g hg hmono
  have hθ0 : 0 ≤ θ.toReal := ENNReal.toReal_nonneg
  have hθ1 : 0 ≤ (1 - θ).toReal := ENNReal.toReal_nonneg
  calc ∫ x, g x ∂ν = θ.toReal * ∫ x, g x ∂ν + (1 - θ).toReal * ∫ x, g x ∂ν := by
        rw [← add_mul, e, one_mul]
    _ ≤ θ.toReal * ∫ x, g x ∂ν₁ + (1 - θ).toReal * ∫ x, g x ∂ν₂ := by gcongr

end SwingRepair
