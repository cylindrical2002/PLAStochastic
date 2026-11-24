import PLAStochastic.ForMathlib.Probability.Moments.AbsoluteThirdCentral

/-! # The actual fourth central moment from four finite raw moments -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BrownianAffine
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω→ℝ}
variable [IsProbabilityMeasure μ]

theorem integral_fourth_sub (hX : MemLp X 4 μ) (a : ℝ) :
    (∫ ω,(X ω-a)^4 ∂μ)=
      (∫ ω,X ω^4 ∂μ)-4*a*(∫ ω,X ω^3 ∂μ)+
        6*a^2*(∫ ω,X ω^2 ∂μ)-4*a^3*(∫ ω,X ω ∂μ)+a^4 := by
  have h₁ : Integrable X μ := hX.integrable (by norm_num)
  have h₂ : Integrable (fun ω => X ω^2) μ :=
    integrable_pow_of_memLp (by decide) (hX.mono_exponent (by norm_num))
  have h₃ : Integrable (fun ω => X ω^3) μ :=
    integrable_pow_of_memLp (by decide) (hX.mono_exponent (by norm_num))
  have h₄ : Integrable (fun ω => X ω^4) μ := integrable_pow_of_memLp (by decide) hX
  have he : (fun ω => (X ω-a)^4)=
      fun ω => X ω^4-4*a*X ω^3+6*a^2*X ω^2-4*a^3*X ω+a^4 := by funext ω; ring
  have hA : Integrable (fun ω => X ω^4-4*a*X ω^3) μ := h₄.sub (h₃.const_mul (4*a))
  have hB : Integrable (fun ω => X ω^4-4*a*X ω^3+6*a^2*X ω^2) μ := hA.add (h₂.const_mul (6*a^2))
  have hC : Integrable (fun ω => X ω^4-4*a*X ω^3+6*a^2*X ω^2-4*a^3*X ω) μ := hB.sub (h₁.const_mul (4*a^3))
  rw [he,integral_add hC (integrable_const _),integral_sub hB (h₁.const_mul _),
    integral_add hA (h₂.const_mul _),integral_sub h₄ (h₃.const_mul _)]
  simp only [integral_const_mul,integral_const,probReal_univ,one_smul]

theorem integral_centered_fourth (hX : MemLp X 4 μ) :
    (∫ ω,(X ω-∫ z,X z ∂μ)^4 ∂μ)=
      (∫ ω,X ω^4 ∂μ)-4*(∫ ω,X ω ∂μ)*(∫ ω,X ω^3 ∂μ)+
        6*(∫ ω,X ω ∂μ)^2*(∫ ω,X ω^2 ∂μ)-3*(∫ ω,X ω ∂μ)^4 := by
  rw [integral_fourth_sub hX]
  ring

theorem integrable_fourth_central (hX : MemLp X 4 μ) (a : ℝ) :
    Integrable (fun ω => (X ω-a)^4) μ :=
  integrable_pow_of_memLp (by decide) (hX.sub (memLp_const a))

end BrownianAffine
