import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Tactic

/-!
# Uniform nonnegative integral budgets through probability kernels

The observed-state distribution is arbitrary. Integrability and a common
nonnegative bound on every conditional fiber pay the composed actual law.
-/

set_option autoImplicit false

namespace ProbabilityTheory

noncomputable section

open MeasureTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

theorem integrable_comp_of_uniform_nonnegative
    (mu : Measure α) [IsProbabilityMeasure mu]
    (kappa : Kernel α β) [IsMarkovKernel kappa]
    {F : β → ℝ} (hF : Measurable F) {B : ℝ} (hB : 0 ≤ B)
    (hpos : ∀ x, ∀ᵐ z ∂kappa x, 0 ≤ F z)
    (hi : ∀ x, Integrable F (kappa x))
    (hb : ∀ x, ∫ z, F z ∂kappa x ≤ B) :
    Integrable F (kappa ∘ₘ mu) ∧ ∫ z, F z ∂(kappa ∘ₘ mu) ≤ B := by
  have hpos' : ∀ᵐ z ∂(kappa ∘ₘ mu), 0 ≤ F z :=
    Measure.ae_comp_of_ae_ae (measurableSet_le measurable_const hF)
      (Filter.Eventually.of_forall hpos)
  have hlin : (∫⁻ z, ENNReal.ofReal (F z) ∂(kappa ∘ₘ mu)) ≤ ENNReal.ofReal B := by
    calc
      _ = ∫⁻ x, ENNReal.ofReal (∫ z, F z ∂kappa x) ∂mu := by
        rw [Measure.lintegral_bind kappa.aemeasurable hF.ennreal_ofReal.aemeasurable]
        exact lintegral_congr fun x =>
          (ofReal_integral_eq_lintegral_ofReal (hi x) (hpos x)).symm
      _ ≤ ∫⁻ _x, ENNReal.ofReal B ∂mu :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hb x)
      _ = _ := by simp
  have hint : Integrable F (kappa ∘ₘ mu) :=
    ⟨hF.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hpos').mpr (hlin.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hint, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hint hpos'] at hlin
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp hlin

end

end ProbabilityTheory
