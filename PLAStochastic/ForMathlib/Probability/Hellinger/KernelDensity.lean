import PLAStochastic.ForMathlib.Probability.Hellinger.Affinity
import PLAStochastic.ForMathlib.Probability.Hellinger.RadonNikodym
import Mathlib.Probability.Kernel.RadonNikodym
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Probability densities over a state-dependent reference kernel

A jointly measurable conditional density may use a different finite
dominating measure at every state. Its actual composition with a marginal
density is normalized by kernel Fubini. Kernel Radon-Nikodym derivatives
provide these families without assuming absolute continuity to volume.
-/

set_option autoImplicit false

namespace ProbabilityTheory

noncomputable section

open MeasureTheory Set

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

structure KernelHellingerDensity (eta : Kernel α β) where
  density : α × β → ℝ
  measurable : Measurable density
  nonneg : ∀ z, 0 ≤ density z
  integrable : ∀ x, Integrable (fun y => density (x, y)) (eta x)
  integral_eq_one : ∀ x, ∫ y, density (x, y) ∂(eta x) = 1

namespace KernelHellingerDensity

variable {eta : Kernel α β}

def fiber (k : KernelHellingerDensity eta) (x : α) : HellingerDensity (eta x) where
  density y := k.density (x, y)
  measurable := k.measurable.comp measurable_prodMk_left
  nonneg y := k.nonneg (x, y)
  integrable := k.integrable x
  integral_eq_one := k.integral_eq_one x

def joint {mu : Measure α} [SFinite mu] [IsSFiniteKernel eta]
    (k : KernelHellingerDensity eta) (p : HellingerDensity mu) :
    HellingerDensity (mu ⊗ₘ eta) where
  density z := p.density z.1 * k.density z
  measurable := (p.measurable.comp measurable_fst).mul k.measurable
  nonneg z := mul_nonneg (p.nonneg z.1) (k.nonneg z)
  integrable := by
    apply (Measure.integrable_compProd_iff
      ((p.measurable.comp measurable_fst).mul k.measurable).aestronglyMeasurable).mpr
    constructor
    · exact Filter.Eventually.of_forall fun x => (k.integrable x).const_mul (p.density x)
    · change Integrable (fun x => ∫ y, ‖p.density x * k.density (x, y)‖ ∂(eta x)) mu
      simpa only [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (p.nonneg _) (k.nonneg _)), integral_const_mul,
        k.integral_eq_one, mul_one] using p.integrable
  integral_eq_one := by
    have hi : Integrable (fun z : α × β => p.density z.1 * k.density z) (mu ⊗ₘ eta) := by
      apply (Measure.integrable_compProd_iff
        ((p.measurable.comp measurable_fst).mul k.measurable).aestronglyMeasurable).mpr
      constructor
      · exact Filter.Eventually.of_forall fun x => (k.integrable x).const_mul (p.density x)
      · change Integrable (fun x => ∫ y, ‖p.density x * k.density (x, y)‖ ∂(eta x)) mu
        simpa only [Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg (p.nonneg _) (k.nonneg _)), integral_const_mul,
          k.integral_eq_one, mul_one] using p.integrable
    rw [Measure.integral_compProd hi]
    simp only [integral_const_mul, k.integral_eq_one, mul_one, p.integral_eq_one]

def ofProbability [MeasurableSpace.CountableOrCountablyGenerated α β]
    (kappa eta : Kernel α β) [IsMarkovKernel kappa] [IsFiniteKernel eta]
    (hac : ∀ x, kappa x ≪ eta x) : KernelHellingerDensity eta where
  density z := (kappa.rnDeriv eta z.1 z.2).toReal
  measurable := (Kernel.measurable_rnDeriv kappa eta).ennreal_toReal
  nonneg _ := ENNReal.toReal_nonneg
  integrable x := by
    have he : (fun y => (kappa.rnDeriv eta x y).toReal) =ᵐ[eta x]
        (fun y => ((kappa x).rnDeriv (eta x) y).toReal) :=
      (Kernel.rnDeriv_eq_rnDeriv_measure (κ := kappa) (η := eta) (a := x)).fun_comp
        ENNReal.toReal
    exact (HellingerDensity.ofProbability (kappa x) (eta x) (hac x)).integrable.congr he.symm
  integral_eq_one x := by
    have he : (fun y => (kappa.rnDeriv eta x y).toReal) =ᵐ[eta x]
        (fun y => ((kappa x).rnDeriv (eta x) y).toReal) :=
      (Kernel.rnDeriv_eq_rnDeriv_measure (κ := kappa) (η := eta) (a := x)).fun_comp
        ENNReal.toReal
    rw [integral_congr_ae he]
    exact (HellingerDensity.ofProbability (kappa x) (eta x) (hac x)).integral_eq_one

end KernelHellingerDensity

end

end ProbabilityTheory
