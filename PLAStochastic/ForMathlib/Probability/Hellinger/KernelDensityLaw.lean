import PLAStochastic.ForMathlib.Probability.Hellinger.KernelDensity
import Mathlib.Probability.Kernel.CompProdEqIff

/-!
# Actual laws represented by conditional kernel densities

Every normalized kernel density defines a Markov kernel. Its composition
with a marginal density is exactly the measure represented by the joint
density, including the full product of Radon-Nikodym factors.
-/

set_option autoImplicit false

namespace ProbabilityTheory.KernelHellingerDensity

noncomputable section

open MeasureTheory Set

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {eta : Kernel α β} [IsSFiniteKernel eta]

def toKernel (k : KernelHellingerDensity eta) : Kernel α β :=
  eta.withDensity (fun x y => ENNReal.ofReal (k.density (x, y)))

theorem toKernel_apply (k : KernelHellingerDensity eta) (x : α) :
    k.toKernel x = (k.fiber x).toMeasure := by
  rw [toKernel, Kernel.withDensity_apply _ k.measurable.ennreal_ofReal]
  rfl

instance isMarkovKernel_toKernel (k : KernelHellingerDensity eta) :
    IsMarkovKernel k.toKernel where
  isProbabilityMeasure x := by
    rw [toKernel_apply]
    infer_instance

theorem ofProbability_toKernel [MeasurableSpace.CountableOrCountablyGenerated α β]
    (kappa eta : Kernel α β) [IsMarkovKernel kappa] [IsFiniteKernel eta]
    (hac : ∀ x, kappa x ≪ eta x) :
    (ofProbability kappa eta hac).toKernel = kappa := by
  ext x : 1
  rw [toKernel_apply]
  calc
    ((ofProbability kappa eta hac).fiber x).toMeasure =
        (HellingerDensity.ofProbability (kappa x) (eta x) (hac x)).toMeasure := by
      unfold HellingerDensity.toMeasure
      apply withDensity_congr_ae
      filter_upwards [Kernel.rnDeriv_eq_rnDeriv_measure
        (κ := kappa) (η := eta) (a := x)] with y hy
      exact congrArg (fun (z : ENNReal) => ENNReal.ofReal z.toReal) hy
    _ = kappa x := HellingerDensity.ofProbability_toMeasure _ _ _

theorem toMeasure_compProd_reference {mu : Measure α} [SFinite mu]
    (p : HellingerDensity mu) :
    p.toMeasure ⊗ₘ eta = (mu ⊗ₘ eta).withDensity
      (fun z : α × β => ENNReal.ofReal (p.density z.1)) := by
  ext s hs
  rw [Measure.compProd_apply hs, HellingerDensity.toMeasure,
    lintegral_withDensity_eq_lintegral_mul _ p.measurable.ennreal_ofReal
      (Kernel.measurable_kernel_prodMk_left hs), withDensity_apply _ hs,
    ← lintegral_indicator hs]
  have hm : Measurable (s.indicator
      (fun z : α × β => ENNReal.ofReal (p.density z.1))) :=
    (p.measurable.comp measurable_fst).ennreal_ofReal.indicator hs
  rw [Measure.lintegral_compProd hm]
  apply lintegral_congr
  intro x
  change ENNReal.ofReal (p.density x) * eta x (Prod.mk x ⁻¹' s) =
    ∫⁻ y, s.indicator (fun z : α × β => ENNReal.ofReal (p.density z.1)) (x, y) ∂(eta x)
  have he : (fun y => s.indicator
      (fun z : α × β => ENNReal.ofReal (p.density z.1)) (x, y)) =
      (Prod.mk x ⁻¹' s).indicator (fun _ => ENNReal.ofReal (p.density x)) := rfl
  rw [he, lintegral_indicator_const (measurable_prodMk_left hs)]

theorem joint_toMeasure {mu : Measure α} [SFinite mu]
    (p : HellingerDensity mu) (k : KernelHellingerDensity eta) :
    (k.joint p).toMeasure = p.toMeasure ⊗ₘ k.toKernel := by
  have hk : Measurable (fun z : α × β => ENNReal.ofReal (k.density z)) :=
    k.measurable.ennreal_ofReal
  have hp : Measurable (fun z : α × β => ENNReal.ofReal (p.density z.1)) :=
    (p.measurable.comp measurable_fst).ennreal_ofReal
  let : IsSFiniteKernel (eta.withDensity
      (fun x y => ENNReal.ofReal (k.density (x, y)))) :=
    inferInstanceAs (IsSFiniteKernel k.toKernel)
  rw [toKernel, Measure.compProd_withDensity hk, toMeasure_compProd_reference,
    ← withDensity_mul _ hp hk]
  unfold HellingerDensity.toMeasure
  congr 1
  funext z
  change ENNReal.ofReal (p.density z.1 * k.density z) =
    ENNReal.ofReal (p.density z.1) * ENNReal.ofReal (k.density z)
  exact ENNReal.ofReal_mul (p.nonneg z.1)

end

end ProbabilityTheory.KernelHellingerDensity
