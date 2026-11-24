import PLAStochastic.ForMathlib.Probability.Hellinger.KernelChainRule
import PLAStochastic.ForMathlib.Probability.Hellinger.KernelDensityLaw
import PLAStochastic.ForMathlib.Probability.Hellinger.MeasureMetric

/-!
# Exact chain identity for actual probability kernels

The common conditional reference is the sum of the two actual kernels.
Its Radon-Nikodym factors represent the joint laws exactly. Thus the chain
identity applies without volume densities, including killed or atomic states.
-/

set_option autoImplicit false

namespace ProbabilityTheory

noncomputable section

open MeasureTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable [MeasurableSpace.CountableOrCountablyGenerated α β]

theorem measureHellinger_compProd_sq (P Q : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (kappa lam : Kernel α β) [IsMarkovKernel kappa] [IsMarkovKernel lam] :
    measureHellinger (P ⊗ₘ kappa) (Q ⊗ₘ lam) ^ 2 = measureHellinger P Q ^ 2 +
      ∫ x, Real.sqrt ((P.rnDeriv (P + Q) x).toReal) *
        Real.sqrt ((Q.rnDeriv (P + Q) x).toReal) *
        measureHellinger (kappa x) (lam x) ^ 2 ∂(P + Q) := by
  let mu := P + Q
  let eta := kappa + lam
  have hacK (x : α) : kappa x ≪ eta x := by
    change kappa x ≪ kappa x + lam x
    exact Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have hacL (x : α) : lam x ≪ eta x := by
    change lam x ≪ kappa x + lam x
    exact Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  let p := HellingerDensity.leftDensity P Q
  let q := HellingerDensity.rightDensity P Q
  let k := KernelHellingerDensity.ofProbability kappa eta hacK
  let l := KernelHellingerDensity.ofProbability lam eta hacL
  have hp : p.toMeasure = P := HellingerDensity.leftDensity_toMeasure P Q
  have hq : q.toMeasure = Q := HellingerDensity.rightDensity_toMeasure P Q
  have hk : k.toKernel = kappa := KernelHellingerDensity.ofProbability_toKernel _ _ _
  have hl : l.toKernel = lam := KernelHellingerDensity.ofProbability_toKernel _ _ _
  have hjK : (k.joint p).toMeasure = P ⊗ₘ kappa := by
    rw [KernelHellingerDensity.joint_toMeasure, hp, hk]
  have hjL : (l.joint q).toMeasure = Q ⊗ₘ lam := by
    rw [KernelHellingerDensity.joint_toMeasure, hq, hl]
  have hfK (x : α) : (k.fiber x).toMeasure = kappa x := by
    rw [← KernelHellingerDensity.toKernel_apply, hk]
  have hfL (x : α) : (l.fiber x).toMeasure = lam x := by
    rw [← KernelHellingerDensity.toKernel_apply, hl]
  have hcond (x : α) : measureHellinger (kappa x) (lam x) =
      (k.fiber x).hellinger (l.fiber x) := by
    simpa only [hfK x, hfL x] using
      measureHellinger_eq_density_of_finite (k.fiber x) (l.fiber x)
  have hbase : measureHellinger P Q = p.hellinger q := rfl
  have hjoint : measureHellinger (P ⊗ₘ kappa) (Q ⊗ₘ lam) =
      (k.joint p).hellinger (l.joint q) := by
    simpa only [hjK, hjL] using measureHellinger_eq_density_of_finite (k.joint p) (l.joint q)
  rw [hjoint, hbase, KernelHellingerDensity.hellinger_sq_joint]
  apply congrArg (fun z => p.hellinger q ^ 2 + z)
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [hcond x]
    rfl

end

end ProbabilityTheory
