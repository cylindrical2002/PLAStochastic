import PLAStochastic.ForMathlib.Probability.Hellinger.KernelMeasureChain
import PLAStochastic.ForMathlib.Probability.Hellinger.StoppedChain

/-!
# State-dependent Hellinger budgets for actual probability kernels

A nonuniform conditional squared budget is averaged against the two actual
past laws. This retains the moment of the physical state and the probability
of an active state, rather than replacing them by a global supremum.
-/

set_option autoImplicit false

namespace ProbabilityTheory

noncomputable section

open MeasureTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable [MeasurableSpace.CountableOrCountablyGenerated α β]

theorem measureHellinger_compProd_integrable (P Q : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (kappa lam : Kernel α β) [IsMarkovKernel kappa] [IsMarkovKernel lam] :
    Integrable (fun x => Real.sqrt ((P.rnDeriv (P + Q) x).toReal) *
      Real.sqrt ((Q.rnDeriv (P + Q) x).toReal) *
      measureHellinger (kappa x) (lam x) ^ 2) (P + Q) := by
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
  have hfK (x : α) : (k.fiber x).toMeasure = kappa x := by
    rw [← KernelHellingerDensity.toKernel_apply,
      KernelHellingerDensity.ofProbability_toKernel]
  have hfL (x : α) : (l.fiber x).toMeasure = lam x := by
    rw [← KernelHellingerDensity.toKernel_apply,
      KernelHellingerDensity.ofProbability_toKernel]
  have hcond (x : α) : measureHellinger (kappa x) (lam x) =
      (k.fiber x).hellinger (l.fiber x) := by
    simpa only [hfK x, hfL x] using
      measureHellinger_eq_density_of_finite (k.fiber x) (l.fiber x)
  apply (KernelHellingerDensity.weighted_conditional_hellinger_integrable p q k l).congr
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [hcond x]
    rfl

theorem measureHellinger_compProd_sq_le_budget (P Q : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (kappa lam : Kernel α β) [IsMarkovKernel kappa] [IsMarkovKernel lam]
    {B : α → ℝ} (hP : Integrable B P) (hQ : Integrable B Q)
    (hcond : ∀ x, measureHellinger (kappa x) (lam x) ^ 2 ≤ B x) :
    measureHellinger (P ⊗ₘ kappa) (Q ⊗ₘ lam) ^ 2 ≤ measureHellinger P Q ^ 2 +
      ((∫ x, B x ∂P) + ∫ x, B x ∂Q) / 2 := by
  let p := HellingerDensity.leftDensity P Q
  let q := HellingerDensity.rightDensity P Q
  have hp : p.toMeasure = P := HellingerDensity.leftDensity_toMeasure P Q
  have hq : q.toMeasure = Q := HellingerDensity.rightDensity_toMeasure P Q
  have hiP : Integrable (fun x => p.density x * B x) (P + Q) :=
    (p.integrable_toMeasure_iff B).mp (hp.symm ▸ hP)
  have hiQ : Integrable (fun x => q.density x * B x) (P + Q) :=
    (q.integrable_toMeasure_iff B).mp (hq.symm ▸ hQ)
  have hB (x : α) : 0 ≤ B x := (sq_nonneg _).trans (hcond x)
  rw [measureHellinger_compProd_sq]
  apply add_le_add le_rfl
  calc
    (∫ x, Real.sqrt ((P.rnDeriv (P + Q) x).toReal) *
      Real.sqrt ((Q.rnDeriv (P + Q) x).toReal) *
      measureHellinger (kappa x) (lam x) ^ 2 ∂(P + Q)) ≤
        ∫ x, (p.density x * B x + q.density x * B x) / 2 ∂(P + Q) := by
      apply integral_mono (measureHellinger_compProd_integrable P Q kappa lam)
        ((hiP.add hiQ).div_const 2)
      intro x
      change Real.sqrt (p.density x) * Real.sqrt (q.density x) *
        measureHellinger (kappa x) (lam x) ^ 2 ≤
        (p.density x * B x + q.density x * B x) / 2
      have hfirst := mul_le_mul_of_nonneg_left (hcond x)
        (mul_nonneg (Real.sqrt_nonneg (p.density x)) (Real.sqrt_nonneg (q.density x)))
      have havg := mul_le_mul_of_nonneg_right
        (HellingerDensity.sqrt_mul_le_average (p.nonneg x) (q.nonneg x)) (hB x)
      nlinarith only [hfirst, havg]
    _ = ((∫ x, B x ∂P) + ∫ x, B x ∂Q) / 2 := by
      rw [integral_div, integral_add hiP hiQ, ← p.integral_toMeasure,
        ← q.integral_toMeasure, hp, hq]

end

end ProbabilityTheory
