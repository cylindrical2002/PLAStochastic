import PLAStochastic.ForMathlib.Probability.Hellinger.KernelDensity

/-!
# Exact Hellinger chain rule over variable reference kernels

The conditional reference may depend on the past state and may contain atoms.
The conditional squared distance is weighted by the marginal affinity density.
This is the same exact chain identity as for product densities, proved by
kernel Fubini on the actual composition-product measure.
-/

set_option autoImplicit false

namespace ProbabilityTheory.KernelHellingerDensity

noncomputable section

open MeasureTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {mu : Measure α} [SFinite mu] {eta : Kernel α β} [IsSFiniteKernel eta]

theorem affinity_joint (p q : HellingerDensity mu) (k l : KernelHellingerDensity eta) :
    (k.joint p).affinity (l.joint q) =
      ∫ x, Real.sqrt (p.density x) * Real.sqrt (q.density x) *
        (k.fiber x).affinity (l.fiber x) ∂mu := by
  rw [HellingerDensity.affinity,
    Measure.integral_compProd ((k.joint p).affinity_integrable (l.joint q))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change (∫ y, Real.sqrt (p.density x * k.density (x, y)) *
      Real.sqrt (q.density x * l.density (x, y)) ∂(eta x)) = _
    simp only [Real.sqrt_mul (p.nonneg x), Real.sqrt_mul (q.nonneg x)]
    rw [HellingerDensity.affinity, ← integral_const_mul]
    congr 1
    funext y
    change Real.sqrt (p.density x) * Real.sqrt (k.density (x, y)) *
      (Real.sqrt (q.density x) * Real.sqrt (l.density (x, y))) =
      (Real.sqrt (p.density x) * Real.sqrt (q.density x)) *
        (Real.sqrt (k.density (x, y)) * Real.sqrt (l.density (x, y)))
    ring

theorem weighted_conditional_affinity_integrable (p q : HellingerDensity mu)
    (k l : KernelHellingerDensity eta) :
    Integrable (fun x => Real.sqrt (p.density x) * Real.sqrt (q.density x) *
      (k.fiber x).affinity (l.fiber x)) mu := by
  have hm : Measurable (fun z : α × β =>
      Real.sqrt ((k.joint p).density z) * Real.sqrt ((l.joint q).density z)) :=
    (k.joint p).measurable.sqrt.mul (l.joint q).measurable.sqrt
  have hi := ((Measure.integrable_compProd_iff hm.aestronglyMeasurable).mp
    ((k.joint p).affinity_integrable (l.joint q))).2
  change Integrable (fun x => ∫ y,
    ‖Real.sqrt (p.density x * k.density (x, y)) *
      Real.sqrt (q.density x * l.density (x, y))‖ ∂(eta x)) mu at hi
  apply hi.congr
  exact Filter.Eventually.of_forall fun x => by
    simp only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _))]
    simp only [Real.sqrt_mul (p.nonneg x), Real.sqrt_mul (q.nonneg x)]
    rw [HellingerDensity.affinity, ← integral_const_mul]
    congr 1
    funext y
    change Real.sqrt (p.density x) * Real.sqrt (k.density (x, y)) *
      (Real.sqrt (q.density x) * Real.sqrt (l.density (x, y))) =
      (Real.sqrt (p.density x) * Real.sqrt (q.density x)) *
        (Real.sqrt (k.density (x, y)) * Real.sqrt (l.density (x, y)))
    ring

theorem weighted_conditional_hellinger_integrable (p q : HellingerDensity mu)
    (k l : KernelHellingerDensity eta) :
    Integrable (fun x => Real.sqrt (p.density x) * Real.sqrt (q.density x) *
      (k.fiber x).hellinger (l.fiber x) ^ 2) mu := by
  have hi := ((p.affinity_integrable q).const_mul 2).sub
    ((weighted_conditional_affinity_integrable p q k l).const_mul 2)
  apply hi.congr
  exact Filter.Eventually.of_forall fun x => by
    simp only [Pi.sub_apply, HellingerDensity.hellinger_sq_eq_affinity]
    ring

theorem hellinger_sq_joint (p q : HellingerDensity mu) (k l : KernelHellingerDensity eta) :
    (k.joint p).hellinger (l.joint q) ^ 2 = p.hellinger q ^ 2 +
      ∫ x, Real.sqrt (p.density x) * Real.sqrt (q.density x) *
        (k.fiber x).hellinger (l.fiber x) ^ 2 ∂mu := by
  have he : (fun x => Real.sqrt (p.density x) * Real.sqrt (q.density x) *
      (k.fiber x).hellinger (l.fiber x) ^ 2) =
      (fun x => 2 * (Real.sqrt (p.density x) * Real.sqrt (q.density x))) -
      (fun x => 2 * (Real.sqrt (p.density x) * Real.sqrt (q.density x) *
        (k.fiber x).affinity (l.fiber x))) := by
    funext x
    simp only [Pi.sub_apply, HellingerDensity.hellinger_sq_eq_affinity]
    ring
  rw [HellingerDensity.hellinger_sq_eq_affinity,
    HellingerDensity.hellinger_sq_eq_affinity, affinity_joint, he]
  have hsub := integral_sub ((p.affinity_integrable q).const_mul 2)
    ((weighted_conditional_affinity_integrable p q k l).const_mul 2)
  change 2 - 2 * (∫ x, Real.sqrt (p.density x) * Real.sqrt (q.density x) *
    (k.fiber x).affinity (l.fiber x) ∂mu) = 2 - 2 * p.affinity q +
    (∫ x, 2 * (Real.sqrt (p.density x) * Real.sqrt (q.density x)) -
      2 * (Real.sqrt (p.density x) * Real.sqrt (q.density x) *
        (k.fiber x).affinity (l.fiber x)) ∂mu)
  rw [hsub, integral_const_mul, integral_const_mul]
  change 2 - 2 * _ = 2 - 2 * p.affinity q + (2 * p.affinity q - 2 * _)
  ring

end

end ProbabilityTheory.KernelHellingerDensity
