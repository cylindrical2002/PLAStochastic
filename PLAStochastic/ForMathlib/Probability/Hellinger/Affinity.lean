import PLAStochastic.ForMathlib.Probability.Hellinger.Observables

/-!
# Affinity and the exact squared-distance identity

The affinity is the actual integral of the product of square-root densities.
Its relation to Hellinger distance fixes the constants used in the chain rule.
-/

set_option autoImplicit false

namespace ProbabilityTheory.HellingerDensity

noncomputable section

open MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

def affinity (p q : HellingerDensity μ) : ℝ :=
  ∫ x, Real.sqrt (p.density x) * Real.sqrt (q.density x) ∂μ

theorem affinity_integrable (p q : HellingerDensity μ) :
    Integrable (fun x => Real.sqrt (p.density x) * Real.sqrt (q.density x)) μ :=
  integrable_mul_of_memLp_two p.sqrt_memLp q.sqrt_memLp

theorem affinity_eq_inner (p q : HellingerDensity μ) :
    p.affinity q = inner ℝ p.root q.root :=
  (inner_toLp_eq_integral_mul p.sqrt_memLp q.sqrt_memLp).symm

theorem affinity_nonneg (p q : HellingerDensity μ) : 0 ≤ p.affinity q :=
  integral_nonneg fun x => mul_nonneg (Real.sqrt_nonneg (p.density x))
    (Real.sqrt_nonneg (q.density x))

theorem affinity_le_one (p q : HellingerDensity μ) : p.affinity q ≤ 1 := by
  rw [affinity_eq_inner]
  simpa only [norm_root, mul_one] using real_inner_le_norm p.root q.root

@[simp] theorem affinity_self (p : HellingerDensity μ) : p.affinity p = 1 := by
  rw [affinity_eq_inner, real_inner_self_eq_norm_sq, norm_root_sq]

theorem hellinger_sq_eq_affinity (p q : HellingerDensity μ) :
    p.hellinger q ^ 2 = 2 - 2 * p.affinity q := by
  rw [hellinger, dist_eq_norm, norm_sub_sq_real, norm_root_sq, norm_root_sq,
    ← affinity_eq_inner]
  ring

end

end ProbabilityTheory.HellingerDensity
