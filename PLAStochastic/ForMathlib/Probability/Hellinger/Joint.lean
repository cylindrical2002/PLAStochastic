import PLAStochastic.ForMathlib.Probability.Hellinger.Affinity
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Joint densities and the exact Hellinger chain rule

A measurable family of probability densities is joined to a marginal density
by multiplying their actual functions. No independence is assumed. The chain
rule weights conditional squared distances by the marginal affinity density.
-/

set_option autoImplicit false

namespace ProbabilityTheory.HellingerDensity

noncomputable section

open MeasureTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]

/-- A probability density together with a jointly measurable conditional family. -/
def joint (p : HellingerDensity μ) (k : α → HellingerDensity ν)
    (hk : Measurable (fun z : α × β => (k z.1).density z.2)) :
    HellingerDensity (μ.prod ν) where
  density z := p.density z.1 * (k z.1).density z.2
  measurable := (p.measurable.comp measurable_fst).mul hk
  nonneg z := mul_nonneg (p.nonneg z.1) ((k z.1).nonneg z.2)
  integrable := by
    apply (integrable_prod_iff
      ((p.measurable.comp measurable_fst).mul hk).aestronglyMeasurable).2
    constructor
    · exact Filter.Eventually.of_forall fun x => (k x).integrable.const_mul (p.density x)
    · change Integrable (fun x => ∫ y, ‖p.density x * (k x).density y‖ ∂ν) μ
      have he : (fun x => ∫ y, ‖p.density x * (k x).density y‖ ∂ν) = p.density := by
        funext x
        simp only [Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg (p.nonneg x) ((k x).nonneg _)), integral_const_mul,
          (k x).integral_eq_one, mul_one]
      rw [he]
      exact p.integrable
  integral_eq_one := by
    have hi : Integrable (fun z : α × β => p.density z.1 * (k z.1).density z.2)
        (μ.prod ν) := by
      apply (integrable_prod_iff
        ((p.measurable.comp measurable_fst).mul hk).aestronglyMeasurable).2
      constructor
      · exact Filter.Eventually.of_forall fun x => (k x).integrable.const_mul (p.density x)
      · change Integrable (fun x => ∫ y, ‖p.density x * (k x).density y‖ ∂ν) μ
        simpa only [Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg (p.nonneg _) ((k _).nonneg _)), integral_const_mul,
          integral_eq_one, mul_one] using p.integrable
    rw [integral_prod _ hi]
    simp only [integral_const_mul, integral_eq_one, mul_one]

@[simp] theorem joint_density (p : HellingerDensity μ) (k : α → HellingerDensity ν)
    (hk : Measurable (fun z : α × β => (k z.1).density z.2)) (x : α) (y : β) :
    (p.joint k hk).density (x, y) = p.density x * (k x).density y := rfl

theorem affinity_joint (p q : HellingerDensity μ) (k l : α → HellingerDensity ν)
    (hk : Measurable (fun z : α × β => (k z.1).density z.2))
    (hl : Measurable (fun z : α × β => (l z.1).density z.2)) :
    (p.joint k hk).affinity (q.joint l hl) =
      ∫ x, Real.sqrt (p.density x) * Real.sqrt (q.density x) *
        (k x).affinity (l x) ∂μ := by
  rw [affinity, integral_prod _ ((p.joint k hk).affinity_integrable (q.joint l hl))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp only [joint_density, Real.sqrt_mul (p.nonneg x), Real.sqrt_mul (q.nonneg x)]
    rw [affinity, ← integral_const_mul]
    congr 1
    funext y
    ring

theorem weighted_conditional_affinity_integrable
    (p q : HellingerDensity μ) (k l : α → HellingerDensity ν)
    (hk : Measurable (fun z : α × β => (k z.1).density z.2))
    (hl : Measurable (fun z : α × β => (l z.1).density z.2)) :
    Integrable (fun x => Real.sqrt (p.density x) * Real.sqrt (q.density x) *
      (k x).affinity (l x)) μ := by
  have hi := ((p.joint k hk).affinity_integrable (q.joint l hl)).integral_prod_left
  convert hi using 1
  funext x
  simp only [joint_density, Real.sqrt_mul (p.nonneg x), Real.sqrt_mul (q.nonneg x)]
  rw [affinity, ← integral_const_mul]
  congr 1
  funext y
  ring

theorem weighted_conditional_hellinger_integrable
    (p q : HellingerDensity μ) (k l : α → HellingerDensity ν)
    (hk : Measurable (fun z : α × β => (k z.1).density z.2))
    (hl : Measurable (fun z : α × β => (l z.1).density z.2)) :
    Integrable (fun x => Real.sqrt (p.density x) * Real.sqrt (q.density x) *
      ((k x).hellinger (l x)) ^ 2) μ := by
  have hi := (p.affinity_integrable q).const_mul 2 |>.sub
    ((weighted_conditional_affinity_integrable p q k l hk hl).const_mul 2)
  convert hi using 1
  funext x
  simp only [Pi.sub_apply, hellinger_sq_eq_affinity]
  ring

/-- Exact chain rule, including a changing marginal and changing conditional laws. -/
theorem hellinger_sq_joint (p q : HellingerDensity μ) (k l : α → HellingerDensity ν)
    (hk : Measurable (fun z : α × β => (k z.1).density z.2))
    (hl : Measurable (fun z : α × β => (l z.1).density z.2)) :
    (p.joint k hk).hellinger (q.joint l hl) ^ 2 = p.hellinger q ^ 2 +
      ∫ x, Real.sqrt (p.density x) * Real.sqrt (q.density x) *
        ((k x).hellinger (l x)) ^ 2 ∂μ := by
  have he : (fun x => Real.sqrt (p.density x) * Real.sqrt (q.density x) *
        ((k x).hellinger (l x)) ^ 2) =
      (fun x => 2 * (Real.sqrt (p.density x) * Real.sqrt (q.density x))) -
      (fun x => 2 * (Real.sqrt (p.density x) * Real.sqrt (q.density x) *
        (k x).affinity (l x))) := by
    funext x
    simp only [Pi.sub_apply, hellinger_sq_eq_affinity]
    ring
  rw [hellinger_sq_eq_affinity, hellinger_sq_eq_affinity, affinity_joint, he]
  have hsub := integral_sub ((p.affinity_integrable q).const_mul 2)
    ((weighted_conditional_affinity_integrable p q k l hk hl).const_mul 2)
  change 2 - 2 * (∫ x, Real.sqrt (p.density x) * Real.sqrt (q.density x) *
    (k x).affinity (l x) ∂μ) = 2 - 2 * p.affinity q +
    (∫ x, 2 * (Real.sqrt (p.density x) * Real.sqrt (q.density x)) -
      2 * (Real.sqrt (p.density x) * Real.sqrt (q.density x) *
        (k x).affinity (l x)) ∂μ)
  rw [hsub, integral_const_mul, integral_const_mul]
  change 2 - 2 * _ = 2 - 2 * p.affinity q + (2 * p.affinity q - 2 * _)
  ring

/-- A common conditional kernel preserves the marginal Hellinger distance exactly. -/
theorem hellinger_joint_same (p q : HellingerDensity μ) (k : α → HellingerDensity ν)
    (hk : Measurable (fun z : α × β => (k z.1).density z.2)) :
    (p.joint k hk).hellinger (q.joint k hk) = p.hellinger q := by
  have he := hellinger_sq_joint p q k k hk hk
  simp only [hellinger_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero,
    integral_zero, add_zero] at he
  nlinarith [(p.joint k hk).hellinger_nonneg (q.joint k hk), p.hellinger_nonneg q]

end

end ProbabilityTheory.HellingerDensity
