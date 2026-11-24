import PLAStochastic.Affine.Lifetime.TailMoments
import PLAStochastic.Affine.Lifetime.InverseErrorLaw

/-!
# Moment integrability at every positive tolerance

The proved Brownian lifetime scaling law transports unit-tolerance finiteness,
all finite moment orders, and a neighborhood of exponential moments to every
positive tolerance. The tail-moment identity uses the original extended lifetime.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

namespace BrownianAffine

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem identDistrib_anchoredLifetime_toReal_tolerance (hB : IsBrownianReal B μ) {ε : ℝ} (hε : 0 < ε) :
    IdentDistrib (fun ω => (anchoredProcessLifetime B ε ω).toReal)
      (fun ω => ε ^ 2 * anchoredUnitLifetime B ω) μ μ := by
  simpa only [Function.comp_def, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hε.le, anchoredUnitLifetime] using!
    (identDistrib_anchoredLifetime_tolerance hB hε).comp ENNReal.measurable_toReal

/-- Finiteness at arbitrary positive tolerance is transferred before passing to real values. -/
theorem anchoredProcessLifetime_tolerance_ae_ne_top (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 < ε) : ∀ᵐ ω ∂μ, anchoredProcessLifetime B ε ω ≠ ∞ := by
  apply (identDistrib_anchoredLifetime_tolerance hB hε).symm.ae_snd (measurableSet_singleton ∞).compl
  filter_upwards [anchoredProcessLifetime_ae_ne_top hB] with ω hω
  exact ENNReal.mul_ne_top (by simp) hω

theorem anchoredProcessLifetime_tolerance_memLp (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 < ε) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun ω => (anchoredProcessLifetime B ε ω).toReal) p μ :=
  (identDistrib_anchoredLifetime_toReal_tolerance hB hε).symm.memLp_snd
    ((anchoredUnitLifetime_memLp hB p hp).const_mul (ε ^ 2))

theorem anchoredProcessLifetime_tolerance_integrable_rpow (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 < ε) {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun ω => (anchoredProcessLifetime B ε ω).toReal ^ p) μ := by
  have hlaw := (identDistrib_anchoredLifetime_toReal_tolerance hB hε).comp (measurable_id.pow_const p)
  apply hlaw.symm.integrable_snd
  have hi := (anchoredUnitLifetime_integrable_rpow hB hp).const_mul ((ε ^ 2) ^ p)
  simpa only [Function.comp_def, id_eq, Real.mul_rpow (sq_nonneg ε) (anchoredUnitLifetime_nonnegative B _)] using hi

theorem anchoredProcessLifetime_tolerance_integrable_pow (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    Integrable (fun ω => (anchoredProcessLifetime B ε ω).toReal ^ n) μ := by
  simpa only [Real.rpow_natCast] using anchoredProcessLifetime_tolerance_integrable_rpow hB hε
    (show (0 : ℝ) ≤ n by positivity)

theorem anchoredProcessLifetime_tolerance_exp_neighborhood (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ t : ℝ, |t| ≤ θ →
      Integrable (fun ω => Real.exp (t * (anchoredProcessLifetime B ε ω).toReal)) μ := by
  obtain ⟨θ, hθ, hint⟩ := anchoredUnitLifetime_exp_neighborhood hB
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  refine ⟨θ / ε ^ 2, div_pos hθ hεsq, fun t ht => ?_⟩
  have hrate : |t * ε ^ 2| ≤ θ := by
    rw [abs_mul, abs_of_nonneg hεsq.le]
    exact (le_div_iff₀ hεsq).mp ht
  have hlaw := (identDistrib_anchoredLifetime_toReal_tolerance hB hε).comp
    (by fun_prop : Measurable (fun x : ℝ => Real.exp (t * x)))
  apply hlaw.symm.integrable_snd
  simpa only [Function.comp_def, mul_assoc] using! hint (t * ε ^ 2) hrate

/-- Real-order raw moments scale by the corresponding power of the tolerance squared. -/
theorem anchoredProcessLifetime_tolerance_moment_scaling (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 < ε) {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun ω => (anchoredProcessLifetime B ε ω).toReal ^ p) μ ∧
      (∫ ω, (anchoredProcessLifetime B ε ω).toReal ^ p ∂μ) =
        (ε ^ 2) ^ p * ∫ ω, anchoredUnitLifetime B ω ^ p ∂μ := by
  refine ⟨anchoredProcessLifetime_tolerance_integrable_rpow hB hε hp, ?_⟩
  have hlaw := (identDistrib_anchoredLifetime_toReal_tolerance hB hε).comp (measurable_id.pow_const p)
  calc
    (∫ ω, (anchoredProcessLifetime B ε ω).toReal ^ p ∂μ) =
        ∫ ω, (ε ^ 2 * anchoredUnitLifetime B ω) ^ p ∂μ := hlaw.integral_eq
    _ = (ε ^ 2) ^ p * ∫ ω, anchoredUnitLifetime B ω ^ p ∂μ := by
      simp_rw [Real.mul_rpow (sq_nonneg ε) (anchoredUnitLifetime_nonnegative B _), integral_const_mul]

/-- The real-order tail identity remains valid at every positive tolerance. -/
theorem anchoredProcessLifetime_tolerance_tail_moment (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 < ε) {p : ℝ} (hp : 0 < p) :
    (∫ ω, (anchoredProcessLifetime B ε ω).toReal ^ p ∂μ) =
      p * ∫ t in Ioi (0 : ℝ), t ^ (p - 1) *
        μ.real {ω | ENNReal.ofReal t < anchoredProcessLifetime B ε ω} := by
  let : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have h := integrable_rpow_tail_identity
    (aemeasurable_anchoredProcessLifetime hB ε).ennreal_toReal
    (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) hp
    (anchoredProcessLifetime_tolerance_integrable_rpow hB hε hp.le)
  rw [h.2]
  congr 1
  apply integral_congr_ae
  filter_upwards [self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
    with t ht
  rw [Measure.real, Measure.real,
    measure_strict_tail_toReal_eq (anchoredProcessLifetime_tolerance_ae_ne_top hB hε) ht.le]

theorem identDistrib_optimalLifetime_toReal_tolerance (hB : IsBrownianReal B μ) {ε : ℝ} (hε : 0 < ε) :
    IdentDistrib (fun ω => (optimalProcessLifetime B ε ω).toReal)
      (fun ω => ε ^ 2 * optimalUnitLifetime B ω) μ μ := by
  simpa only [Function.comp_def, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hε.le, optimalUnitLifetime] using!
    (identDistrib_optimalLifetime_tolerance hB hε).comp ENNReal.measurable_toReal

/-- Finiteness at arbitrary positive tolerance is transferred before passing to real values. -/
theorem optimalProcessLifetime_tolerance_ae_ne_top (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 < ε) : ∀ᵐ ω ∂μ, optimalProcessLifetime B ε ω ≠ ∞ := by
  apply (identDistrib_optimalLifetime_tolerance hB hε).symm.ae_snd (measurableSet_singleton ∞).compl
  filter_upwards [optimalProcessLifetime_ae_ne_top hB] with ω hω
  exact ENNReal.mul_ne_top (by simp) hω

theorem optimalProcessLifetime_tolerance_memLp (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 < ε) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun ω => (optimalProcessLifetime B ε ω).toReal) p μ :=
  (identDistrib_optimalLifetime_toReal_tolerance hB hε).symm.memLp_snd
    ((optimalUnitLifetime_memLp hB p hp).const_mul (ε ^ 2))

theorem optimalProcessLifetime_tolerance_integrable_rpow (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 < ε) {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun ω => (optimalProcessLifetime B ε ω).toReal ^ p) μ := by
  have hlaw := (identDistrib_optimalLifetime_toReal_tolerance hB hε).comp (measurable_id.pow_const p)
  apply hlaw.symm.integrable_snd
  have hi := (optimalUnitLifetime_integrable_rpow hB hp).const_mul ((ε ^ 2) ^ p)
  simpa only [Function.comp_def, id_eq, Real.mul_rpow (sq_nonneg ε) (optimalUnitLifetime_nonnegative B _)] using hi

theorem optimalProcessLifetime_tolerance_integrable_pow (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    Integrable (fun ω => (optimalProcessLifetime B ε ω).toReal ^ n) μ := by
  simpa only [Real.rpow_natCast] using optimalProcessLifetime_tolerance_integrable_rpow hB hε
    (show (0 : ℝ) ≤ n by positivity)

theorem optimalProcessLifetime_tolerance_exp_neighborhood (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ t : ℝ, |t| ≤ θ →
      Integrable (fun ω => Real.exp (t * (optimalProcessLifetime B ε ω).toReal)) μ := by
  obtain ⟨θ, hθ, hint⟩ := optimalUnitLifetime_exp_neighborhood hB
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  refine ⟨θ / ε ^ 2, div_pos hθ hεsq, fun t ht => ?_⟩
  have hrate : |t * ε ^ 2| ≤ θ := by
    rw [abs_mul, abs_of_nonneg hεsq.le]
    exact (le_div_iff₀ hεsq).mp ht
  have hlaw := (identDistrib_optimalLifetime_toReal_tolerance hB hε).comp
    (by fun_prop : Measurable (fun x : ℝ => Real.exp (t * x)))
  apply hlaw.symm.integrable_snd
  simpa only [Function.comp_def, mul_assoc] using! hint (t * ε ^ 2) hrate

/-- Real-order raw moments scale by the corresponding power of the tolerance squared. -/
theorem optimalProcessLifetime_tolerance_moment_scaling (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 < ε) {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun ω => (optimalProcessLifetime B ε ω).toReal ^ p) μ ∧
      (∫ ω, (optimalProcessLifetime B ε ω).toReal ^ p ∂μ) =
        (ε ^ 2) ^ p * ∫ ω, optimalUnitLifetime B ω ^ p ∂μ := by
  refine ⟨optimalProcessLifetime_tolerance_integrable_rpow hB hε hp, ?_⟩
  have hlaw := (identDistrib_optimalLifetime_toReal_tolerance hB hε).comp (measurable_id.pow_const p)
  calc
    (∫ ω, (optimalProcessLifetime B ε ω).toReal ^ p ∂μ) =
        ∫ ω, (ε ^ 2 * optimalUnitLifetime B ω) ^ p ∂μ := hlaw.integral_eq
    _ = (ε ^ 2) ^ p * ∫ ω, optimalUnitLifetime B ω ^ p ∂μ := by
      simp_rw [Real.mul_rpow (sq_nonneg ε) (optimalUnitLifetime_nonnegative B _), integral_const_mul]

/-- The real-order tail identity remains valid at every positive tolerance. -/
theorem optimalProcessLifetime_tolerance_tail_moment (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 < ε) {p : ℝ} (hp : 0 < p) :
    (∫ ω, (optimalProcessLifetime B ε ω).toReal ^ p ∂μ) =
      p * ∫ t in Ioi (0 : ℝ), t ^ (p - 1) *
        μ.real {ω | ENNReal.ofReal t < optimalProcessLifetime B ε ω} := by
  let : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have h := integrable_rpow_tail_identity
    (aemeasurable_optimalProcessLifetime hB ε).ennreal_toReal
    (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) hp
    (optimalProcessLifetime_tolerance_integrable_rpow hB hε hp.le)
  rw [h.2]
  congr 1
  apply integral_congr_ae
  filter_upwards [self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
    with t ht
  rw [Measure.real, Measure.real,
    measure_strict_tail_toReal_eq (optimalProcessLifetime_tolerance_ae_ne_top hB hε) ht.le]

end BrownianAffine
