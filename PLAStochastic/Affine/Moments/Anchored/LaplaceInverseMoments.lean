import PLAStochastic.Affine.Error.Positivity
import PLAStochastic.Affine.Moments.Anchored.ExpandingStrip
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Inverse moments from the actual Laplace transform

The gamma integral and Tonelli's theorem give the inverse-moment formula
without assuming a closed form for the distribution or its transform.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace BrownianAffine

set_option backward.isDefEq.respectTransparency false

def laplaceENN (ν : Measure ℝ) (z : ℝ) : ℝ≥0∞ :=
  ∫⁻ s, ENNReal.ofReal (Real.exp (-(s * z))) ∂ν

theorem measurable_laplaceENN (ν : Measure ℝ) [SFinite ν] : Measurable (laplaceENN ν) := by
  apply Measurable.lintegral_prod_right
  fun_prop

theorem lintegral_gamma_kernel {q s : ℝ} (hq : 0 < q) (hs : 0 < s) :
    (∫⁻ z : ℝ in Ioi 0, ENNReal.ofReal (z ^ (q - 1) * Real.exp (-(s * z)))) =
      ENNReal.ofReal (Real.Gamma q) * ENNReal.ofReal (s ^ (-q)) := by
  have hi : IntegrableOn (fun z : ℝ => z ^ (q - 1) * Real.exp (-(s * z))) (Ioi 0) := by
    simpa only [Real.rpow_one, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := q - 1)
        (by linarith) (by norm_num) hs)
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun z : ℝ => z ^ (q - 1) * Real.exp (-(s * z))) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
    exact mul_nonneg (Real.rpow_nonneg hz.le _) (Real.exp_nonneg _)
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn,
    Real.integral_rpow_mul_exp_neg_mul_Ioi hq hs, one_div, Real.inv_rpow hs.le,
    ← Real.rpow_neg hs.le, mul_comm, ENNReal.ofReal_mul (Real.Gamma_pos_of_pos hq).le]

/-- Tonelli's identity is valid even when the inverse moment is infinite. -/
theorem gamma_mul_inverse_moment_lintegral (ν : Measure ℝ) [SFinite ν]
    (hν : ∀ᵐ s ∂ν, 0 < s) {q : ℝ} (hq : 0 < q) :
    ENNReal.ofReal (Real.Gamma q) * (∫⁻ s, ENNReal.ofReal (s ^ (-q)) ∂ν) =
      ∫⁻ z : ℝ in Ioi 0, ENNReal.ofReal (z ^ (q - 1)) * laplaceENN ν z := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc
    (∫⁻ s, ENNReal.ofReal (Real.Gamma q) * ENNReal.ofReal (s ^ (-q)) ∂ν) =
        ∫⁻ s, ∫⁻ z : ℝ in Ioi 0,
          ENNReal.ofReal (z ^ (q - 1) * Real.exp (-(s * z))) ∂volume ∂ν := by
      apply lintegral_congr_ae
      filter_upwards [hν] with s hs
      exact (lintegral_gamma_kernel hq hs).symm
    _ = ∫⁻ z : ℝ in Ioi 0, ∫⁻ s,
          ENNReal.ofReal (z ^ (q - 1) * Real.exp (-(s * z))) ∂ν := by
      apply lintegral_lintegral_swap
      apply Measurable.aemeasurable
      fun_prop
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
      simp only [ENNReal.ofReal_mul (Real.rpow_nonneg hz.le _)]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

def laplaceReal (ν : Measure ℝ) (z : ℝ) : ℝ := ∫ s, Real.exp (-(s * z)) ∂ν

theorem measurable_laplaceReal (ν : Measure ℝ) [SFinite ν] : Measurable (laplaceReal ν) := by
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.integral_prod_right
  apply Measurable.stronglyMeasurable
  fun_prop

theorem laplaceReal_nonneg (ν : Measure ℝ) (z : ℝ) : 0 ≤ laplaceReal ν z :=
  integral_nonneg (fun _ => Real.exp_nonneg _)

theorem laplace_integrable (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hν : ∀ᵐ s ∂ν, 0 < s) {z : ℝ} (hz : 0 ≤ z) :
    Integrable (fun s => Real.exp (-(s * z))) ν := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  filter_upwards [hν] with s hs
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hs.le hz))

theorem ofReal_laplaceReal (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hν : ∀ᵐ s ∂ν, 0 < s) {z : ℝ} (hz : 0 ≤ z) :
    ENNReal.ofReal (laplaceReal ν z) = laplaceENN ν z :=
  ofReal_integral_eq_lintegral_ofReal (laplace_integrable ν hν hz)
    (Eventually.of_forall (fun _ => Real.exp_nonneg _))

theorem inverse_moment_laplace_integral (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hν : ∀ᵐ s ∂ν, 0 < s) {q : ℝ} (hq : 0 < q)
    (hi : Integrable (fun s : ℝ => s ^ (-q)) ν) :
    IntegrableOn (fun z : ℝ => z ^ (q - 1) * laplaceReal ν z) (Ioi 0) ∧
      (∫ s : ℝ, s ^ (-q) ∂ν) = (Real.Gamma q)⁻¹ *
        ∫ z : ℝ in Ioi 0, z ^ (q - 1) * laplaceReal ν z := by
  have hn : 0 ≤ᵐ[ν] (fun s : ℝ => s ^ (-q)) :=
    hν.mono (fun _ hs => Real.rpow_nonneg hs.le _)
  have hm : Measurable (fun z : ℝ => z ^ (q - 1) * laplaceReal ν z) :=
    (measurable_id.pow_const _).mul (measurable_laplaceReal ν)
  have hgn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun z : ℝ => z ^ (q - 1) * laplaceReal ν z) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
    exact mul_nonneg (Real.rpow_nonneg hz.le _) (laplaceReal_nonneg ν z)
  have he : (∫⁻ z : ℝ in Ioi 0, ENNReal.ofReal (z ^ (q - 1) * laplaceReal ν z)) =
      ENNReal.ofReal (Real.Gamma q) * ENNReal.ofReal (∫ s : ℝ, s ^ (-q) ∂ν) := by
    rw [ofReal_integral_eq_lintegral_ofReal hi hn, gamma_mul_inverse_moment_lintegral ν hν hq]
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg hz.le _), ofReal_laplaceReal ν hν hz.le]
  have hgi : IntegrableOn (fun z : ℝ => z ^ (q - 1) * laplaceReal ν z) (Ioi 0) := by
    refine ⟨hm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hgn).mpr ?_⟩
    rw [he]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  refine ⟨hgi, ?_⟩
  have heR := congrArg ENNReal.toReal he
  rw [← integral_eq_lintegral_of_nonneg_ae hgn hm.aestronglyMeasurable,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.Gamma_pos_of_pos hq).le,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hn)] at heR
  rw [heR, ← mul_assoc, inv_mul_cancel₀ (Real.Gamma_pos_of_pos hq).ne', one_mul]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem realDriftedSum_positive_ae (hB : IsBrownianReal B μ) :
    ∀ᵐ ω ∂μ, 0 < realDriftedSum (B · ω) 1 := by
  have hp : ∀ᵐ ω ∂μ, 0 < (anchoredProcessError B 1 ω) ^ 2 :=
    (anchoredProcessError_unit_positive_ae hB).mono (fun _ h => sq_pos_of_pos h)
  have hh := (identDistrib_sq_anchoredError_half_realDriftedSum hB).ae_snd
    (p := fun x : ℝ => 0 < x) measurableSet_Ioi hp
  filter_upwards [hh] with ω hω
  linarith

theorem anchored_inverse_sum_moment (hB : IsBrownianReal B μ) {q : ℝ} (hq : 0 ≤ q) :
    Integrable (fun ω => realDriftedSum (B · ω) 1 ^ (-q)) μ ∧
      (∫ ω, anchoredUnitLifetime B ω ^ q ∂μ) =
        (2 : ℝ) ^ q * ∫ ω, realDriftedSum (B · ω) 1 ^ (-q) ∂μ := by
  have h := (identDistrib_anchoredLifetime_real_two_div_realDriftedSum hB).comp
    (measurable_id.pow_const q)
  have hi := h.integrable_snd (anchoredUnitLifetime_integrable_rpow hB hq)
  have he : (fun ω => (2 / realDriftedSum (B · ω) 1) ^ q) =ᵐ[μ]
      (fun ω => (2 : ℝ) ^ q * realDriftedSum (B · ω) 1 ^ (-q)) := by
    filter_upwards [realDriftedSum_positive_ae hB] with ω hω
    rw [Real.div_rpow (by norm_num) hω.le, Real.rpow_neg hω.le, div_eq_mul_inv]
  have hi' : Integrable (fun ω => (2 : ℝ) ^ q * realDriftedSum (B · ω) 1 ^ (-q)) μ :=
    hi.congr he
  have htwo : (2 : ℝ) ^ q ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) q).ne'
  refine ⟨(integrable_const_mul_iff (isUnit_iff_ne_zero.mpr htwo) _).mp hi', ?_⟩
  calc
    (∫ ω, anchoredUnitLifetime B ω ^ q ∂μ) = ∫ ω, (2 / realDriftedSum (B · ω) 1) ^ q ∂μ :=
      h.integral_eq
    _ = ∫ ω, (2 : ℝ) ^ q * realDriftedSum (B · ω) 1 ^ (-q) ∂μ := integral_congr_ae he
    _ = _ := integral_const_mul _ _

/-- The gamma-transform formula in the manuscript, for the actual dependent supremum sum.
The transform integrand is integrable as a consequence of the proved Brownian moments. -/
theorem anchoredUnitLifetime_moment_laplace_integral (hB : IsBrownianReal B μ)
    {q : ℝ} (hq : 0 < q) :
    IntegrableOn (fun z : ℝ => z ^ (q - 1) *
        ∫ ω, Real.exp (-(realDriftedSum (B · ω) 1 * z)) ∂μ) (Ioi 0) ∧
      (∫ ω, anchoredUnitLifetime B ω ^ q ∂μ) = (2 : ℝ) ^ q / Real.Gamma q *
        ∫ z : ℝ in Ioi 0, z ^ (q - 1) *
          ∫ ω, Real.exp (-(realDriftedSum (B · ω) 1 * z)) ∂μ := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  let S : Ω → ℝ := fun ω => realDriftedSum (B · ω) 1
  have hS : AEMeasurable S μ := aemeasurable_realDriftedSum hB
  have hν : ∀ᵐ s ∂μ.map S, 0 < s :=
    (ae_map_iff hS measurableSet_Ioi).mpr (realDriftedSum_positive_ae hB)
  have hi : Integrable (fun s : ℝ => s ^ (-q)) (μ.map S) :=
    (integrable_map_measure (by fun_prop) hS).mpr (anchored_inverse_sum_moment hB hq.le).1
  have h := inverse_moment_laplace_integral (μ.map S) hν hq hi
  have hl (z : ℝ) : laplaceReal (μ.map S) z =
      ∫ ω, Real.exp (-(realDriftedSum (B · ω) 1 * z)) ∂μ :=
    integral_map hS (by fun_prop)
  simp only [hl] at h
  refine ⟨h.1, ?_⟩
  have hm : (∫ s : ℝ, s ^ (-q) ∂μ.map S) =
      ∫ ω, realDriftedSum (B · ω) 1 ^ (-q) ∂μ := integral_map hS (by fun_prop)
  rw [(anchored_inverse_sum_moment hB hq.le).2, ← hm, h.2, div_eq_mul_inv, mul_assoc]

end BrownianAffine
