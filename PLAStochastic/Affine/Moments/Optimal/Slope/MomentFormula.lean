import PLAStochastic.Affine.Moments.Optimal.Slope.Measurability
import PLAStochastic.Affine.Process.PathLaw.EndpointDensity
import PLAStochastic.Affine.Error.Positivity
import PLAStochastic.Affine.Lifetime.UnitMoments
import PLAStochastic.Affine.Lifetime.InverseErrorLaw

/-!
# Actual optimal Brownian moments from integration over slopes

The deterministic coarea formula and Gaussian endpoint density cancellation are
combined for the actual continuous Brownian path. Finiteness follows from the
already proved lifetime moments, rather than an assumption on the exponentially
weighted slope integrand.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace BrownianAffine

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The real inverse-error power law retains the genuine lifetime as its left side. -/
theorem identDistrib_optimalUnitLifetime_rpow_error (hB : IsBrownianReal B μ) (q : ℝ) :
    IdentDistrib (fun ω => optimalUnitLifetime B ω ^ q)
      (fun ω => optimalProcessError B 1 ω ^ (-2 * q)) μ μ := by
  have hi := (identDistrib_optimalLifetime_unit hB).comp
    (by fun_prop : Measurable (fun z : ℝ≥0∞ => z.toReal ^ q))
  have he : (fun ω => (((ENNReal.ofReal (optimalProcessError B 1 ω)) ^ 2)⁻¹).toReal ^ q) =
      (fun ω => optimalProcessError B 1 ω ^ (-2 * q)) := by
    funext ω
    have hd : 0 ≤ optimalProcessError B 1 ω := bestError_nonneg _ _
    rw [ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofReal hd,
      ← Real.rpow_neg_eq_inv_rpow, ← Real.rpow_natCast_mul hd]
    congr 1
    norm_num
  simpa only [Function.comp_def, optimalUnitLifetime, he] using! hi

theorem optimalUnitLifetime_moment_eq_inverse_error (hB : IsBrownianReal B μ) (q : ℝ) :
    (∫ ω, optimalUnitLifetime B ω ^ q ∂μ) =
      ∫ ω, optimalProcessError B 1 ω ^ (-2 * q) ∂μ :=
  (identDistrib_optimalUnitLifetime_rpow_error hB q).integral_eq

theorem optimalProcessError_integrable_inverse_rpow (hB : IsBrownianReal B μ)
    {q : ℝ} (hq : 0 ≤ q) : Integrable (fun ω => optimalProcessError B 1 ω ^ (-2 * q)) μ :=
  (identDistrib_optimalUnitLifetime_rpow_error hB q).integrable_iff.mp
    (optimalUnitLifetime_integrable_rpow hB hq)

private theorem bridge_drift_lintegral_swap (hB : IsBrownianReal B μ) (q : ℝ) :
    (∫⁻ ω, ∫⁻ y : ℝ, slopeWeightENNReal q (bridgeUnitPath B ω + y • timePath 1) ∂volume ∂μ) =
      ∫⁻ y : ℝ, ∫⁻ ω, slopeWeightENNReal q (bridgeUnitPath B ω + y • timePath 1) ∂μ := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hG : Measurable (fun p : Path 1 × ℝ =>
      slopeWeightENNReal q (p.1 + p.2 • timePath 1)) :=
    (measurable_slopeWeightENNReal q).comp measurable_add_endpoint_path
  have hb := aemeasurable_bridgeUnitPath hB
  have hm : Measurable (fun g : Path 1 =>
      ∫⁻ y : ℝ, slopeWeightENNReal q (g + y • timePath 1)) :=
    hG.lintegral_prod_right
  calc
    (∫⁻ ω, ∫⁻ y : ℝ, slopeWeightENNReal q (bridgeUnitPath B ω + y • timePath 1) ∂volume ∂μ) =
        ∫⁻ g, ∫⁻ y : ℝ, slopeWeightENNReal q (g + y • timePath 1) ∂volume
          ∂μ.map (bridgeUnitPath B) := (lintegral_map' hm.aemeasurable hb).symm
    _ = ∫⁻ y : ℝ, ∫⁻ g, slopeWeightENNReal q (g + y • timePath 1)
        ∂μ.map (bridgeUnitPath B) := lintegral_lintegral_swap hG.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro y
      exact lintegral_map' (hG.comp measurable_prodMk_right).aemeasurable hb

/-- Coarea is applied on the almost-sure set of genuinely nonaffine bridge paths,
then Tonelli and independence cancel the Gaussian endpoint density. -/
theorem optimal_inverse_error_lintegral_slopeWeight (hB : IsBrownianReal B μ)
    {q : ℝ} (hq : 0 < q) :
    (∫⁻ ω, ENNReal.ofReal (optimalProcessError B 1 ω ^ (-2 * q)) ∂μ) =
      ENNReal.ofReal ((2 : ℝ) ^ (2 * q) * q) *
        ∫⁻ ω, gaussianEndpointWeight (B 1 ω) *
          slopeWeightENNReal q (unitPath (processPath B ω) 1) ∂μ := by
  calc
    (∫⁻ ω, ENNReal.ofReal (optimalProcessError B 1 ω ^ (-2 * q)) ∂μ) =
        ∫⁻ ω, ENNReal.ofReal ((2 : ℝ) ^ (2 * q) * q) *
          (∫⁻ y : ℝ, slopeWeightENNReal q (bridgeUnitPath B ω + y • timePath 1)) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [bridge_slopeMinimum_positive_ae hB] with ω hω
      simpa only [optimalError_bridgeUnitPath] using!
        slopeWeight_drift_lintegral (bridgeUnitPath B ω) hω hq
    _ = ENNReal.ofReal ((2 : ℝ) ^ (2 * q) * q) *
        (∫⁻ ω, ∫⁻ y : ℝ, slopeWeightENNReal q (bridgeUnitPath B ω + y • timePath 1) ∂volume ∂μ) :=
      lintegral_const_mul' (μ := μ) (ENNReal.ofReal ((2 : ℝ) ^ (2 * q) * q))
        (fun ω => ∫⁻ y : ℝ, slopeWeightENNReal q (bridgeUnitPath B ω + y • timePath 1))
        ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal ((2 : ℝ) ^ (2 * q) * q) *
        (∫⁻ y : ℝ, ∫⁻ ω, slopeWeightENNReal q (bridgeUnitPath B ω + y • timePath 1) ∂μ) := by
      exact congrArg (fun z => ENNReal.ofReal ((2 : ℝ) ^ (2 * q) * q) * z)
        (bridge_drift_lintegral_swap hB q)
    _ = _ := congrArg (fun z => ENNReal.ofReal ((2 : ℝ) ^ (2 * q) * q) * z)
      (brownian_bridge_endpoint_lintegral hB (measurable_slopeWeightENNReal q))

/-- The ordinary-Brownian integrand, with the constant Gaussian normalization outside. -/
def brownianSlopeIntegrand (q : ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ :=
  Real.exp (B 1 ω ^ 2 / 2) * slopeWeight q (unitPath (processPath B ω) 1)

omit [MeasurableSpace Ω] in
theorem brownianSlopeIntegrand_nonnegative (q : ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    0 ≤ brownianSlopeIntegrand q B ω :=
  mul_nonneg (Real.exp_nonneg _) (slopeWeight_nonnegative _ _)

theorem aemeasurable_brownianSlopeIntegrand (hB : IsBrownianReal B μ) (q : ℝ) :
    AEMeasurable (brownianSlopeIntegrand q B) μ := by
  have he : AEMeasurable (fun ω => Real.exp (B 1 ω ^ 2 / 2)) μ :=
    (by fun_prop : Measurable (fun z : ℝ => Real.exp (z ^ 2 / 2))).comp_aemeasurable
      (hB.aemeasurable 1)
  exact he.mul ((measurable_slopeWeight q).comp_aemeasurable (aemeasurable_brownianUnitPath hB 1))

theorem optimal_inverse_error_lintegral_slopeIntegrand (hB : IsBrownianReal B μ)
    {q : ℝ} (hq : 0 < q) :
    (∫⁻ ω, ENNReal.ofReal (optimalProcessError B 1 ω ^ (-2 * q)) ∂μ) =
      ENNReal.ofReal ((2 : ℝ) ^ (2 * q) * q * Real.sqrt (2 * Real.pi)) *
        ∫⁻ ω, ENNReal.ofReal (brownianSlopeIntegrand q B ω) ∂μ := by
  have he (ω : Ω) : gaussianEndpointWeight (B 1 ω) *
      slopeWeightENNReal q (unitPath (processPath B ω) 1) =
      ENNReal.ofReal (Real.sqrt (2 * Real.pi)) *
        ENNReal.ofReal (brownianSlopeIntegrand q B ω) := by
    unfold gaussianEndpointWeight slopeWeightENNReal brownianSlopeIntegrand
    rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _),
      ENNReal.ofReal_mul (Real.exp_nonneg _), mul_assoc]
  rw [optimal_inverse_error_lintegral_slopeWeight hB hq]
  simp_rw [he]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity)]

/-- Finiteness of the exponential weight follows from actual lifetime moments and coarea. -/
theorem integrable_brownianSlopeIntegrand (hB : IsBrownianReal B μ)
    {q : ℝ} (hq : 0 < q) : Integrable (brownianSlopeIntegrand q B) μ := by
  have hi := optimalProcessError_integrable_inverse_rpow hB hq.le
  have hn : 0 ≤ᵐ[μ] (fun ω => optimalProcessError B 1 ω ^ (-2 * q)) :=
    Eventually.of_forall fun ω => Real.rpow_nonneg (bestError_nonneg _ _) _
  have hf := (lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable hn).mpr hi
  rw [optimal_inverse_error_lintegral_slopeIntegrand hB hq] at hf
  have hc : 0 < (2 : ℝ) ^ (2 * q) * q * Real.sqrt (2 * Real.pi) := by
    positivity
  have hj := ENNReal.lt_top_of_mul_ne_top_right hf (ENNReal.ofReal_pos.mpr hc).ne'
  exact (lintegral_ofReal_ne_top_iff_integrable
    (aemeasurable_brownianSlopeIntegrand hB q).aestronglyMeasurable
    (Eventually.of_forall (brownianSlopeIntegrand_nonnegative q B))).mp hj.ne

/-- The actual optimal lifetime moment, in the ordinary-Brownian derivative-of-range form. -/
theorem optimalUnitLifetime_moment_slope_integral (hB : IsBrownianReal B μ)
    {q : ℝ} (hq : 0 < q) :
    (∫ ω, optimalUnitLifetime B ω ^ q ∂μ) =
      (2 : ℝ) ^ (2 * q) * q * Real.sqrt (2 * Real.pi) *
        ∫ ω, brownianSlopeIntegrand q B ω ∂μ := by
  rw [optimalUnitLifetime_moment_eq_inverse_error hB q]
  have hi := optimalProcessError_integrable_inverse_rpow hB hq.le
  have hn : 0 ≤ᵐ[μ] (fun ω => optimalProcessError B 1 ω ^ (-2 * q)) :=
    Eventually.of_forall fun ω => Real.rpow_nonneg (bestError_nonneg _ _) _
  rw [integral_eq_lintegral_of_nonneg_ae hn hi.aestronglyMeasurable,
    optimal_inverse_error_lintegral_slopeIntegrand hB hq, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity),
    integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall (brownianSlopeIntegrand_nonnegative q B))
      (aemeasurable_brownianSlopeIntegrand hB q).aestronglyMeasurable]

end BrownianAffine
