import PLAStochastic.Affine.Process.PathLaw.PathSpace
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Cancelling the Gaussian endpoint density

The actual bridge is independent of the actual normal endpoint. For every
nonnegative Borel functional on continuous paths, integration over bridge
slopes equals Brownian expectation weighted by the reciprocal normal density.
All equalities are in ENNReal, before any finiteness assertion is needed.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace BrownianAffine

noncomputable section
set_option backward.isDefEq.respectTransparency false

def gaussianEndpointWeight (z : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt (2 * Real.pi) * Real.exp (z ^ 2 / 2))

theorem measurable_gaussianEndpointWeight : Measurable gaussianEndpointWeight := by
  unfold gaussianEndpointWeight
  fun_prop

theorem gaussianPDF_mul_endpointWeight (z : ℝ) :
    gaussianPDF 0 1 z * gaussianEndpointWeight z = 1 := by
  change ENNReal.ofReal (gaussianPDFReal 0 1 z) *
    ENNReal.ofReal (Real.sqrt (2 * Real.pi) * Real.exp (z ^ 2 / 2)) = 1
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 1 z)]
  have hs : Real.sqrt (2 * Real.pi) ≠ 0 :=
    (Real.sqrt_pos.2 (mul_pos two_pos Real.pi_pos)).ne'
  have he : gaussianPDFReal 0 1 z *
      (Real.sqrt (2 * Real.pi) * Real.exp (z ^ 2 / 2)) = 1 := by
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, neg_div]
    calc
      _ = (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (2 * Real.pi) *
          (Real.exp (-(z ^ 2 / 2)) * Real.exp (z ^ 2 / 2)) := by ring
      _ = 1 := by rw [inv_mul_cancel₀ hs, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  rw [he, ENNReal.ofReal_one]

theorem measurable_add_endpoint_path :
    Measurable (fun p : Path 1 × ℝ => p.1 + p.2 • timePath 1) := by fun_prop

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The endpoint density cancellation used in the ordinary-Brownian moment formula. -/
theorem brownian_bridge_endpoint_lintegral (hB : IsBrownianReal B μ)
    {Φ : Path 1 → ℝ≥0∞} (hΦ : Measurable Φ) :
    (∫⁻ y : ℝ, ∫⁻ ω, Φ (bridgeUnitPath B ω + y • timePath 1) ∂μ) =
      ∫⁻ ω, gaussianEndpointWeight (B 1 ω) * Φ (unitPath (processPath B ω) 1) ∂μ := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hb := aemeasurable_bridgeUnitPath hB
  have hz := hB.aemeasurable 1
  let F : Path 1 × ℝ → ℝ≥0∞ := fun p =>
    gaussianEndpointWeight p.2 * Φ (p.1 + p.2 • timePath 1)
  have hF : Measurable F :=
    (measurable_gaussianEndpointWeight.comp measurable_snd).mul
      (hΦ.comp measurable_add_endpoint_path)
  have hG : Measurable (fun p : Path 1 × ℝ => Φ (p.1 + p.2 • timePath 1)) :=
    hΦ.comp measurable_add_endpoint_path
  have hmap : μ.map (fun ω => (bridgeUnitPath B ω, B 1 ω)) =
      (μ.map (bridgeUnitPath B)).prod (gaussianReal 0 1) := by
    rw [(bridgeUnitPath_indep_endpoint hB).map_prod_eq_prod_map_map hb hz,
      (brownian_endpoint_standard_normal hB.toIsPreBrownianReal).map_eq]
  symm
  calc
    (∫⁻ ω, gaussianEndpointWeight (B 1 ω) * Φ (unitPath (processPath B ω) 1) ∂μ) =
        ∫⁻ ω, F (bridgeUnitPath B ω, B 1 ω) ∂μ := by
      apply lintegral_congr
      intro ω
      rw [brownianUnitPath_eq_bridge_add_endpoint]
    _ = ∫⁻ p, F p ∂(μ.map (bridgeUnitPath B)).prod (gaussianReal 0 1) := by
      rw [← hmap]
      exact (lintegral_map' hF.aemeasurable (hb.prodMk hz)).symm
    _ = ∫⁻ g, ∫⁻ z, F (g, z) ∂gaussianReal 0 1 ∂μ.map (bridgeUnitPath B) :=
      lintegral_prod F hF.aemeasurable
    _ = ∫⁻ g, ∫⁻ z : ℝ, Φ (g + z • timePath 1) ∂volume ∂μ.map (bridgeUnitPath B) := by
      apply lintegral_congr
      intro g
      have hFg : Measurable (fun z : ℝ => F (g, z)) := hF.comp measurable_prodMk_left
      rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0),
        lintegral_withDensity_eq_lintegral_mul volume (measurable_gaussianPDF 0 1)
          hFg]
      apply lintegral_congr
      intro z
      change gaussianPDF 0 1 z * (gaussianEndpointWeight z * Φ (g + z • timePath 1)) = _
      rw [← mul_assoc, gaussianPDF_mul_endpointWeight, one_mul]
    _ = ∫⁻ z, ∫⁻ g, Φ (g + z • timePath 1) ∂μ.map (bridgeUnitPath B) :=
      lintegral_lintegral_swap hG.aemeasurable
    _ = ∫⁻ z, ∫⁻ ω, Φ (bridgeUnitPath B ω + z • timePath 1) ∂μ := by
      apply lintegral_congr
      intro z
      exact lintegral_map' (hG.comp measurable_prodMk_right).aemeasurable hb

end

end BrownianAffine
