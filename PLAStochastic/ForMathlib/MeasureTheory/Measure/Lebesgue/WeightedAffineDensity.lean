import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Explicit densities for weighted affine sections

The weight may depend on every coordinate, including the coordinate used for
the change of variables. This retains the active-facet selector in the exact
density formula, without an independence assumption on that selector.
-/

namespace PGM
noncomputable section
open MeasureTheory Set
open scoped ENNReal

theorem kernel_map_volume_affine {a : ℝ} (ha : a ≠ 0) (b : ℝ) :
    (volume : Measure ℝ).map (fun x => a * x + b) =
      ENNReal.ofReal |a⁻¹| • volume := by
  have he : (volume : Measure ℝ).map (fun x => a * x + b) =
      ((volume : Measure ℝ).map (fun x => a * x)).map (fun x => x + b) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [he, Real.map_volume_mul_left ha, Measure.map_smul,
    (measurePreserving_add_right volume b).map_eq]

theorem kernel_lintegral_affine_inverse {a : ℝ} (ha : a ≠ 0) (b : ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, f x) = ENNReal.ofReal |a⁻¹| * ∫⁻ z, f ((z - b) / a) := by
  have hh := lintegral_map (μ := (volume : Measure ℝ))
    (f := fun z => f ((z - b) / a)) (g := fun x => a * x + b)
    (hf.comp (by fun_prop)) (by fun_prop)
  rw [kernel_map_volume_affine ha, lintegral_smul_measure] at hh
  simpa only [add_sub_cancel_right, mul_div_cancel_left₀ _ ha, smul_eq_mul] using hh.symm

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The one-coordinate Jacobian and Tonelli's theorem, retaining the full
weight instead of replacing it by a marginal expectation. -/
theorem kernel_weighted_affine_lintegral (P : Measure Ω) [SFinite P]
    {a : ℝ} (ha : a ≠ 0) {b : Ω → ℝ} (hb : Measurable b)
    {F : Ω × ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ p, F p ∂P.prod volume) =
      ∫⁻ z, ENNReal.ofReal |a⁻¹| * ∫⁻ ω, F (ω, (z - b ω) / a) ∂P := by
  rw [lintegral_prod _ hF.aemeasurable]
  have hs (ω : Ω) := kernel_lintegral_affine_inverse ha (b ω)
    (f := fun z => F (ω, z)) (by fun_prop)
  simp_rw [hs]
  simp_rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [lintegral_lintegral_swap (by fun_prop)]

/-- The explicit density of an arbitrary weighted affine root. -/
def kernelLinearDensity (P : Measure Ω) (a : ℝ) (b : Ω → ℝ)
    (W : Ω × ℝ → ℝ≥0∞) (z : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal |a⁻¹| * ∫⁻ ω, W (ω, (z - b ω) / a) ∂P

theorem measurable_kernelLinearDensity (P : Measure Ω) [SFinite P]
    (a : ℝ) {b : Ω → ℝ} (hb : Measurable b)
    {W : Ω × ℝ → ℝ≥0∞} (hW : Measurable W) :
    Measurable (kernelLinearDensity P a b W) := by
  have hm : Measurable (fun p : ℝ × Ω => W (p.2, (p.1 - b p.2) / a)) := by fun_prop
  exact measurable_const.mul hm.lintegral_prod_right'

/-- Exact weighted pushforward law. Neither the active selector nor the input
density is differentiated, and the formula remains valid for infinite mass. -/
theorem kernel_weighted_affine_map_density (P : Measure Ω) [SFinite P]
    {a : ℝ} (ha : a ≠ 0) {b : Ω → ℝ} (hb : Measurable b)
    {W : Ω × ℝ → ℝ≥0∞} (hW : Measurable W) :
    ((P.prod volume).withDensity W).map (fun p => b p.1 + a * p.2) =
      volume.withDensity (kernelLinearDensity P a b W) := by
  have hmap : Measurable (fun p : Ω × ℝ => b p.1 + a * p.2) := by fun_prop
  refine Measure.ext_of_lintegral _ fun φ hφ => ?_
  have hφmap : Measurable (fun p : Ω × ℝ => φ (b p.1 + a * p.2)) := by fun_prop
  rw [lintegral_map hφ hmap,
    lintegral_withDensity_eq_lintegral_mul _ hW hφmap,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_kernelLinearDensity P a hb hW) hφ]
  simp only [Pi.mul_apply]
  have hF : Measurable (fun p : Ω × ℝ => W p * φ (b p.1 + a * p.2)) := by fun_prop
  rw [kernel_weighted_affine_lintegral P ha hb hF]
  apply lintegral_congr
  intro z
  dsimp only [kernelLinearDensity, Pi.mul_apply]
  have he (ω : Ω) : b ω + a * ((z - b ω) / a) = z := by field_simp; ring
  simp_rw [he]
  rw [lintegral_mul_const _ (show Measurable (fun ω => W (ω, (z - b ω) / a)) by fun_prop)]
  exact (mul_assoc _ _ _).symm

end
end PGM
