import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-! Integration of a function of the sum over the positive quadrant. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- Translation of the positive half-line for an extended nonnegative integrand. -/
theorem lintegral_Ioi_translate (d : ℝ) (f : ℝ → ℝ≥0∞) :
    (∫⁻ t in Ioi (0 : ℝ), f (d + t)) = ∫⁻ u in Ioi d, f u := by
  rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi]
  convert lintegral_add_left_eq_self (μ := (volume : Measure ℝ)) ((Ioi d).indicator f) d using 1
  congr 1
  funext t
  simp only [indicator_apply, mem_Ioi]
  by_cases h : 0 < t
  · simp [h, show d < d + t by linarith]
  · simp [h, show ¬d < d + t by linarith]

/-- Tonelli's identity on the positive quadrant, with no finiteness assumption. -/
theorem lintegral_Ioi_add_eq_weighted {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ s in Ioi (0 : ℝ), ∫⁻ t in Ioi (0 : ℝ), f (s + t)) =
      ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal u * f u := by
  let ρ := (volume.restrict (Ioi (0 : ℝ))).withDensity f
  have hn : 0 ≤ᵐ[ρ] (fun u : ℝ => u) := by
    apply (withDensity_absolutelyContinuous _ _).ae_le
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact le_of_lt hu
  have hc := lintegral_eq_lintegral_meas_lt ρ hn measurable_id.aemeasurable
  rw [lintegral_withDensity_eq_lintegral_mul _ hf ENNReal.measurable_ofReal] at hc
  simp only [Pi.mul_apply, mul_comm (f _) (ENNReal.ofReal _)] at hc
  rw [hc]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro s hs
  dsimp only
  rw [lintegral_Ioi_translate]
  change _ = (volume.restrict (Ioi (0 : ℝ))).withDensity f (Ioi s)
  have hi : Ioi s ∩ Ioi (0 : ℝ) = Ioi s := by
    apply inter_eq_left.mpr
    intro u hu
    change 0 < u
    exact lt_trans hs hu
  rw [withDensity_apply _ measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi, hi]

/-- The product-measure form of the positive quadrant identity. -/
theorem lintegral_positiveQuadrant_add_eq_weighted {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ p : ℝ × ℝ, f (p.1 + p.2)
      ∂(volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) =
      ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal u * f u := by
  calc
    _ = ∫⁻ s in Ioi (0 : ℝ), ∫⁻ t in Ioi (0 : ℝ), f (s + t) :=
      lintegral_prod _ (hf.comp (measurable_fst.add measurable_snd)).aemeasurable
    _ = _ := lintegral_Ioi_add_eq_weighted hf

/-- Absolute integrability on the quadrant is exactly weighted half-line integrability.
The real function may have either sign. -/
theorem integrable_positiveQuadrant_add_iff {f : ℝ → ℝ} (hf : Measurable f) :
    Integrable (fun p : ℝ × ℝ => f (p.1 + p.2))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) ↔
      IntegrableOn (fun u => u * f u) (Ioi (0 : ℝ)) := by
  have hp : AEStronglyMeasurable (fun p : ℝ × ℝ => f (p.1 + p.2))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    (hf.comp (measurable_fst.add measurable_snd)).aestronglyMeasurable
  have hw : AEStronglyMeasurable (fun u => u * f u) (volume.restrict (Ioi (0 : ℝ))) :=
    (measurable_id.mul hf).aestronglyMeasurable
  simp only [IntegrableOn, Integrable, hp, hw, true_and, HasFiniteIntegral]
  rw [lintegral_positiveQuadrant_add_eq_weighted hf.enorm]
  have he : (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal u * ‖f u‖ₑ) =
      ∫⁻ u in Ioi (0 : ℝ), ‖u * f u‖ₑ := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro u hu
    dsimp only
    rw [enorm_mul, Real.enorm_eq_ofReal (le_of_lt hu)]
  rw [he]

/-- A real nonnegative integrand has the same total product integral as its weighted integral. -/
theorem integral_positiveQuadrant_add_eq_weighted {f : ℝ → ℝ} (hf : Measurable f)
    (hn : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ f u) :
    (∫ p : ℝ × ℝ, f (p.1 + p.2)
      ∂(volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) =
      ∫ u in Ioi (0 : ℝ), u * f u := by
  have hp : 0 ≤ᵐ[(volume.restrict (Ioi (0 : ℝ))).prod
      (volume.restrict (Ioi (0 : ℝ)))] (fun p : ℝ × ℝ => f (p.1 + p.2)) := by
    apply (ae_prod_iff_ae_ae (measurableSet_le measurable_const
      (hf.comp (measurable_fst.add measurable_snd)))).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    apply hn (s + t)
    change 0 < s + t
    exact add_pos hs ht
  have hw : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] (fun u => u * f u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (le_of_lt hu) (hn u hu)
  rw [integral_eq_lintegral_of_nonneg_ae hp
      (hf.comp (measurable_fst.add measurable_snd)).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae hw (measurable_id.mul hf).aestronglyMeasurable,
    lintegral_positiveQuadrant_add_eq_weighted hf.ennreal_ofReal]
  congr 1
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro u hu
  dsimp only
  rw [ENNReal.ofReal_mul (le_of_lt hu)]

/-- The product identity also holds for signed real functions under absolute integrability. -/
theorem integral_positiveQuadrant_add_eq_weighted_signed {f : ℝ → ℝ} (hf : Measurable f)
    (hi : IntegrableOn (fun u => u * f u) (Ioi (0 : ℝ))) :
    (∫ p : ℝ × ℝ, f (p.1 + p.2)
      ∂(volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) =
      ∫ u in Ioi (0 : ℝ), u * f u := by
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part
      ((integrable_positiveQuadrant_add_iff hf).mpr hi),
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi,
    lintegral_positiveQuadrant_add_eq_weighted hf.ennreal_ofReal,
    lintegral_positiveQuadrant_add_eq_weighted
      (f := fun u => ENNReal.ofReal (-f u)) hf.neg.ennreal_ofReal]
  congr 1 <;> congr 1
  · apply setLIntegral_congr_fun measurableSet_Ioi
    intro u hu
    dsimp only
    rw [ENNReal.ofReal_mul (le_of_lt hu)]
  · apply setLIntegral_congr_fun measurableSet_Ioi
    intro u hu
    dsimp only
    rw [← mul_neg, ENNReal.ofReal_mul (le_of_lt hu)]

/-- Fubini gives the signed iterated identity from the weighted absolute integrability. -/
theorem integral_Ioi_add_eq_weighted_signed {f : ℝ → ℝ} (hf : Measurable f)
    (hi : IntegrableOn (fun u => u * f u) (Ioi (0 : ℝ))) :
    (∫ s in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), f (s + t)) =
      ∫ u in Ioi (0 : ℝ), u * f u := by
  rw [← integral_prod _ ((integrable_positiveQuadrant_add_iff hf).mpr hi)]
  exact integral_positiveQuadrant_add_eq_weighted_signed hf hi

/-- The nonnegative iterated integral identity follows with genuine product integrability. -/
theorem integral_Ioi_add_eq_weighted {f : ℝ → ℝ} (hf : Measurable f)
    (hn : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ f u)
    (hi : IntegrableOn (fun u => u * f u) (Ioi (0 : ℝ))) :
    (∫ s in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), f (s + t)) =
      ∫ u in Ioi (0 : ℝ), u * f u := by
  rw [← integral_prod _ ((integrable_positiveQuadrant_add_iff hf).mpr hi)]
  exact integral_positiveQuadrant_add_eq_weighted hf hn

end BrownianAffine
