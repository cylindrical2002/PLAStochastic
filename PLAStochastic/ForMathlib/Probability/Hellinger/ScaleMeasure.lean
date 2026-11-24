import PLAStochastic.ForMathlib.Probability.Hellinger.LogCoordinates
import PLAStochastic.ForMathlib.Probability.Hellinger.RadonNikodym
import PLAStochastic.ForMathlib.MeasureTheory.Measure.Lebesgue.WeightedAffineDensity

/-! # Hellinger scale regularity of actual pushed-forward probability measures -/

set_option autoImplicit false

namespace ProbabilityTheory.HellingerDensity

noncomputable section

open MeasureTheory

theorem dilate_toMeasure (p : HellingerDensity (volume : Measure ℝ))
    {a : ℝ} (ha : 0 < a) :
    (p.dilate a ha).toMeasure = p.toMeasure.map (fun x => a * x) := by
  symm
  refine Measure.ext_of_lintegral _ fun φ hφ => ?_
  have hm : Measurable (fun x => a * x) := measurable_const.mul measurable_id
  have hmφ : Measurable (fun x => φ (a * x)) := hφ.comp hm
  rw [lintegral_map hφ hm, toMeasure, toMeasure,
    lintegral_withDensity_eq_lintegral_mul _ p.measurable.ennreal_ofReal hmφ,
    lintegral_withDensity_eq_lintegral_mul _ (p.dilate a ha).measurable.ennreal_ofReal hφ]
  have h := PGM.kernel_lintegral_affine_inverse ha.ne' 0
    (f := fun x => ENNReal.ofReal (p.density x) * φ (a * x))
    (p.measurable.ennreal_ofReal.mul (hφ.comp hm))
  simp only [sub_zero, mul_div_cancel₀ _ ha.ne'] at h
  dsimp only [Pi.mul_apply]
  rw [h, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro x
  change ENNReal.ofReal |a⁻¹| * (ENNReal.ofReal (p.density (x / a)) * φ x) =
    ENNReal.ofReal (p.density (x / a) / a) * φ x
  rw [abs_inv, abs_of_pos ha, ENNReal.ofReal_inv_of_pos ha,
    ENNReal.ofReal_div_of_pos ha]
  simp only [div_eq_mul_inv]
  ac_rfl

theorem measureHellinger_map_mul_le_density
    (p : HellingerDensity (volume : Measure ℝ)) {a : ℝ} (ha : 0 < a) :
    let : IsProbabilityMeasure (p.toMeasure.map (fun x => a * x)) :=
      Measure.isProbabilityMeasure_map (measurable_const.mul measurable_id).aemeasurable
    measureHellinger (p.toMeasure.map (fun x => a * x)) p.toMeasure ≤
      (p.dilate a ha).hellinger p := by
  let : IsProbabilityMeasure (p.toMeasure.map (fun x => a * x)) :=
    Measure.isProbabilityMeasure_map (measurable_const.mul measurable_id).aemeasurable
  simpa only [dilate_toMeasure p ha] using measureHellinger_le_density (p.dilate a ha) p

theorem measureHellinger_scale_le_two_thirds
    (p : HellingerDensity (volume : Measure ℝ))
    (hp : ∀ x, x ≤ 0 → p.density x = 0) {p' p'' : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt p.density (p' x) x)
    (hd' : ∀ x, HasDerivAt p' (p'' x) x)
    (hm' : Measurable p') (hm'' : Measurable p'')
    (hi' : IntegrableOn (fun x => p.density x + x * p' x) (Set.Ioi (0 : ℝ)) volume)
    (hi'' : IntegrableOn (fun x => p.density x + 3 * x * p' x + x ^ 2 * p'' x)
      (Set.Ioi (0 : ℝ)) volume) (s : ℝ) :
    let : IsProbabilityMeasure (p.toMeasure.map (fun x => Real.exp s * x)) :=
      Measure.isProbabilityMeasure_map (measurable_const.mul measurable_id).aemeasurable
    measureHellinger (p.toMeasure.map (fun x => Real.exp s * x)) p.toMeasure ≤
      (2 * Real.sqrt (2 * ∫ x in Set.Ioi (0 : ℝ), |p.density x + 3 * x * p' x + x ^ 2 * p'' x|) +
        Real.sqrt (∫ x in Set.Ioi (0 : ℝ), |p.density x + x * p' x|) / 2) * |s| ^ (2 / 3 : ℝ) :=
    by
  let : IsProbabilityMeasure (p.toMeasure.map (fun x => Real.exp s * x)) :=
    Measure.isProbabilityMeasure_map (measurable_const.mul measurable_id).aemeasurable
  exact (measureHellinger_map_mul_le_density p (Real.exp_pos s)).trans
    (hellinger_dilate_exp_le_two_thirds p hp hd hd' hm' hm'' hi' hi'' s)

end

end ProbabilityTheory.HellingerDensity
