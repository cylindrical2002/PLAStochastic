import PLAStochastic.Index.GEP.StrongApprox.Quantile.ConditionalSplit
import Mathlib.MeasureTheory.Group.LIntegral

/-! # WP5: the conditional quantile split reconstructs independent children -/

namespace PGM

noncomputable section

open MeasureTheory Measure ProbabilityTheory Set Filter Topology
open scoped ENNReal

theorem SADensity.lintegral_law {p : ℝ → ℝ} (hp : SADensity p) (f : ℝ → ℝ≥0∞) :
    ∫⁻ x, f x ∂(hp.law : Measure ℝ) = ∫⁻ x, ENNReal.ofReal (p x) * f x :=
  lintegral_withDensity_eq_lintegral_mul_non_measurable volume
    hp.continuous.measurable.ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) f

theorem SADensity.split_lintegral_cancel {p : ℝ → ℝ} (hp : SADensity p)
    (a : ℝ) (f : ℝ → ℝ≥0∞) :
    ENNReal.ofReal (saSumDensity p a) * (∫⁻ x, f x ∂((hp.splitDensity a).law : Measure ℝ)) =
      ∫⁻ x, ENNReal.ofReal (p x) * ENNReal.ofReal (p (a - x)) * f x := by
  rw [(hp.splitDensity a).lintegral_law,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro x
  rw [← mul_assoc, ← ENNReal.ofReal_mul (hp.sumDensity_pos a).le,
    saSplitDensity, mul_div_cancel₀ _ (hp.sumDensity_pos a).ne',
    ENNReal.ofReal_mul (hp.pos x).le]

/-- Integrating the conditional split against the sum law reconstructs the product law. -/
theorem SADensity.split_disintegration {p : ℝ → ℝ} (hp : SADensity p)
    {f : ℝ × ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ a, ∫⁻ x, f (x, a - x) ∂((hp.splitDensity a).law : Measure ℝ)
      ∂(hp.sumDensity.law : Measure ℝ)) =
        ∫⁻ x, ∫⁻ y, f (x, y) ∂(hp.law : Measure ℝ) ∂(hp.law : Measure ℝ) := by
  rw [hp.sumDensity.lintegral_law]
  simp_rw [hp.split_lintegral_cancel]
  rw [lintegral_lintegral_swap (by
    exact ((hp.continuous.measurable.comp measurable_snd).ennreal_ofReal.mul
      (hp.continuous.measurable.comp (measurable_fst.sub measurable_snd)).ennreal_ofReal).mul
      (hf.comp (measurable_snd.prodMk (measurable_fst.sub measurable_snd))) |>.aemeasurable)]
  rw [hp.lintegral_law]
  apply lintegral_congr
  intro x
  rw [hp.lintegral_law, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have ht := lintegral_add_left_eq_self (μ := volume)
    (fun a : ℝ => ENNReal.ofReal (p x) * ENNReal.ofReal (p (a - x)) * f (x, a - x)) x
  simpa only [add_sub_cancel_left, mul_assoc] using ht.symm

set_option maxHeartbeats 400000 in
/-- One parent sum and one independent uniform innovation generate two independent children. -/
theorem SADensity.splitQuantile_pair_law {p : ℝ → ℝ} (hp : SADensity p) :
    (((hp.sumDensity.law : Measure ℝ).prod saUniform).map
      (fun z : ℝ × ℝ => (saSplitQuantile hp z.1 z.2, z.1 - saSplitQuantile hp z.1 z.2))) =
        (hp.law : Measure ℝ).prod (hp.law : Measure ℝ) := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hm : Measurable (fun z : ℝ × ℝ =>
      (saSplitQuantile hp z.1 z.2, z.1 - saSplitQuantile hp z.1 z.2)) :=
    hp.measurable_splitQuantile.prodMk (measurable_fst.sub hp.measurable_splitQuantile)
  rw [lintegral_map hf hm]
  have hfhm : Measurable (fun z : ℝ × ℝ =>
      f (saSplitQuantile hp z.1 z.2, z.1 - saSplitQuantile hp z.1 z.2)) := hf.comp hm
  rw [lintegral_prod _ hfhm.aemeasurable, lintegral_prod _ hf.aemeasurable]
  rw [← hp.split_disintegration hf]
  apply lintegral_congr
  intro a
  have hma : Measurable (saSplitQuantile hp a) :=
    (hp.splitDensity a).regularCDF.measurable_quantile
  have hfa : Measurable (fun x => f (x, a - x)) :=
    hf.comp (measurable_id.prodMk (measurable_const.sub measurable_id))
  calc
    (∫⁻ u, f (saSplitQuantile hp a u, a - saSplitQuantile hp a u) ∂saUniform) =
        ∫⁻ x, f (x, a - x) ∂(saUniform.map (saSplitQuantile hp a)) :=
      (lintegral_map hfa hma).symm
    _ = _ := congrArg (fun η : Measure ℝ => ∫⁻ x, f (x, a - x) ∂η)
      (hp.splitQuantile_law a)

end

end PGM
