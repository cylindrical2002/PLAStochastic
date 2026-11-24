import PLAStochastic.Affine.Extrema.Density.LayerIntegral

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

theorem isOpen_orderedExtremaDomain : IsOpen orderedExtremaDomain := by
  have hl : Continuous (fun p : ExtremaVector => p.1) := by fun_prop
  have hh : Continuous (fun p : ExtremaVector => p.2.1) := by fun_prop
  have hs : Continuous (fun p : ExtremaVector => p.2.2.1) := by fun_prop
  have hq : Continuous (fun p : ExtremaVector => p.2.2.2.1) := by fun_prop
  have hw : Continuous (fun p : ExtremaVector => p.2.2.2.2) := by fun_prop
  exact (isOpen_lt hl continuous_const).inter ((isOpen_lt continuous_const hh).inter
    ((isOpen_lt hl hw).inter ((isOpen_lt hw hh).inter ((isOpen_lt continuous_const hs).inter
      ((isOpen_lt hs hq).inter (isOpen_lt hq continuous_const))))))

theorem continuousOn_orderedExtremaDensity : ContinuousOn orderedExtremaDensity orderedExtremaDomain := by
  have h := continuousOn_orderedContactDensityKernel.comp
    continuous_extremaContactParameters.continuousOn (fun p hp => extremaContactParameters_mem hp)
  unfold orderedExtremaDensity
  simpa only [Function.comp_def,extremaContactParameters] using h

theorem measurable_orderedExtremaDensity : Measurable orderedExtremaDensity := by
  have hr : Measurable (fun p : ExtremaVector => p.2.1-p.1) := by fun_prop
  have hs : Measurable (fun p : ExtremaVector => p.2.2.1) := by fun_prop
  have hv : Measurable (fun p : ExtremaVector => p.2.2.2.1-p.2.2.1) := by fun_prop
  have hx : Measurable (fun p : ExtremaVector => -p.1) := by fun_prop
  have hz : Measurable (fun p : ExtremaVector => p.2.2.2.2-p.1) := by fun_prop
  have ht : Measurable (fun p : ExtremaVector => 1-p.2.2.1-(p.2.2.2.1-p.2.2.1)) := by fun_prop
  have hA : Measurable (fun p : ExtremaVector => heatBoundaryLeft (p.2.1-p.1) p.2.2.1 (-p.1)) :=
    measurable_heatSpatialSeries_comp hr hs hx measurable_const 0 1
  have hC : Measurable (fun p : ExtremaVector => heatCrossBoundary (p.2.1-p.1) (p.2.2.2.1-p.2.2.1)) :=
    (measurable_heatSpatialSeries_comp hr hv hr measurable_const 1 1).neg
  have hR : Measurable (fun p : ExtremaVector => heatBoundaryRight (p.2.1-p.1)
      (1-p.2.2.1-(p.2.2.2.1-p.2.2.1)) (p.2.2.2.2-p.1)) :=
    (measurable_heatSpatialSeries_comp hr ht hz hr 0 1).neg
  unfold orderedExtremaDensity orderedContactDensityKernel
  exact ((hA.mul hC).mul hR).div_const 4

theorem orderedExtremaDensity_pos {p : ExtremaVector} (hp : p ∈ orderedExtremaDomain) :
    0 < orderedExtremaDensity p := by
  rcases hp with ⟨hl,hh,hlw,hwh,hs,hsq,hq⟩
  have hr : 0 < p.2.1-p.1 := by linarith
  have hx : -p.1 ∈ Ioo 0 (p.2.1-p.1) := ⟨by linarith,by linarith⟩
  have hz : p.2.2.2.2-p.1 ∈ Ioo 0 (p.2.1-p.1) := ⟨by linarith,by linarith⟩
  unfold orderedExtremaDensity orderedContactDensityKernel
  exact div_pos (mul_pos (mul_pos (heatBoundaryLeft_strictlyPositive hr hs hx)
    (heatCrossBoundary_strictlyPositive hr (by linarith)))
    (heatBoundaryRight_strictlyPositive hr (by linarith) hz)) (by norm_num)

/-- The analytic five-variable density measure, with its physical ordered support. -/
def orderedExtremaDensityMeasure : Measure ExtremaVector :=
  (volume.withDensity (fun p => ENNReal.ofReal (orderedExtremaDensity p))).restrict orderedExtremaDomain

theorem orderedExtremaDensityMeasure_support_ae :
    ∀ᵐ p ∂orderedExtremaDensityMeasure, p ∈ orderedExtremaDomain :=
  ae_restrict_mem measurableSet_orderedExtremaDomain

/-- Interior compact sets have finite candidate mass by actual local kernel continuity. -/
theorem orderedExtremaDensityMeasure_compact_lt_top {K : Set ExtremaVector}
    (hK : IsCompact K) (hKi : K ⊆ orderedExtremaDomain) : orderedExtremaDensityMeasure K < ∞ := by
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn (continuousOn_orderedExtremaDensity.mono hKi)
  rw [orderedExtremaDensityMeasure,Measure.restrict_apply hK.measurableSet,
    inter_eq_left.mpr hKi,withDensity_apply _ hK.measurableSet]
  calc
    _ ≤ ∫⁻ _ in K, ENNReal.ofReal |M| := by
      apply setLIntegral_mono' hK.measurableSet
      intro p hp
      exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans ((hM p hp).trans (le_abs_self M)))
    _ < ∞ := by
      rw [lintegral_const,Measure.restrict_apply_univ]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top

end BrownianAffine
