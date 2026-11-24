import PLAStochastic.Affine.Extrema.Contact.MarkedLaw

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- Convert the marked time/lag/endpoint coordinates to the five physical coordinates. -/
def orderedContactRead (x r : ℝ) (p : OrderedLayerCoordinates) : ExtremaVector :=
  (-x,r-x,p.1,p.1+p.2.1,p.2.2-x)

theorem orderedContactRead_mark {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (x r e : ℝ) (ω : Ω) :
    orderedContactRead x r (orderedContactMark B x r e ω)=orderedContactVector B x r e ω := by
  simp only [orderedContactRead,orderedContactMark,orderedContactVector,add_sub_cancel_left]

theorem continuous_orderedContactRead (x r : ℝ) : Continuous (orderedContactRead x r) := by
  unfold orderedContactRead
  fun_prop

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- Null measurability of the actual layer with all Borel observations retained. -/
theorem nullMeasurableSet_orderedContactLayer_tests (hB : IsBrownianReal B μ)
    {x r e d : ℝ} (hr : 0 < r) (he : 0 < e) (hd : 0 < d)
    {S D₁ D₂ : Set ℝ} (hS : MeasurableSet S) (hD₁ : MeasurableSet D₁) (hD₂ : MeasurableSet D₂) :
    NullMeasurableSet {ω | orderedContactLayerEvent B x r e d 1 S D₁ D₂ ω} μ := by
  have hn := (nullMeasurableSet_orderedContactLayer hB x r e d).inter
    ((aemeasurable_orderedContactMark hB x r e).nullMeasurableSet_preimage (hD₁.prod (hD₂.prod hS)))
  apply hn.congr
  filter_upwards [hB.cont] with ω hc
  apply propext
  exact (orderedContactLayer_iff_mark hc hr he hd S D₁ D₂).symm

/-- A test supported on the physical ordered-extrema domain automatically removes
terminal points outside the old interval. -/
theorem orderedContactTest_eq_interior_indicator {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (B · ω)) {x r e d : ℝ} (hr : 0 < r) (he : 0 < e) (hd : 0 < d)
    {φ : ExtremaVector → ℝ} (hsupp : ∀ p, p ∉ orderedExtremaDomain → φ p=0) :
    ENNReal.ofReal (orderedContactTest φ B x r e d ω) =
      {ω | orderedContactLayerEvent B x r e d 1 (Icc 0 r) univ univ ω}.indicator
        (fun ω => ENNReal.ofReal (φ (orderedContactRead x r (orderedContactMark B x r e ω)))) ω := by
  classical
  let A := {ω | orderedContactLayerEvent B x r e d 1 (Icc 0 r) univ univ ω}
  have hA : ω ∈ A ↔ orderedContactLayerEvent B x r e d 1 univ univ univ ω ∧ x+B 1 ω ∈ Icc 0 r := by
    rw [show ω ∈ A ↔ orderedContactLayerEvent B x r e d 1 (Icc 0 r) univ univ ω from Iff.rfl,
      orderedContactLayer_iff_mark hc hr he hd (Icc 0 r) univ univ]
    simp only [orderedContactMark,mem_prod,mem_univ,true_and]
  by_cases hbase : orderedContactLayerEvent B x r e d 1 univ univ univ ω
  · by_cases hz : x+B 1 ω ∈ Icc 0 r
    · have hmem := hA.mpr ⟨hbase,hz⟩
      rw [indicator_of_mem hmem,orderedContactRead_mark,orderedContactTest,if_pos hbase]
    · have hnot : ω ∉ A := fun hh => hz (hA.mp hh).2
      rw [indicator_of_notMem hnot,orderedContactTest,if_pos hbase]
      have hout : orderedContactVector B x r e ω ∉ orderedExtremaDomain := by
        intro hp
        have hlo : -x < B 1 ω := hp.2.2.1
        have hup : B 1 ω < r-x := hp.2.2.2.1
        exact hz ⟨by linarith,by linarith⟩
      rw [hsupp _ hout,ENNReal.ofReal_zero]
  · have hnot : ω ∉ A := fun hh => hbase (hA.mp hh).1
    rw [indicator_of_notMem hnot,orderedContactTest,if_neg hbase,ENNReal.ofReal_zero]

/-- Arbitrary Borel tests supported in the ordered physical domain satisfy the
exact marked-layer law, with no density law supplied as an assumption. -/
theorem lintegral_orderedContactTest_eq_heatLayer (hB : IsBrownianReal B μ)
    {x r e d : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) (he : 0 < e) (hd : 0 < d)
    {φ : ExtremaVector → ℝ} (hφ : Measurable φ)
    (hsupp : ∀ p, p ∉ orderedExtremaDomain → φ p=0) :
    (∫⁻ ω, ENNReal.ofReal (orderedContactTest φ B x r e d ω) ∂μ) =
      ∫⁻ p, ENNReal.ofReal (φ (orderedContactRead x r p)) ∂orderedHeatLayerMeasure r e d 1 x := by
  have hmread : Measurable (fun p => ENNReal.ofReal (φ (orderedContactRead x r p))) :=
    (hφ.comp (continuous_orderedContactRead x r).measurable).ennreal_ofReal
  rw [←orderedContactMarkMeasure_eq_heatLayer hB hr hx he hd,orderedContactMarkMeasure,
    lintegral_map' hmread.aemeasurable
      (aemeasurable_orderedContactMark hB x r e).restrict,
    ←lintegral_indicator₀ (nullMeasurableSet_orderedContactLayer_tests hB hr he hd
      measurableSet_Icc MeasurableSet.univ MeasurableSet.univ)]
  exact lintegral_congr_ae (hB.cont.mono (fun ω hc =>
    orderedContactTest_eq_interior_indicator hc hr he hd hsupp))

/-- The actual continuous-path observable is the three-kernel density integral,
for every nonnegative Borel test supported in the physical ordered domain. -/
theorem lintegral_orderedContactTest_eq_heatIntegral (hB : IsBrownianReal B μ)
    {x r e d : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) (he : 0 < e) (hd : 0 < d)
    {φ : ExtremaVector → ℝ} (hφ : Measurable φ) (hn : ∀ p, 0 ≤ φ p)
    (hsupp : ∀ p, p ∉ orderedExtremaDomain → φ p=0) :
    (∫⁻ ω, ENNReal.ofReal (orderedContactTest φ B x r e d ω) ∂μ) =
      ∫⁻ p in orderedHeatLayerDomain r 1, ENNReal.ofReal
        (φ (orderedContactRead x r p)*orderedContactLayerKernel r e d 1 p.1 p.2.1 x p.2.2) := by
  have hmread : Measurable (fun p => ENNReal.ofReal (φ (orderedContactRead x r p))) :=
    (hφ.comp (continuous_orderedContactRead x r).measurable).ennreal_ofReal
  rw [lintegral_orderedContactTest_eq_heatLayer hB hr hx he hd hφ hsupp,orderedHeatLayerMeasure,
    setLIntegral_withDensity_eq_setLIntegral_mul volume
      (measurable_orderedContactLayerKernel r e d 1 x).ennreal_ofReal
      hmread
      (measurableSet_orderedHeatLayerDomain r 1)]
  apply lintegral_congr
  intro p
  simp only [Pi.mul_apply,ENNReal.ofReal_mul (hn _),mul_comm]

end BrownianAffine
