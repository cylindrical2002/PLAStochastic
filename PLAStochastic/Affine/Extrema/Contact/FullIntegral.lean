import PLAStochastic.Affine.Extrema.Contact.WeightedLaw

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- Membership of the physical ordered domain enforces all triangular heat
coordinates and the valid initial interval, directly from the coordinate map. -/
theorem orderedContactRead_mem_domain {x r : ℝ} {p : OrderedLayerCoordinates}
    (hp : orderedContactRead x r p ∈ orderedExtremaDomain) :
    x ∈ Ioo 0 r ∧ p ∈ orderedHeatLayerDomain r 1 := by
  change -x < 0 ∧ 0 < r-x ∧ -x < p.2.2-x ∧ p.2.2-x < r-x ∧
    0 < p.1 ∧ p.1 < p.1+p.2.1 ∧ p.1+p.2.1 < 1 at hp
  refine ⟨⟨by linarith [hp.1],by linarith [hp.2.1]⟩,
    ⟨hp.2.2.2.2.1,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩
  all_goals linarith [hp.2.2.1,hp.2.2.2.1,hp.2.2.2.2.2.1,hp.2.2.2.2.2.2]

/-- Invalid old intervals contribute zero to every physical-domain-supported test. -/
theorem orderedContactTest_eq_zero_of_not_initial {Ω : Type*}
    (B : ℝ≥0 → Ω → ℝ) (ω : Ω) {x r e d : ℝ} (hx : x ∉ Ioo 0 r)
    {φ : ExtremaVector → ℝ} (hsupp : ∀ p, p ∉ orderedExtremaDomain → φ p=0) :
    orderedContactTest φ B x r e d ω=0 := by
  have hz : φ (orderedContactVector B x r e ω)=0 := by
    apply hsupp
    intro hp
    rw [←orderedContactRead_mark B x r e ω] at hp
    exact hx (orderedContactRead_mem_domain hp).1
  unfold orderedContactTest
  split_ifs <;> simp only [hz]

/-- The exact actual layer law extends to every real level pair. The support of
the test removes invalid intervals and all complementary heat-coordinate regions. -/
theorem lintegral_orderedContactTest_eq_full_heatIntegral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    (x r : ℝ) {e d : ℝ} (he : 0 < e) (hd : 0 < d)
    {φ : ExtremaVector → ℝ} (hφ : Measurable φ) (hn : ∀ p, 0 ≤ φ p)
    (hsupp : ∀ p, p ∉ orderedExtremaDomain → φ p=0) :
    (∫⁻ ω, ENNReal.ofReal (orderedContactTest φ B x r e d ω) ∂μ) =
      ∫⁻ p : OrderedLayerCoordinates, ENNReal.ofReal
        (φ (orderedContactRead x r p)*orderedContactLayerKernel r e d 1 p.1 p.2.1 x p.2.2) := by
  by_cases hx : x ∈ Ioo 0 r
  · rw [lintegral_orderedContactTest_eq_heatIntegral hB (hx.1.trans hx.2) hx he hd hφ hn hsupp,
      ←lintegral_indicator (measurableSet_orderedHeatLayerDomain r 1)]
    apply lintegral_congr
    intro p
    by_cases hp : p ∈ orderedHeatLayerDomain r 1
    · rw [indicator_of_mem hp]
    · have hz : φ (orderedContactRead x r p)=0 :=
        hsupp _ (fun h => hp (orderedContactRead_mem_domain h).2)
      rw [indicator_of_notMem hp,hz,zero_mul,ENNReal.ofReal_zero]
  · have hzero (p : OrderedLayerCoordinates) : φ (orderedContactRead x r p)=0 :=
      hsupp _ (fun h => hx (orderedContactRead_mem_domain h).1)
    simp only [orderedContactTest_eq_zero_of_not_initial B _ hx hsupp,hzero,
      zero_mul,ENNReal.ofReal_zero,lintegral_zero]

end BrownianAffine
