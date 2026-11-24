import PLAStochastic.Affine.Extrema.KilledBoxLaw

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

abbrev ExtremaVector := ℝ × ℝ × ℝ × ℝ × ℝ

/-- The actual minimum, maximum, their selected times, and final position. -/
def brownianExtremaVector {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : ExtremaVector :=
  let g := unitPath (processPath B ω) 1
  (slopeLower g 0,slopeUpper g 0,(lowerTime g 0 : ℝ),(upperTime g 0 : ℝ),B 1 ω)

def orderedExtremaDomain : Set ExtremaVector :=
  {p | p.1 < 0 ∧ 0 < p.2.1 ∧ p.1 < p.2.2.2.2 ∧ p.2.2.2.2 < p.2.1 ∧
    0 < p.2.2.1 ∧ p.2.2.1 < p.2.2.2.1 ∧ p.2.2.2.1 < 1}

def reverseOrderedExtremaDomain : Set ExtremaVector :=
  {p | p.1 < 0 ∧ 0 < p.2.1 ∧ p.1 < p.2.2.2.2 ∧ p.2.2.2.2 < p.2.1 ∧
    0 < p.2.2.2.1 ∧ p.2.2.2.1 < p.2.2.1 ∧ p.2.2.1 < 1}

theorem measurableSet_orderedExtremaDomain : MeasurableSet orderedExtremaDomain := by
  unfold orderedExtremaDomain
  measurability

theorem measurableSet_reverseOrderedExtremaDomain : MeasurableSet reverseOrderedExtremaDomain := by
  unfold reverseOrderedExtremaDomain
  measurability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem aemeasurable_brownianExtremaVector (hB : IsBrownianReal B μ) :
    AEMeasurable (brownianExtremaVector B) μ := by
  have hl : AEMeasurable (fun ω => slopeLower (unitPath (processPath B ω) 1) 0) μ :=
    ((slopeLower_joint_lipschitz.continuous.measurable).comp (f := fun g : Path 1 => (g,0)) (by fun_prop)).comp_aemeasurable
      (aemeasurable_brownianUnitPath hB 1)
  have hh : AEMeasurable (fun ω => slopeUpper (unitPath (processPath B ω) 1) 0) μ :=
    ((slopeUpper_joint_lipschitz.continuous.measurable).comp (f := fun g : Path 1 => (g,0)) (by fun_prop)).comp_aemeasurable
      (aemeasurable_brownianUnitPath hB 1)
  exact hl.prodMk (hh.prodMk ((aemeasurable_brownian_lowerTime hB 0).prodMk
    ((aemeasurable_brownian_upperTime hB 0).prodMk (hB.aemeasurable 1))))

/-- Both time orders exhaust the actual law; endpoint and diagonal components are null. -/
theorem brownianExtremaVector_ordered_support_ae (hB : IsBrownianReal B μ) :
    ∀ᵐ ω ∂μ, brownianExtremaVector B ω ∈ orderedExtremaDomain ∪ reverseOrderedExtremaDomain := by
  filter_upwards [hB.cont,hB.eval_zero_ae_eq_zero,brownian_endpoint_strict_extrema_ae hB,
    brownian_extrema_unique_distinct_interior_ae hB 0] with ω hc hz hb ht
  have h0 : slopeResidual (unitPath (processPath B ω) 1) 0 rangeTimeZero = 0 := by
    have h := slopeResidual_actual_unit B hc 0 0 (by simp)
    simpa only [nnrealRangeTime,rangeTimeZero,hz,NNReal.coe_zero,mul_zero,sub_self] using h
  have h1 : slopeResidual (unitPath (processPath B ω) 1) 0 rangeTimeOne = B 1 ω := by
    have h := slopeResidual_actual_unit B hc 0 1 le_rfl
    simpa only [nnrealRangeTime,rangeTimeOne,NNReal.coe_one,zero_mul,sub_zero] using h
  have hs := hb 0
  rw [h0,h1] at hs
  have hne : (lowerTime (unitPath (processPath B ω) 1) 0 : ℝ) ≠
      (upperTime (unitPath (processPath B ω) 1) 0 : ℝ) := by
    intro he
    exact ht.2.2.2.2 (Subtype.ext he.symm)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact Or.inl ⟨hs.1,hs.2.1,hs.2.2.1,hs.2.2.2,ht.2.2.2.1.1,hlt,ht.2.2.1.2⟩
  · exact Or.inr ⟨hs.1,hs.2.1,hs.2.2.1,hs.2.2.2,ht.2.2.1.1,hgt,ht.2.2.2.1.2⟩

def brownianExtremaMeasure (B : ℝ≥0 → Ω → ℝ) (μ : Measure Ω) : Measure ExtremaVector :=
  μ.map (brownianExtremaVector B)

def brownianOrderedExtremaMeasure (B : ℝ≥0 → Ω → ℝ) (μ : Measure Ω) : Measure ExtremaVector :=
  (brownianExtremaMeasure B μ).restrict orderedExtremaDomain

theorem brownianExtremaMeasure_ordered_support (hB : IsBrownianReal B μ) :
    ∀ᵐ p ∂brownianExtremaMeasure B μ, p ∈ orderedExtremaDomain ∪ reverseOrderedExtremaDomain :=
  (ae_map_iff (aemeasurable_brownianExtremaVector hB)
    (measurableSet_orderedExtremaDomain.union measurableSet_reverseOrderedExtremaDomain)).mpr
      (brownianExtremaVector_ordered_support_ae hB)

theorem brownianExtremaMeasure_eq_ordered_sum (hB : IsBrownianReal B μ) :
    brownianExtremaMeasure B μ = brownianOrderedExtremaMeasure B μ +
      (brownianExtremaMeasure B μ).restrict reverseOrderedExtremaDomain := by
  have hd : Disjoint orderedExtremaDomain reverseOrderedExtremaDomain := by
    apply Set.disjoint_left.mpr
    intro p hp hq
    exact (not_lt_of_gt hp.2.2.2.2.2.1) hq.2.2.2.2.2.1
  rw [brownianOrderedExtremaMeasure,← Measure.restrict_union hd measurableSet_reverseOrderedExtremaDomain]
  exact (Measure.restrict_eq_self_of_ae_mem (brownianExtremaMeasure_ordered_support hB)).symm

theorem brownianExtremaMeasure_univ (hB : IsBrownianReal B μ) : brownianExtremaMeasure B μ univ = 1 := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  rw [brownianExtremaMeasure,Measure.map_apply_of_aemeasurable (aemeasurable_brownianExtremaVector hB) MeasurableSet.univ]
  simp

end BrownianAffine
