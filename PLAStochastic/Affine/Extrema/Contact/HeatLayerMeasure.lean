import PLAStochastic.Brownian.Killed.OrderedBoundary.Integral
import PLAStochastic.Affine.Process.Killed.Boundary.Identities

/-! # The analytic measure of the ordered two-contact heat layer -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

abbrev OrderedLayerCoordinates := ℝ × ℝ × ℝ

def orderedHeatLayerDomain (r T : ℝ) : Set OrderedLayerCoordinates :=
  {p | p.1 ∈ Ioo 0 T ∧ p.2.1 ∈ Ioo 0 (T-p.1) ∧ p.2.2 ∈ Icc 0 r}

theorem measurableSet_orderedHeatLayerDomain (r T : ℝ) :
    MeasurableSet (orderedHeatLayerDomain r T) := by
  unfold orderedHeatLayerDomain
  simp only [mem_Ioo,mem_Icc]
  have hs : Measurable (fun p : OrderedLayerCoordinates => p.1) := by fun_prop
  have hv : Measurable (fun p : OrderedLayerCoordinates => p.2.1) := by fun_prop
  have hz : Measurable (fun p : OrderedLayerCoordinates => p.2.2) := by fun_prop
  exact ((measurableSet_lt measurable_const hs).inter
    (measurableSet_lt hs measurable_const)).inter
    (((measurableSet_lt measurable_const hv).inter
      (measurableSet_lt hv (measurable_const.sub hs))).inter
      ((measurableSet_le measurable_const hz).inter
        (measurableSet_le hz measurable_const)))

theorem measurable_orderedContactLayerKernel (r e d T x : ℝ) :
    Measurable (fun p : OrderedLayerCoordinates => orderedContactLayerKernel r e d T p.1 p.2.1 x p.2.2) := by
  have hA := measurable_heatSpatialSeries_comp
    (measurable_const (a := r)) (by fun_prop : Measurable (fun p : OrderedLayerCoordinates => p.1))
    (measurable_const (a := x)) (measurable_const (a := (0 : ℝ))) 0 1
  have hR := (measurable_heatSpatialSeries_comp
    (measurable_const (a := r+e)) (by fun_prop : Measurable (fun p : OrderedLayerCoordinates => p.2.1))
    (measurable_const (a := e)) (measurable_const (a := r+e)) 0 1).neg
  have hK := measurable_heatSpatialSeries_comp
    (measurable_const (a := r+e+d))
    (by fun_prop : Measurable (fun p : OrderedLayerCoordinates => T-p.1-p.2.1))
    (measurable_const (a := r+e)) (by fun_prop : Measurable (fun p : OrderedLayerCoordinates => p.2.2+e)) 0 0
  exact (((hA.div_const 2).mul hR).div_const 2).mul hK

/-- The genuine density measure in first-contact time, elapsed second-contact time,
and translated endpoint coordinates, restricted to its triangular support. -/
def orderedHeatLayerMeasure (r e d T x : ℝ) : Measure OrderedLayerCoordinates :=
  (volume.withDensity (fun p => ENNReal.ofReal
    (orderedContactLayerKernel r e d T p.1 p.2.1 x p.2.2))).restrict (orderedHeatLayerDomain r T)

private theorem lintegral_parameter_indicator {α β : Type*} [MeasurableSpace β]
    {μ : Measure β} (A : Set α) (f : α → β → ℝ≥0∞) (a : α) :
    (∫⁻ b, A.indicator (fun a => f a b) a ∂μ) =
      A.indicator (fun a => ∫⁻ b, f a b ∂μ) a := by
  by_cases ha : a ∈ A <;> simp [indicator,ha]

/-- Tonelli on the triangular time region, for an arbitrary nonnegative Borel kernel. -/
theorem setLIntegral_orderedHeatLayerDomain {F : OrderedLayerCoordinates → ℝ≥0∞}
    (hF : Measurable F) (r T : ℝ) (D₁ D₂ S : Set ℝ) :
    (∫⁻ p in (D₁ ×ˢ (D₂ ×ˢ S)) ∩ orderedHeatLayerDomain r T, F p) =
      ∫⁻ s in D₁ ∩ Ioo 0 T, ∫⁻ v in D₂ ∩ Ioo 0 (T-s), ∫⁻ z in S ∩ Icc 0 r, F (s,v,z) := by
  let G := (orderedHeatLayerDomain r T).indicator F
  have hG : Measurable G := hF.indicator (measurableSet_orderedHeatLayerDomain r T)
  have he : (∫⁻ p in D₁ ×ˢ (D₂ ×ˢ S), G p) =
      ∫⁻ p in (D₁ ×ˢ (D₂ ×ˢ S)) ∩ orderedHeatLayerDomain r T, F p := by
    dsimp only [G]
    rw [lintegral_indicator (measurableSet_orderedHeatLayerDomain r T),
      Measure.restrict_restrict (measurableSet_orderedHeatLayerDomain r T), inter_comm]
  rw [← he]
  change (∫⁻ p in D₁ ×ˢ (D₂ ×ˢ S), G p ∂volume.prod (volume.prod volume)) = _
  rw [setLIntegral_prod _ hG.aemeasurable]
  have hin (s : ℝ) : (∫⁻ q in D₂ ×ˢ S, G (s,q) ∂volume.prod volume) =
      ∫⁻ v in D₂, ∫⁻ z in S, G (s,v,z) :=
    setLIntegral_prod _ (hG.comp (by fun_prop)).aemeasurable
  simp_rw [hin]
  have hpoint (s v z : ℝ) : G (s,v,z) =
      (Ioo 0 T).indicator (fun s => (Ioo 0 (T-s)).indicator
        (fun v => (Icc 0 r).indicator (fun z => F (s,v,z)) z) v) s := by
    simp only [G, orderedHeatLayerDomain, mem_ofPred_eq, indicator]
    split_ifs <;> simp_all
  simp_rw [hpoint, lintegral_parameter_indicator, lintegral_indicator measurableSet_Icc,
    Measure.restrict_restrict measurableSet_Icc]
  simp only [lintegral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo, inter_comm]

/-- The candidate density gives exactly the triple heat convolution on every Borel rectangle. -/
theorem orderedHeatLayerMeasure_apply_prod {r e d T x : ℝ}
    (hr : 0 < r) (hx : x ∈ Ioo 0 r) (he : 0 < e)
    {D₁ D₂ S : Set ℝ} (hD₁ : MeasurableSet D₁) (hD₂ : MeasurableSet D₂)
    (hS : MeasurableSet S) :
    orderedHeatLayerMeasure r e d T x (D₁ ×ˢ (D₂ ×ˢ S)) =
      ∫⁻ s in D₁ ∩ Ioo 0 T, ENNReal.ofReal (heatBoundaryLeft r s x/2) *
        ∫⁻ v in D₂ ∩ Ioo 0 (T-s), ENNReal.ofReal (heatBoundaryRight (r+e) v e/2) *
          ∫⁻ z in S ∩ Icc 0 r, ENNReal.ofReal (dirichletHeatKernel (r+e+d) (T-s-v) (r+e) (z+e)) := by
  rw [orderedHeatLayerMeasure, Measure.restrict_apply (hD₁.prod (hD₂.prod hS)),
    withDensity_apply _ ((hD₁.prod (hD₂.prod hS)).inter
      (measurableSet_orderedHeatLayerDomain r T)),
    setLIntegral_orderedHeatLayerDomain (measurable_orderedContactLayerKernel r e d T x).ennreal_ofReal]
  apply setLIntegral_congr_fun (hD₁.inter measurableSet_Ioo)
  intro s hs
  dsimp only
  have hA := (heatBoundaryLeft_strictlyPositive hr hs.2.1 hx).le
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_congr_fun (hD₂.inter measurableSet_Ioo)
  intro v hv
  dsimp only
  have hR := (heatBoundaryRight_strictlyPositive (by linarith : 0 < r+e) hv.2.1
    (show e ∈ Ioo 0 (r+e) from ⟨he,by linarith⟩)).le
  rw [← mul_assoc, ← lintegral_const_mul' _ _
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
  apply setLIntegral_congr_fun (hS.inter measurableSet_Icc)
  intro z _
  dsimp only [orderedContactLayerKernel]
  rw [show heatBoundaryLeft r s x / 2 * heatBoundaryRight (r+e) v e / 2 =
    (heatBoundaryLeft r s x/2)*(heatBoundaryRight (r+e) v e/2) by ring,
    ENNReal.ofReal_mul (mul_nonneg (div_nonneg hA (by norm_num)) (div_nonneg hR (by norm_num))),
    ENNReal.ofReal_mul (div_nonneg hA (by norm_num))]

end BrownianAffine
