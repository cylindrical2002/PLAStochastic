import PLAStochastic.Affine.Extrema.Contact.FullIntegral
import PLAStochastic.Affine.Extrema.Contact.LevelAveraging
import PLAStochastic.Affine.Extrema.Density.HeatBoundaryIntegral
import PLAStochastic.Affine.Extrema.Contact.Coordinates

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- The exact finite-layer heat kernel in the five physical extrema coordinates. -/
def orderedExtremaLayerKernel (e d : ℝ) (p : ExtremaVector) : ℝ :=
  orderedContactLayerKernel (p.2.1-p.1) e d 1 p.2.2.1 (p.2.2.2.1-p.2.2.1)
    (-p.1) (p.2.2.2.2-p.1)

def orderedExtremaLayerDensity (e d : ℝ) (p : ExtremaVector) : ℝ :=
  orderedContactLayerQuotient (p.2.1-p.1) e d 1 p.2.2.1 (p.2.2.2.1-p.2.2.1)
    (-p.1) (p.2.2.2.2-p.1)

/-- The A0-C-Ar/4 ordered-extrema density in the paper's original five coordinates. -/
def orderedExtremaDensity (p : ExtremaVector) : ℝ :=
  orderedContactDensityKernel (p.2.1-p.1) 1 p.2.2.1 (p.2.2.2.1-p.2.2.1)
    (-p.1) (p.2.2.2.2-p.1)

theorem measurable_orderedExtremaLayerDensity (e d : ℝ) :
    Measurable (orderedExtremaLayerDensity e d) := by
  have h := (measurable_orderedContactLayerQuotient e d).comp continuous_extremaContactParameters.measurable
  unfold orderedExtremaLayerDensity
  simpa only [Function.comp_def,extremaContactParameters] using h

theorem orderedExtremaLayerDensity_eq (e d : ℝ) (p : ExtremaVector) :
    orderedExtremaLayerDensity e d p=orderedExtremaLayerKernel e d p/(e*d) :=
  orderedContactLayerQuotient_eq _ _ _ _ _ _ _ _

theorem measurable_orderedExtremaLayerKernel {e d : ℝ} (he : 0 < e) (hd : 0 < d) :
    Measurable (orderedExtremaLayerKernel e d) := by
  have hfun : orderedExtremaLayerKernel e d = fun p => orderedExtremaLayerDensity e d p*(e*d) := by
    funext p
    rw [orderedExtremaLayerDensity_eq,div_mul_cancel₀ _ (mul_ne_zero he.ne' hd.ne')]
  rw [hfun]
  exact (measurable_orderedExtremaLayerDensity e d).mul_const _

/-- Tonelli and the two unit-Jacobian translations turn the real Brownian contact
observables into the full five-coordinate heat-layer integral. -/
theorem lintegral_levelOrderedContactTest_eq_kernel {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    {e d : ℝ} (he : 0 < e) (hd : 0 < d)
    {φ : ExtremaVector → ℝ} (hφ : Measurable φ) (hn : ∀ p, 0 ≤ φ p)
    (hsupp : ∀ p, p ∉ orderedExtremaDomain → φ p=0) :
    (∫⁻ q : ℝ × ℝ, ∫⁻ ω, ENNReal.ofReal
      (orderedContactTest φ B (-q.1) (q.2-q.1) e d ω) ∂μ) =
      ∫⁻ p, ENNReal.ofReal (φ p*orderedExtremaLayerKernel e d p) := by
  have hm : Measurable (fun p => ENNReal.ofReal (φ p*orderedExtremaLayerKernel e d p)) :=
    (hφ.mul (measurable_orderedExtremaLayerKernel he hd)).ennreal_ofReal
  simp_rw [lintegral_orderedContactTest_eq_full_heatIntegral hB _ _ he hd hφ hn hsupp]
  rw [←lintegral_orderedContactCoordinates hm]
  apply lintegral_congr
  intro q
  apply lintegral_congr
  intro p
  simp only [orderedContactRead,orderedExtremaLayerKernel,neg_neg,sub_neg_eq_add,
    sub_add_cancel,add_sub_cancel_left,add_sub_cancel_right]

/-- The exact normalized real Brownian level average is the five-variable layer
density integral, before passage to the boundary limit. -/
theorem lintegral_levelOrderedContactTest_normalized_eq_layerDensity {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    {e d : ℝ} (he : 0 < e) (hd : 0 < d)
    {φ : ExtremaVector → ℝ} (hφ : Measurable φ) (hn : ∀ p, 0 ≤ φ p)
    (hsupp : ∀ p, p ∉ orderedExtremaDomain → φ p=0) :
    (∫⁻ q : ℝ × ℝ, ∫⁻ ω, ENNReal.ofReal
      (orderedContactTest φ B (-q.1) (q.2-q.1) e d ω) ∂μ) /
        (ENNReal.ofReal e*ENNReal.ofReal d) =
      ∫⁻ p, ENNReal.ofReal (φ p*orderedExtremaLayerDensity e d p) := by
  rw [lintegral_levelOrderedContactTest_eq_kernel hB he hd hφ hn hsupp]
  have hi : (ENNReal.ofReal e*ENNReal.ofReal d)⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.mpr (mul_ne_zero (ENNReal.ofReal_pos.mpr he).ne' (ENNReal.ofReal_pos.mpr hd).ne')
  rw [div_eq_mul_inv,←lintegral_mul_const' _ _ hi]
  apply lintegral_congr
  intro p
  rw [←div_eq_mul_inv,←ENNReal.ofReal_mul he.le,←ENNReal.ofReal_div_of_pos (mul_pos he hd),
    orderedExtremaLayerDensity_eq,mul_div_assoc]

end BrownianAffine
