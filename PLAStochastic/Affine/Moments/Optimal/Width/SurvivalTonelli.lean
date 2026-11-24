import PLAStochastic.Affine.Moments.Optimal.Width.UnitWidthCoordinates
import PLAStochastic.Affine.Moments.Optimal.Laplace.Convolution

/-! # Tonelli on the unit-width extremum domain

All statements concern nonnegative Borel integrands, before finiteness.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

theorem lintegral_four_space_time_order {F : UnitWidthCoordinates → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ p : UnitWidthCoordinates, F p) =
      ∫⁻ a : ℝ, ∫⁻ b : ℝ, ∫⁻ v : ℝ, ∫⁻ w : ℝ, F (a, v, w, b) := by
  change (∫⁻ p, F p ∂volume.prod volume) = _
  rw [lintegral_prod _ hF.aemeasurable]
  apply lintegral_congr
  intro a
  have hFa : Measurable (fun p : ℝ × ℝ × ℝ => F (a, p)) := hF.comp measurable_prodMk_left
  change (∫⁻ p, F (a,p) ∂volume.prod volume) = _
  rw [lintegral_prod _ hFa.aemeasurable]
  have he (v : ℝ) : (∫⁻ p : ℝ × ℝ, F (a, v, p)) = ∫⁻ b : ℝ, ∫⁻ w : ℝ, F (a, v, w, b) := by
    have hm : Measurable (fun p : ℝ × ℝ => F (a, v, p)) := hF.comp (by fun_prop)
    change (∫⁻ p, F (a,v,p) ∂volume.prod volume) = _
    rw [lintegral_prod _ hm.aemeasurable]
    exact lintegral_lintegral_swap hm.aemeasurable
  simp_rw [he]
  have hm : Measurable (fun p : (ℝ × ℝ) × ℝ => F (a, p.1.1, p.2, p.1.2)) :=
    hF.comp (by fun_prop)
  have hh : Measurable (fun p : ℝ × ℝ => ∫⁻ w : ℝ, F (a, p.1, w, p.2)) :=
    hm.lintegral_prod_right'
  exact lintegral_lintegral_swap hh.aemeasurable

theorem measurableSet_unitWidthMomentDomain (T : ℝ) : MeasurableSet (unitWidthMomentDomain T) := by
  unfold unitWidthMomentDomain
  measurability

theorem unitWidthMomentDomain_mem_iff (T a v w b : ℝ) :
    (a, v, w, b) ∈ unitWidthMomentDomain T ↔
      a ∈ Ioo 0 1 ∧ b ∈ Ioo 0 1 ∧ 0 < v ∧ w ∈ Ioo 0 (T-v) := by
  simp only [unitWidthMomentDomain, mem_ofPred_eq, mem_Ioo]
  constructor <;> rintro ⟨ha,hb,hv,hw,hT⟩ <;> exact ⟨ha,hb,hv,hw,by linarith⟩

/-- Spatial coordinates are outermost; the remaining simplex is exactly the
domain used in the genuine convolution `Q`. -/
theorem lintegral_unitWidthMomentDomain {F : UnitWidthCoordinates → ℝ≥0∞}
    (hF : Measurable F) (T : ℝ) :
    (∫⁻ p in unitWidthMomentDomain T, F p) =
      ∫⁻ a in Ioo (0 : ℝ) 1, ∫⁻ b in Ioo (0 : ℝ) 1,
        ∫⁻ v in Ioi (0 : ℝ), ∫⁻ w in Ioo (0 : ℝ) (T-v), F (a,v,w,b) := by
  classical
  rw [← lintegral_indicator (measurableSet_unitWidthMomentDomain T),
    lintegral_four_space_time_order (hF.indicator (measurableSet_unitWidthMomentDomain T))]
  rw [← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro a
  by_cases ha : a ∈ Ioo (0 : ℝ) 1
  swap
  · simp [ha, indicator, unitWidthMomentDomain_mem_iff]
  rw [indicator_of_mem ha, ← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro b
  by_cases hb : b ∈ Ioo (0 : ℝ) 1
  swap
  · simp [ha, hb, indicator, unitWidthMomentDomain_mem_iff]
  rw [indicator_of_mem hb, ← lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr
  intro v
  by_cases hv : 0 < v
  swap
  · simp [ha, hb, hv, indicator, unitWidthMomentDomain_mem_iff]
  rw [indicator_of_mem (show v ∈ Ioi (0 : ℝ) from hv),
    ← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro w
  by_cases hw : w ∈ Ioo (0 : ℝ) (T-v) <;>
    simp [ha, hb, hv, hw, indicator, unitWidthMomentDomain_mem_iff]

/-- Any nonnegative Borel spatial weight factors through the actual convolution. -/
theorem lintegral_unitWidthMomentDomain_eq_convolution {G : ℝ × ℝ → ℝ≥0∞}
    (hG : Measurable G) (T : ℝ) :
    (∫⁻ p in unitWidthMomentDomain T, G (p.1,p.2.2.2) *
      ENNReal.ofReal (optimalMomentConvolutionIntegrand p.1 p.2.2.2 T p.2.1 p.2.2.1)) =
      ∫⁻ a in Ioo (0 : ℝ) 1, ∫⁻ b in Ioo (0 : ℝ) 1,
        G (a,b) * optimalMomentConvolutionENN a b T := by
  have hk : Measurable (fun p : UnitWidthCoordinates =>
      ENNReal.ofReal (optimalMomentConvolutionIntegrand p.1 p.2.2.2 T p.2.1 p.2.2.1)) :=
    (measurable_optimalMomentConvolutionIntegrand.comp
      (f := fun p : UnitWidthCoordinates => (p.1,p.2.2.2,T,p.2.1,p.2.2.1)) (by fun_prop)).ennreal_ofReal
  have hm : Measurable (fun p : UnitWidthCoordinates => G (p.1,p.2.2.2) *
      ENNReal.ofReal (optimalMomentConvolutionIntegrand p.1 p.2.2.2 T p.2.1 p.2.2.1)) :=
    (hG.comp (by fun_prop)).mul hk
  rw [lintegral_unitWidthMomentDomain hm T]
  apply lintegral_congr
  intro a
  apply lintegral_congr
  intro b
  have hw (v : ℝ) : Measurable (fun w : ℝ =>
      ENNReal.ofReal (optimalMomentConvolutionIntegrand a b T v w)) :=
    (measurable_optimalMomentConvolutionIntegrand.comp
      (f := fun w : ℝ => (a,b,T,v,w)) (by fun_prop)).ennreal_ofReal
  simp_rw [lintegral_const_mul (G (a,b)) (hw _)]
  have hv : Measurable (fun v : ℝ => ∫⁻ w in Ioo (0 : ℝ) (T-v),
      ENNReal.ofReal (optimalMomentConvolutionIntegrand a b T v w)) := by
    have hm : Measurable (fun p : ℝ × ℝ => (Ioo 0 (T-p.1)).indicator
        (fun w => ENNReal.ofReal (optimalMomentConvolutionIntegrand a b T p.1 w)) p.2) := by
      have hk := (measurable_optimalMomentConvolutionIntegrand.comp (f := fun p : ℝ × ℝ =>
        (a,b,T,p.1,p.2)) (by fun_prop)).ennreal_ofReal
      have hs : MeasurableSet {p : ℝ × ℝ | p.2 ∈ Ioo 0 (T-p.1)} := by
        simp only [mem_Ioo]
        measurability
      exact hk.indicator hs
    simpa only [lintegral_indicator measurableSet_Ioo] using! hm.lintegral_prod_right'
  exact lintegral_const_mul (G (a,b)) hv

end BrownianAffine
