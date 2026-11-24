import PLAStochastic.Affine.Extrema.OrderedVector
import PLAStochastic.ForMathlib.MeasureTheory.Integral.RectangleAverage

/-! # Lebesgue coordinates for the ordered contact layer -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- Tonelli in the nested real triple convention used by the contact layer. -/
theorem lintegral_real_triple {F : ℝ × ℝ × ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ p : ℝ × ℝ × ℝ, F p) = ∫⁻ a : ℝ, ∫⁻ b : ℝ, ∫⁻ c : ℝ, F (a,b,c) := by
  rw [show (volume : Measure (ℝ × ℝ × ℝ)) = volume.prod (volume.prod volume) from rfl,
    lintegral_prod _ hF.aemeasurable]
  apply lintegral_congr
  intro a
  exact lintegral_prod _ (hF.comp (by fun_prop)).aemeasurable

/-- The two actual translations from contact lag and endpoint to extrema coordinates
preserve five-dimensional Lebesgue integration. -/
theorem lintegral_orderedContactCoordinates {F : ExtremaVector → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q : ℝ × ℝ, ∫⁻ p : ℝ × ℝ × ℝ,
      F (q.1,q.2,p.1,p.1+p.2.1,p.2.2+q.1)) = ∫⁻ u : ExtremaVector, F u := by
  have hG : Measurable (fun qp : (ℝ × ℝ) × (ℝ × ℝ × ℝ) =>
      F (qp.1.1,qp.1.2,qp.2.1,qp.2.1+qp.2.2.1,qp.2.2.2+qp.1.1)) := hF.comp (by fun_prop)
  rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
    lintegral_prod _ hG.lintegral_prod_right'.aemeasurable]
  rw [show (volume : Measure ExtremaVector) = volume.prod volume from rfl,
    lintegral_prod _ hF.aemeasurable]
  apply lintegral_congr
  intro l
  dsimp only
  have hl : Measurable (fun y : ℝ × ℝ × ℝ × ℝ => F (l,y)) := hF.comp (by fun_prop)
  rw [show (volume : Measure (ℝ × ℝ × ℝ × ℝ)) = volume.prod volume from rfl,
    lintegral_prod _ hl.aemeasurable]
  apply lintegral_congr
  intro h
  have ha : Measurable (fun p : ℝ × ℝ × ℝ => F (l,h,p.1,p.1+p.2.1,p.2.2+l)) := hF.comp (by fun_prop)
  have hb : Measurable (fun p : ℝ × ℝ × ℝ => F (l,h,p)) := hF.comp (by fun_prop)
  rw [lintegral_real_triple ha,lintegral_real_triple hb]
  apply lintegral_congr
  intro s
  dsimp only
  have hz (v : ℝ) : (∫⁻ z : ℝ, F (l,h,s,s+v,z+l)) = ∫⁻ z : ℝ, F (l,h,s,s+v,z) :=
    lintegral_add_right_eq_self (μ := (volume : Measure ℝ)) (fun z => F (l,h,s,s+v,z)) l
  simp_rw [hz]
  exact lintegral_add_left_eq_self (μ := (volume : Measure ℝ)) (fun v => ∫⁻ z : ℝ, F (l,h,s,v,z)) s

end BrownianAffine
