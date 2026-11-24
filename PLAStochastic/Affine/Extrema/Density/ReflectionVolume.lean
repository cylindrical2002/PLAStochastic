import PLAStochastic.Affine.Extrema.OrderedVector

/-! # Lebesgue preservation of the actual extrema-reflection coordinates -/
noncomputable section
open MeasureTheory Set
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

private theorem volume_preserving_swap_real_pair {Γ : Type*} [MeasureSpace Γ]
    [SFinite (volume : Measure Γ)] :
    MeasurePreserving (fun p : ℝ × ℝ × Γ => (p.2.1,p.1,p.2.2)) volume volume := by
  have ha := volume_preserving_prodAssoc (α₁ := ℝ) (β₁ := ℝ) (γ₁ := Γ)
  have hs : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) volume volume :=
    Measure.measurePreserving_swap
  have hm := hs.prod (MeasurePreserving.id (volume : Measure Γ))
  convert! ha.comp (hm.comp (MeasurePreserving.symm _ ha)) using 1

/-- Swapping the two extremal levels and times and negating the spatial coordinates
is a genuine Lebesgue-preserving map of the five-dimensional product. -/
theorem measurePreserving_extrema_reflection :
    MeasurePreserving (fun p : ExtremaVector =>
      (-p.2.1,-p.1,p.2.2.2.1,p.2.2.1,-p.2.2.2.2)) volume volume := by
  have hs₁ := volume_preserving_swap_real_pair (Γ := ℝ × ℝ × ℝ)
  have hs₂ := (MeasurePreserving.id (volume : Measure ℝ)).prod
    ((MeasurePreserving.id (volume : Measure ℝ)).prod
      (volume_preserving_swap_real_pair (Γ := ℝ)))
  have hn := Measure.measurePreserving_neg (volume : Measure ℝ)
  have hi := MeasurePreserving.id (volume : Measure ℝ)
  have hneg := hn.prod (hn.prod (hi.prod (hi.prod hn)))
  convert! hneg.comp (hs₂.comp hs₁) using 1

end BrownianAffine
