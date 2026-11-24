import PLAStochastic.Index.CEPS.Normal.TwoParameterSlopes

/-! # Moving evaluation of a spatial family with two holomorphic parameter slices -/

noncomputable section
open Complex Set Metric
namespace PGM

theorem cepsNormal_differentiableOn_two_parameter_eval
    {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V) {R : ℝ} {G : (ℂ × ℂ) → ℂ → ℂ}
    (hc : ContinuousOn (fun x : (ℂ × ℂ) × ℂ => G x.1 x.2) ((U ×ˢ V) ×ˢ ball 0 R))
    (hG₁ : ∀ z ∈ V, DifferentiableOn ℂ (fun x : ℂ × ℂ => G (x.1, z) x.2) (U ×ˢ ball 0 R))
    (hG₂ : ∀ b ∈ U, DifferentiableOn ℂ (fun x : ℂ × ℂ => G (b, x.1) x.2) (V ×ˢ ball 0 R))
    {a : (ℂ × ℂ) → ℂ} (ha : DifferentiableOn ℂ a (U ×ˢ V))
    (hamap : MapsTo a (U ×ˢ V) (ball 0 R)) :
    DifferentiableOn ℂ (fun x => G x (a x)) (U ×ˢ V) := by
  have hcE : ContinuousOn (fun x => G x (a x)) (U ×ˢ V) :=
    hc.comp (f := fun x : ℂ × ℂ => (x, a x)) (continuousOn_id.prodMk ha.continuousOn)
      (fun x hx => ⟨hx, hamap hx⟩)
  refine osgood (hU.prod hV) hcE ?_ ?_
  · intro x hx
    have ha₁ : DifferentiableOn ℂ (fun b => a (b, x.2)) U :=
      ha.comp (f := fun b : ℂ => (b, x.2)) (by fun_prop) (fun b hb => ⟨hb, hx.2⟩)
    have he : DifferentiableOn ℂ (fun b => G (b, x.2) (a (b, x.2))) U :=
      (hG₁ x.2 hx.2).comp (f := fun b : ℂ => (b, a (b, x.2)))
        (differentiableOn_id.prodMk ha₁)
        (fun b hb => ⟨hb, hamap (show (b, x.2) ∈ U ×ˢ V from ⟨hb, hx.2⟩)⟩)
    exact (he x.1 hx.1).differentiableAt (hU.mem_nhds hx.1)
  · intro x hx
    have ha₂ : DifferentiableOn ℂ (fun z => a (x.1, z)) V :=
      ha.comp (f := fun z : ℂ => (x.1, z)) (by fun_prop) (fun z hz => ⟨hx.1, hz⟩)
    have he : DifferentiableOn ℂ (fun z => G (x.1, z) (a (x.1, z))) V :=
      (hG₂ x.1 hx.1).comp (f := fun z : ℂ => (z, a (x.1, z)))
        (differentiableOn_id.prodMk ha₂)
        (fun z hz => ⟨hz, hamap (show (x.1, z) ∈ U ×ˢ V from ⟨hx.1, hz⟩)⟩)
    exact (he x.2 hx.2).differentiableAt (hV.mem_nhds hx.2)

end PGM
