import PLAStochastic.Index.CEPS.Scaled.SignedSurrogateGJoint

/-! # Holomorphic slices of the central signed surrogate weight -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSignedSurrogateG_scale_spatial_differentiableOn {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η) (N : ℕ) (hN : N + 1 ≤ m)
    {lam r : ℂ} (hlam : ‖lam‖ ≤ dom.centralDriftRadius N M)
    (hr : r ∈ ball (0 : ℂ) (dom.centralCoordinateRadius N M)) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledSignedSurrogateG dom ρW N lam r x.1 x.2)
      (ball 0 (dom.centralScaleRadius N M) ×ˢ ball 0 1) := by
  let T : Set (ℂ × ℂ) := ball 0 (dom.centralScaleRadius N M) ×ˢ ball 0 1
  have hQs := (cepsScaledSignedQuotient_holomorphic_slices_central dom hW hθ hD N M hlam).1 r hr
  have hQ : DifferentiableOn ℂ (fun x : ℂ × ℂ =>
      cepsMorseQ D θ ρW (x.1 * lam) (x.1 * r) (x.1 * x.2)) T :=
    hQs.comp (differentiableOn_fst.prodMk (differentiableOn_fst.mul differentiableOn_snd))
      (fun x hx => ⟨hx.1, (cepsScaledCentral_spatial_map dom hW hθ hD N M hlam
        (show (x.1, r) ∈ ball 0 (dom.centralScaleRadius N M) ×ˢ ball 0 (dom.centralCoordinateRadius N M)
          from ⟨hx.1, hr⟩) hx.2).2⟩)
  have hL : DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsCanonDriftTaylor dom ρW N (x.1 * lam)
      (cepsScaledSignedDiscount D θ ρW lam r x.1) (x.1 * x.2)) T :=
    (cepsScaledSignedCanonicalCurve_differentiableOn dom hW hθ hD hf hη N hN hlam).comp
      (f := fun x : ℂ × ℂ => ((x.1, r), x.2))
      (differentiableOn_fst.prodMk (differentiableOn_const r) |>.prodMk differentiableOn_snd)
      (fun _ hx => ⟨⟨hx.1, hr⟩, hx.2⟩)
  have hE : DifferentiableOn ℂ (fun x : ℂ × ℂ => exp (-x.2 * (1 + x.1 * lam))) T := by fun_prop
  apply (hE.mul (hQ.mul ((hL.const_mul (-2)).cexp))).congr
  intro x hx
  exact cepsScaledSignedSurrogateG_eq_morse dom hW hθ hD N M hlam (mem_ball_zero_iff.mp hr).le hx.1 x.2

include hW hθ hD in
theorem cepsScaledSignedSurrogateG_coordinate_spatial_differentiableOn {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η) (N : ℕ) (hN : N + 1 ≤ m)
    {lam b : ℂ} (hlam : ‖lam‖ ≤ dom.centralDriftRadius N M)
    (hb : b ∈ ball (0 : ℂ) (dom.centralScaleRadius N M)) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledSignedSurrogateG dom ρW N lam x.1 b x.2)
      (ball 0 (dom.centralCoordinateRadius N M) ×ˢ ball 0 1) := by
  let T : Set (ℂ × ℂ) := ball 0 (dom.centralCoordinateRadius N M) ×ˢ ball 0 1
  have hQs := (cepsScaledSignedQuotient_holomorphic_slices_central dom hW hθ hD N M hlam).2 b hb
  have hQ : DifferentiableOn ℂ (fun x : ℂ × ℂ =>
      cepsMorseQ D θ ρW (b * lam) (b * x.1) (b * x.2)) T :=
    hQs.comp (differentiableOn_fst.prodMk (differentiableOn_snd.const_mul b))
      (fun x hx => ⟨hx.1, (cepsScaledCentral_spatial_map dom hW hθ hD N M hlam
        (show (b, x.1) ∈ ball 0 (dom.centralScaleRadius N M) ×ˢ ball 0 (dom.centralCoordinateRadius N M)
          from ⟨hb, hx.1⟩) hx.2).2⟩)
  have hL : DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsCanonDriftTaylor dom ρW N (b * lam)
      (cepsScaledSignedDiscount D θ ρW lam x.1 b) (b * x.2)) T :=
    (cepsScaledSignedCanonicalCurve_differentiableOn dom hW hθ hD hf hη N hN hlam).comp
      (f := fun x : ℂ × ℂ => ((b, x.1), x.2))
      ((differentiableOn_const b).prodMk differentiableOn_fst |>.prodMk differentiableOn_snd)
      (fun _ hx => ⟨⟨hb, hx.1⟩, hx.2⟩)
  have hE : DifferentiableOn ℂ (fun x : ℂ × ℂ => exp (-x.2 * (1 + b * lam))) T := by fun_prop
  apply (hE.mul (hQ.mul ((hL.const_mul (-2)).cexp))).congr
  intro x hx
  exact cepsScaledSignedSurrogateG_eq_morse dom hW hθ hD N M hlam (mem_ball_zero_iff.mp hx.1).le hb x.2

end PGM
