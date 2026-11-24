import PLAStochastic.Index.CEPS.Scaled.SignedQuotientChart

/-! # Holomorphic scale/spatial and signed-coordinate/spatial quotient slices -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSigned_raw_differentiableOn_central (N : ℕ) (M : ℝ) {lam : ℂ}
    (hlam : ‖lam‖ ≤ dom.centralDriftRadius N M) :
    DifferentiableOn ℂ (fun x : (ℂ × ℂ) × ℂ =>
      -cepsD ρW (x.1.1 * lam) (cepsScaledSignedDiscount D θ ρW lam x.1.2 x.1.1) x.2)
      ((ball 0 (dom.centralScaleRadius N M) ×ˢ ball 0 (dom.centralCoordinateRadius N M)) ×ˢ ball 0 dom.ρA) := by
  apply (cepsScaledSigned_raw_analyticOnNhd dom hW hθ hD ?_).differentiableOn
  intro x hx
  have h := (cepsScaledCentral_chart_bounds dom hW hθ hD N M hlam
    (mem_ball_zero_iff.mp hx.2).le hx.1).2.1
  exact dom.μ_lt_chart (h.le.trans (by linarith [dom.μ₀_pos]))

include hW hθ hD in
theorem cepsScaledCentral_negative_physical_root_chart (N : ℕ) (M : ℝ) {lam : ℂ}
    (hlam : ‖lam‖ ≤ dom.centralDriftRadius N M) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsMorseRoot D θ ρW (x.1 * lam) (x.1 * (-x.2)))
      (ball 0 (dom.centralScaleRadius N M) ×ˢ ball 0 (dom.centralCoordinateRadius N M)) ∧
    MapsTo (fun x : ℂ × ℂ => cepsMorseRoot D θ ρW (x.1 * lam) (x.1 * (-x.2)))
      (ball 0 (dom.centralScaleRadius N M) ×ˢ ball 0 (dom.centralCoordinateRadius N M)) (ball 0 dom.ρA) := by
  obtain ⟨hp, hpmap⟩ := cepsScaledCentral_physical_root_chart dom hW hθ hD N M hlam
  have hn : MapsTo (fun x : ℂ × ℂ => (x.1, -x.2))
      (ball 0 (dom.centralScaleRadius N M) ×ˢ ball 0 (dom.centralCoordinateRadius N M))
      (ball 0 (dom.centralScaleRadius N M) ×ˢ ball 0 (dom.centralCoordinateRadius N M)) := fun x hx =>
    ⟨hx.1, mem_ball_zero_iff.mpr (by simpa using mem_ball_zero_iff.mp hx.2)⟩
  exact ⟨hp.comp (differentiableOn_fst.prodMk differentiableOn_snd.neg) hn, hpmap.comp hn⟩

include hW hθ hD in
theorem cepsScaledSignedQuotient_holomorphic_slices_central (N : ℕ) (M : ℝ) {lam : ℂ}
    (hlam : ‖lam‖ ≤ dom.centralDriftRadius N M) :
    (∀ r ∈ ball (0 : ℂ) (dom.centralCoordinateRadius N M),
      DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsMorseQ D θ ρW (x.1 * lam) (x.1 * r) x.2)
        (ball 0 (dom.centralScaleRadius N M) ×ˢ ball 0 dom.ρA)) ∧
    (∀ b ∈ ball (0 : ℂ) (dom.centralScaleRadius N M),
      DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsMorseQ D θ ρW (b * lam) (b * x.1) x.2)
        (ball 0 (dom.centralCoordinateRadius N M) ×ˢ ball 0 dom.ρA)) := by
  let U : Set ℂ := ball 0 (dom.centralScaleRadius N M)
  let V : Set ℂ := ball 0 (dom.centralCoordinateRadius N M)
  have hG := cepsScaledSigned_raw_differentiableOn_central dom hW hθ hD N M hlam
  obtain ⟨hp, hpmap⟩ := cepsScaledCentral_physical_root_chart dom hW hθ hD N M hlam
  obtain ⟨hm, hmmap⟩ := cepsScaledCentral_negative_physical_root_chart dom hW hθ hD N M hlam
  constructor
  · intro r hr
    have hraw : DifferentiableOn ℂ (fun x : ℂ × ℂ =>
        -cepsD ρW (x.1 * lam) (cepsScaledSignedDiscount D θ ρW lam r x.1) x.2)
        (U ×ˢ ball 0 dom.ρA) := hG.comp
      (f := fun x : ℂ × ℂ => ((x.1, r), x.2))
      (differentiableOn_fst.prodMk (differentiableOn_const r) |>.prodMk differentiableOn_snd)
      (fun _ hx => ⟨⟨hx.1, hr⟩, hx.2⟩)
    have hpa : DifferentiableOn ℂ (fun b : ℂ => cepsMorseRoot D θ ρW (b * lam) (b * r)) U :=
      hp.comp (differentiableOn_id.prodMk (differentiableOn_const r)) (fun _ hb => ⟨hb, hr⟩)
    have hma : DifferentiableOn ℂ (fun b : ℂ => cepsMorseRoot D θ ρW (b * lam) (b * (-r))) U :=
      hm.comp (differentiableOn_id.prodMk (differentiableOn_const r)) (fun _ hb => ⟨hb, hr⟩)
    have h := cepsNormal_joint_moving_second_dslope_of_differentiable
      (G := fun b ζ => -cepsD ρW (b * lam) (cepsScaledSignedDiscount D θ ρW lam r b) ζ)
      (a := fun b => cepsMorseRoot D θ ρW (b * lam) (b * r))
      (b := fun b => cepsMorseRoot D θ ρW (b * lam) (b * (-r)))
      isOpen_ball hraw hpa hma (fun b hb => hpmap (show (b, r) ∈ U ×ˢ V from ⟨hb, hr⟩))
      (fun b hb => hmmap (show (b, r) ∈ U ×ˢ V from ⟨hb, hr⟩))
    simpa only [cepsMorseQ, cepsScaledSignedDiscount, mul_neg] using h
  · intro b hb
    have hraw : DifferentiableOn ℂ (fun x : ℂ × ℂ =>
        -cepsD ρW (b * lam) (cepsScaledSignedDiscount D θ ρW lam x.1 b) x.2)
        (V ×ˢ ball 0 dom.ρA) := hG.comp
      (f := fun x : ℂ × ℂ => ((b, x.1), x.2))
      ((differentiableOn_const b).prodMk differentiableOn_fst |>.prodMk differentiableOn_snd)
      (fun _ hx => ⟨⟨hb, hx.1⟩, hx.2⟩)
    have hpa : DifferentiableOn ℂ (fun r : ℂ => cepsMorseRoot D θ ρW (b * lam) (b * r)) V :=
      hp.comp ((differentiableOn_const b).prodMk differentiableOn_id) (fun _ hr => ⟨hb, hr⟩)
    have hma : DifferentiableOn ℂ (fun r : ℂ => cepsMorseRoot D θ ρW (b * lam) (b * (-r))) V :=
      hm.comp ((differentiableOn_const b).prodMk differentiableOn_id) (fun _ hr => ⟨hb, hr⟩)
    have h := cepsNormal_joint_moving_second_dslope_of_differentiable
      (G := fun r ζ => -cepsD ρW (b * lam) (cepsScaledSignedDiscount D θ ρW lam r b) ζ)
      (a := fun r => cepsMorseRoot D θ ρW (b * lam) (b * r))
      (b := fun r => cepsMorseRoot D θ ρW (b * lam) (b * (-r)))
      isOpen_ball hraw hpa hma (fun r hr => hpmap (show (b, r) ∈ U ×ˢ V from ⟨hb, hr⟩))
      (fun r hr => hmmap (show (b, r) ∈ U ×ˢ V from ⟨hb, hr⟩))
    simpa only [cepsMorseQ, cepsScaledSignedDiscount, mul_neg] using h

end PGM
