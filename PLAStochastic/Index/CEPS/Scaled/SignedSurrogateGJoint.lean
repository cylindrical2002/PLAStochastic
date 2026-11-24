import PLAStochastic.Index.CEPS.Scaled.SignedQuotientSlices

/-! # Joint continuity and holomorphic slices of the central signed surrogate -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledCentral_spatial_map (N : ℕ) (M : ℝ) {lam : ℂ}
    (hlam : ‖lam‖ ≤ dom.centralDriftRadius N M)
    {x : ℂ × ℂ} (hx : x ∈ ball (0 : ℂ) (dom.centralScaleRadius N M) ×ˢ
      ball 0 (dom.centralCoordinateRadius N M)) {ξ : ℂ} (hξ : ξ ∈ ball (0 : ℂ) 1) :
    ‖x.1 * ξ‖ < dom.c₀ / 2 ∧ x.1 * ξ ∈ ball (0 : ℂ) dom.ρA := by
  have hbc := (cepsScaledCentral_scale_bounds dom hW hθ hD N M hlam
    (mem_ball_zero_iff.mp hx.2).le hx.1).1
  have hnorm : ‖x.1 * ξ‖ ≤ dom.c₀ / 4 := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp hξ).le (norm_nonneg x.1)).trans
      (by simpa only [mul_one] using hbc)
  have hsmall : ‖x.1 * ξ‖ < dom.c₀ / 2 := hnorm.trans_lt (by linarith [dom.c₀_pos])
  exact ⟨hsmall, mem_ball_zero_iff.mpr (by have := dom.c₀_le; have := dom.ρA_pos; linarith)⟩

include hW hθ hD in
theorem cepsScaledSignedSurrogateG_eq_morse (N : ℕ) (M : ℝ) {lam r b : ℂ}
    (hlam : ‖lam‖ ≤ dom.centralDriftRadius N M)
    (hr : ‖r‖ ≤ dom.centralCoordinateRadius N M)
    (hb : b ∈ ball (0 : ℂ) (dom.centralScaleRadius N M)) (ξ : ℂ) :
    cepsScaledSignedSurrogateG dom ρW N lam r b ξ =
      exp (-ξ * (1 + b * lam)) * (cepsMorseQ D θ ρW (b * lam) (b * r) (b * ξ) *
        exp (-2 * cepsCanonDriftTaylor dom ρW N (b * lam)
          (cepsScaledSignedDiscount D θ ρW lam r b) (b * ξ))) := by
  have hc := cepsScaledCentral_chart_bounds dom hW hθ hD N M hlam hr hb
  have hi := cepsMorseQ_eq_cepsQ_of_morse_bounds dom hW hθ hD
    (hc.2.1.le.trans (by linarith [dom.μ₀_pos])) hc.2.2.1 (b * ξ)
  change cepsMorseQ D θ ρW (b * lam) (b * r) (b * ξ) =
    cepsQ D θ ρW (b * lam) (cepsScaledSignedDiscount D θ ρW lam r b) (b * ξ) at hi
  simp only [cepsScaledSignedSurrogateG, cepsScaledBoundedSpatialG, cepsCanonSurrogateWeight]
  rw [← hi]

include hW hθ hD in
theorem cepsScaledSignedCanonicalCurve_differentiableOn {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η) (N : ℕ) (hN : N + 1 ≤ m)
    {lam : ℂ} (hlam : ‖lam‖ ≤ dom.centralDriftRadius N M) :
    DifferentiableOn ℂ (fun x : (ℂ × ℂ) × ℂ => cepsCanonDriftTaylor dom ρW N
      (x.1.1 * lam) (cepsScaledSignedDiscount D θ ρW lam x.1.2 x.1.1) (x.1.1 * x.2))
      ((ball 0 (dom.centralScaleRadius N M) ×ˢ ball 0 (dom.centralCoordinateRadius N M)) ×ˢ ball 0 1) := by
  let U : Set (ℂ × ℂ) := ball 0 (dom.centralScaleRadius N M) ×ˢ ball 0 (dom.centralCoordinateRadius N M)
  have hq : DifferentiableOn ℂ (fun x : (ℂ × ℂ) × ℂ =>
      cepsScaledSignedDiscount D θ ρW lam x.1.2 x.1.1) (U ×ˢ ball 0 1) := by
    have hmu : DifferentiableOn ℂ (fun x : (ℂ × ℂ) × ℂ => x.1.1 * lam) (U ×ˢ ball 0 1) := by fun_prop
    have hMin := (differentiableOn_cepsMorseMin hW hθ hD).comp hmu (fun x hx => by
      have hc := cepsScaledCentral_chart_bounds dom hW hθ hD N M hlam (mem_ball_zero_iff.mp hx.1.2).le hx.1.1
      exact mem_ball_zero_iff.mpr (dom.μ_lt_chart (hc.2.1.le.trans (by linarith [dom.μ₀_pos]))))
    exact hMin.add (by fun_prop)
  have hcurve : DifferentiableOn ℂ (fun x : (ℂ × ℂ) × ℂ =>
      (x.1.1 * lam, (cepsScaledSignedDiscount D θ ρW lam x.1.2 x.1.1, x.1.1 * x.2)))
      (U ×ˢ ball 0 1) := (by fun_prop : DifferentiableOn ℂ (fun x : (ℂ × ℂ) × ℂ => x.1.1 * lam) _).prodMk
        (hq.prodMk (by fun_prop))
  apply (cepsCanonDriftTaylor_differentiableOn dom hW hθ hD hf hη N hN).comp hcurve
  intro x hx
  have hphys := (cepsScaledCentral_spatial_map dom hW hθ hD N M hlam hx.1 hx.2).1
  have hqbound := (cepsScaledCentral_scale_bounds dom hW hθ hD N M hlam
    (mem_ball_zero_iff.mp hx.1.2).le hx.1.1).2.2.2.1
  exact ⟨(re_le_norm _).trans_lt (hphys.trans (half_lt_self dom.c₀_pos)), hqbound⟩

include hW hθ hD in
theorem cepsScaledSignedSurrogateG_continuousOn_joint {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η) (N : ℕ) (hN : N + 1 ≤ m)
    {lam : ℂ} (hlam : ‖lam‖ ≤ dom.centralDriftRadius N M) :
    ContinuousOn (fun x : (ℂ × ℂ) × ℂ => cepsScaledSignedSurrogateG dom ρW N lam x.1.2 x.1.1 x.2)
      ((ball 0 (dom.centralScaleRadius N M) ×ˢ ball 0 (dom.centralCoordinateRadius N M)) ×ˢ ball 0 1) := by
  let T : Set ((ℂ × ℂ) × ℂ) :=
    (ball 0 (dom.centralScaleRadius N M) ×ˢ ball 0 (dom.centralCoordinateRadius N M)) ×ˢ ball 0 1
  have hQ : ContinuousOn (fun x : (ℂ × ℂ) × ℂ =>
      cepsMorseQ D θ ρW (x.1.1 * lam) (x.1.1 * x.1.2) (x.1.1 * x.2)) T :=
    (cepsScaledSignedQuotient_continuousOn_central dom hW hθ hD N M hlam).comp
      (f := fun x : (ℂ × ℂ) × ℂ => (x.1, x.1.1 * x.2)) (by fun_prop)
      (fun x hx => ⟨hx.1, (cepsScaledCentral_spatial_map dom hW hθ hD N M hlam hx.1 hx.2).2⟩)
  have hL := (cepsScaledSignedCanonicalCurve_differentiableOn dom hW hθ hD hf hη N hN hlam).continuousOn
  have hE : ContinuousOn (fun x : (ℂ × ℂ) × ℂ => exp (-x.2 * (1 + x.1.1 * lam))) T := by fun_prop
  apply (hE.mul (hQ.mul ((hL.const_mul (-2)).cexp))).congr
  intro x hx
  exact cepsScaledSignedSurrogateG_eq_morse dom hW hθ hD N M hlam
    (mem_ball_zero_iff.mp hx.1.2).le hx.1.1 x.2

end PGM
