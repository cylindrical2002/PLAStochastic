import PLAStochastic.Index.CEPS.Contour.NormalForms
import PLAStochastic.Index.CEPS.Scaled.TrueHalfPairScaling

/-! # Exact contour transfer of the actual scaled complete pair -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)
variable {σ : ℝ} (hσ : 0 < σ) (hσc : σ ≤ dom.c₀)

include hW hθ hD in
theorem cepsScaledTruePhysicalPair_shrink_eq {lam b : ℝ} {z : ℂ}
    (hμ : |b * lam| ≤ (dom.shrink σ hσ hσc).μ₀)
    (hq : ‖cepsComplexScaledDiscount lam z b‖ < (dom.shrink σ hσ hσc).q₀)
    (ht : ((b : ℂ) ^ 2 * z).re < σ) :
    cepsScaledTruePhysicalPair (dom.shrink σ hσ hσc) ρW lam z b =
      cepsScaledTruePhysicalPair dom ρW lam z b := by
  unfold cepsScaledTruePhysicalPair
  simp only [← ofReal_mul]
  rw [dom.regularEntrance_shrink_eq hW hθ hD hσ hσc hμ hq.le _ ht,
    dom.regularBridge_deriv_shrink_eq hW hθ hD hσ hσc hμ hq _,
    dom.regularBridge_shrink_eq hW hθ hD hσ hσc hμ hq.le _]

include hW hθ hD in
theorem cepsScaledTrueHalfPhysicalPair_shrink_eq {lam b : ℝ} {z : ℂ}
    (hμ : |b * lam| ≤ (dom.shrink σ hσ hσc).μ₀)
    (hq : ‖cepsComplexScaledDiscount lam z b‖ < (dom.shrink σ hσ hσc).q₀)
    (ht : ((b : ℂ) ^ 2 * z).re < σ) :
    cepsScaledTrueHalfPhysicalPair (dom.shrink σ hσ hσc) ρW lam z b =
      cepsScaledTrueHalfPhysicalPair dom ρW lam z b := by
  unfold cepsScaledTrueHalfPhysicalPair
  simp only [← ofReal_mul]
  rw [dom.regularHalfEntrance_shrink_eq hW hθ hD hσ hσc hμ hq.le ht,
    dom.halfBridge_deriv_shrink_eq hW hθ hD hσ hσc hμ hq _,
    dom.halfBridge_shrink_eq hW hθ hD hσ hσc hμ hq.le _]

include hW hθ hD in
theorem cepsScaledTrueSubtractedPhysicalPair_shrink_eq {lam b : ℝ} {z : ℂ}
    (hμ : |b * lam| ≤ (dom.shrink σ hσ hσc).μ₀)
    (hq : ‖cepsComplexScaledDiscount lam z b‖ < (dom.shrink σ hσ hσc).q₀)
    (ht : ((b : ℂ) ^ 2 * z).re < σ) :
    cepsScaledTrueSubtractedPhysicalPair (dom.shrink σ hσ hσc) ρW lam z b =
      cepsScaledTrueSubtractedPhysicalPair dom ρW lam z b := by
  unfold cepsScaledTrueSubtractedPhysicalPair
  rw [cepsScaledTruePhysicalPair_shrink_eq dom hW hθ hD hσ hσc hμ hq ht,
    cepsScaledTrueHalfPhysicalPair_shrink_eq dom hW hθ hD hσ hσc hμ hq ht]

include hW hθ hD in
theorem cepsScaledTrueSubtractedPair_shrink_eq (M M' lam : ℝ) {z : ℂ} (hz : z.re = 0)
    {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z))
    (hbs' : (b : ℂ) ∈ ball (0 : ℂ)
      ((dom.shrink σ hσ hσc).trueFrequencyScaleRadius M' lam z)) :
    cepsScaledTrueSubtractedPair (dom.shrink σ hσ hσc) ρW lam z b =
      cepsScaledTrueSubtractedPair dom ρW lam z b := by
  have hz' : 0 ≤ z.re := hz.ge
  obtain ⟨hμ, hq, _⟩ := cepsScaledTrueFrequency_curve_bounds
    (dom.shrink σ hσ hσc) hW hθ hD M' lam hz' hb hbs'
  have hq' : ‖cepsComplexScaledDiscount lam z b‖ < (dom.shrink σ hσ hσc).q₀ :=
    hq.trans_lt (half_lt_self (dom.shrink σ hσ hσc).q₀_pos)
  have ht : ((b : ℂ) ^ 2 * z).re < σ := by
    simpa [mul_re, pow_two, hz] using hσ
  rw [← cepsScaledTrueSubtractedPair_eq_physical (dom.shrink σ hσ hσc)
      hW hθ hD M' lam hz' hb hbs',
    ← cepsScaledTrueSubtractedPair_eq_physical dom hW hθ hD M lam hz' hb hbs,
    cepsScaledTrueSubtractedPhysicalPair_shrink_eq dom hW hθ hD hσ hσc hμ hq' ht]

end PGM
