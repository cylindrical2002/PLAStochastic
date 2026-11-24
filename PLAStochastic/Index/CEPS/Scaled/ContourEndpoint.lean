import PLAStochastic.Index.CEPS.Contour.NormalForms
import PLAStochastic.Index.CEPS.Scaled.EndpointActualRadius

/-! # Exact contour transfer of the physical and filled marked endpoint -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)
variable {σ : ℝ} (hσ : 0 < σ) (hσc : σ ≤ dom.c₀)

include hW hθ hD in
theorem cepsNormalHalfPrimitive_shrink_eq {μ : ℝ}
    (hμ : |μ| ≤ (dom.shrink σ hσ hσc).μ₀) {q t w : ℂ}
    (hq : ‖q‖ ≤ (dom.shrink σ hσ hσc).q₀) (ht : t.re < σ) :
    cepsNormalHalfPrimitive (cepsCgf ρW) (fun x q => cepsRootPlus D θ ρW x q)
      (fun x q t => cepsD ρW x q t) ((dom.shrink σ hσ hσc).canonL ρW) μ q t w =
    cepsNormalHalfPrimitive (cepsCgf ρW) (fun x q => cepsRootPlus D θ ρW x q)
      (fun x q t => cepsD ρW x q t) (dom.canonL ρW) μ q t w := by
  have hp := (dom.normalRoots_mem_shrink hW hθ hD hσ hσc hμ hq).1
  change (cepsRootPlus D θ ρW μ q).re < σ at hp
  unfold cepsNormalHalfPrimitive
  rw [dom.shrink_canonL_eq hW hθ hD hσ hσc hμ hq ht,
    dom.shrink_canonL_eq hW hθ hD hσ hσc hμ hq hp]

include hW hθ hD in
theorem cepsScaledMarkedEndpoint_shrink_eq {b : ℝ} (hb : 0 < b) {z : ℂ}
    (hμ : |b| ≤ (dom.shrink σ hσ hσc).μ₀)
    (hq : ‖cepsComplexScaledDiscount 1 z b‖ ≤ (dom.shrink σ hσ hσc).q₀)
    (ht : ((b : ℂ) ^ 2 * z).re < σ)
    (hmark : (b : ℂ) ^ 2 * z ∈ ball (0 : ℂ) (cepsMarkedUnitRadius D θ)) :
    cepsScaledMarkedEndpoint (dom.shrink σ hσ hσc) ρW b z =
      cepsScaledMarkedEndpoint dom ρW b z := by
  by_cases hz : z = 0
  · subst z
    rw [cepsScaledMarkedEndpoint_zero, cepsScaledMarkedEndpoint_zero]
  · rw [cepsScaledMarkedEndpoint_eq_physical (dom.shrink σ hσ hσc) hW hθ hD hb hz hmark,
      cepsScaledMarkedEndpoint_eq_physical dom hW hθ hD hb hz hmark]
    have hq' : ‖(b : ℂ) ^ 2 * z * (1 + (b : ℂ))‖ ≤
        (dom.shrink σ hσ hσc).q₀ := by
      simpa only [cepsComplexScaledDiscount, ofReal_one, mul_one] using hq
    rw [cepsNormalHalfPrimitive_shrink_eq dom hW hθ hD hσ hσc hμ hq' ht]

include hW hθ hD in
theorem cepsScaledMarkedEndpoint_shrink_eq_on_disc (M : ℝ) {z : ℂ} (hz : z.re = 0)
    {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ)
      ((dom.shrink σ hσ hσc).trueEndpointScaleRadius M z)) :
    cepsScaledMarkedEndpoint (dom.shrink σ hσ hσc) ρW b z =
      cepsScaledMarkedEndpoint dom ρW b z := by
  obtain ⟨hμ, hq, hmark⟩ := cepsScaledTrueEndpoint_curve_bounds
    (dom.shrink σ hσ hσc) hW hθ hD M hz.ge hbs
  have ht : ((b : ℂ) ^ 2 * z).re < σ := by
    simpa [mul_re, pow_two, hz] using hσ
  exact cepsScaledMarkedEndpoint_shrink_eq dom hW hθ hD hσ hσc hb hμ hq.le ht hmark

end PGM
