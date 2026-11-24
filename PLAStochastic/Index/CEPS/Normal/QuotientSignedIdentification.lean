import PLAStochastic.Index.CEPS.Normal.ActualQuotientDisc

/-! # Quotient identification before choosing a square-root branch -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

theorem cepsMorseQ_eq_cepsQ_of_morse_bounds
    {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
    (hθ : 0 < θ) (hD : 0 < D) {μ r : ℂ}
    (hμ : ‖μ‖ ≤ dom.μ₀) (hr : ‖r‖ < dom.rmax) (ζ : ℂ) :
    cepsMorseQ D θ ρW μ r ζ =
      cepsQ D θ ρW μ (cepsMorseMin D θ ρW μ + r ^ 2) ζ := by
  have hsq : (sqrt ((cepsMorseMin D θ ρW μ + r ^ 2) - cepsMorseMin D θ ρW μ)) ^ 2 = r ^ 2 := by
    rw [sqrt_sq_eq]
    ring
  have hi := cepsMorseQ_sqrt_eq_cepsQ D θ ρW μ (cepsMorseMin D θ ρW μ + r ^ 2) ζ
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · rw [h] at hi
    exact hi
  · rw [h, cepsMorseQ_neg dom hW hθ hD hμ hr] at hi
    exact hi

end PGM
