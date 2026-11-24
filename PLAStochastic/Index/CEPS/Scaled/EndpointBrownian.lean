import PLAStochastic.Index.CEPS.Scaled.EndpointScaleLimit

/-! # The variance-dependent Brownian limit of the marked endpoint -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def cepsBrownianMarkedEndpoint (V : ℝ) (z : ℂ) : ℂ :=
  let r := Complex.sqrt (2 / (V : ℂ)) * Complex.sqrt (z + 1 / (2 * (V : ℂ)))
  exp (1 / (V : ℂ) - r) * (2 * r) / (1 / (V : ℂ) + r)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrueRegularEndpoint_eq_brownian {z : ℂ} (hz : 0 ≤ z.re) :
    cepsScaledTrueRegularEndpoint dom ρW z 0 = cepsBrownianMarkedEndpoint (cepsStepVar ρW) z := by
  rw [cepsScaledTrueRegularEndpoint_scale_zero dom hW hθ hD hz,
    cepsScaledSignedRoot_zero dom hW hθ hD 1 hz 1,
    cepsScaledSignedRoot_zero dom hW hθ hD 1 hz (-1)]
  simp only [ofReal_one, one_pow, one_mul, neg_mul]
  unfold cepsBrownianMarkedEndpoint
  rw [show -(-(1 : ℂ) / cepsStepVar ρW +
      Complex.sqrt (2 / (cepsStepVar ρW : ℂ)) *
        Complex.sqrt (z + 1 / (2 * (cepsStepVar ρW : ℂ)))) =
      1 / (cepsStepVar ρW : ℂ) - Complex.sqrt (2 / (cepsStepVar ρW : ℂ)) *
        Complex.sqrt (z + 1 / (2 * (cepsStepVar ρW : ℂ))) by ring]
  congr 1 <;> ring

end PGM
