import PLAStochastic.Index.CEPS.Scaled.CentralRootRadius
import PLAStochastic.Index.CEPS.Normal.QuotientSignedIdentification

/-! # Surrogate bridge before square-root descent -/

noncomputable section
open Complex Set Metric MeasureTheory
namespace PGM

def cepsScaledSignedDiscount (D θ : ℝ) (ρW : Measure ℝ) (lam r b : ℂ) : ℂ :=
  cepsMorseMin D θ ρW (b * lam) + (b * r) ^ 2

def cepsScaledSignedSurrogateG {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (N : ℕ) (lam r b ξ : ℂ) : ℂ :=
  cepsScaledBoundedSpatialG dom ρW N (b * lam)
    (cepsScaledSignedDiscount D θ ρW lam r b) (1 + b * lam) b ξ

def cepsScaledSignedSurrogateDenominator {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (N : ℕ) (lam r b : ℂ) : ℂ :=
  dslope (cepsScaledSignedSurrogateG dom ρW N lam r b)
    (cepsScaledMorseChart D θ ρW lam (-r) b) (cepsScaledMorseChart D θ ρW lam r b)

def cepsScaledSignedSurrogateBridge {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (N : ℕ) (lam r b : ℂ) : ℂ :=
  -cepsScaledSignedSurrogateG dom ρW N lam r b (cepsScaledMorseChart D θ ρW lam r b) *
    cepsScaledSignedSurrogateG dom ρW N lam r b (cepsScaledMorseChart D θ ρW lam (-r) b) /
      cepsScaledSignedSurrogateDenominator dom ρW N lam r b

end PGM
