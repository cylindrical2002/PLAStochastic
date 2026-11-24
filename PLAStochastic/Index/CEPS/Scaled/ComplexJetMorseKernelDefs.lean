import PLAStochastic.Index.CEPS.Scaled.ComplexJetMorseScaleRoot
import PLAStochastic.Index.CEPS.Scaled.ComplexJetMinimumUnit

/-! # Signed Morse coordinates: energy, frequency and the two scaled Morse nodes -/

noncomputable section
open Complex
namespace PGM

abbrev CepsComplexJetMorseParam (d : ℕ) := ((Fin d → ℂ) × ℂ) × ℂ

def cepsComplexJetMorseEnergy (d N : ℕ) (η : (Fin d → ℂ) × ℂ → ℂ)
    (u : CepsComplexJetMorseParam d × ℂ) : ℂ :=
  u.2 ^ 2 + u.1.1.2 ^ 2 * cepsComplexCgfJetMinimumUnit d N η
    (u.1.1.1, u.1.2 * u.1.1.2)

def cepsComplexJetMorseFrequency (d N : ℕ) (η : (Fin d → ℂ) × ℂ → ℂ)
    (u : CepsComplexJetMorseParam d × ℂ) : ℂ :=
  cepsComplexJetMorseEnergy d N η u / (1 + u.1.2 * u.1.1.2)

def cepsComplexJetMorseNode (d : ℕ) (Θ : ((Fin d → ℂ) × ℂ) × ℂ → ℂ)
    (sgn : ℂ) (u : CepsComplexJetMorseParam d × ℂ) : ℂ :=
  cepsComplexJetMorseScaleRoot d Θ u.1.1.1 u.1.1.2 (sgn * u.2) u.1.2

end PGM
