import PLAStochastic.Index.CEPS.Final.Defs
import PLAStochastic.Index.CEPS.Scaled.KernelNormalModel

/-! # Concrete finite-jet mean and low-band coefficients -/

noncomputable section
namespace PGM

/-- The real mean coefficient; reality on input classes is proved in `KernelMean`. -/
def cepsKernelCs (j : ℕ) (p : ℕ → ℝ) : ℝ := (cepsKernelMeanCoeffJetModel p j).re

/-- The genuine normal coefficient on the imaginary axis, expressed in finite input jets. -/
def cepsKernelGk (j : ℕ) (p : ℕ → ℝ) (y : ℝ) : ℂ :=
  cepsKernelNormalCoeffJetModel p j (Complex.I * y)

end PGM
