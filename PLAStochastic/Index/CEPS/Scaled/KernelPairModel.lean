import PLAStochastic.Index.CEPS.Scaled.KernelHalfFactors

/-! # Explicit finite mixed-jet complete pair and half-line subtraction models -/

noncomputable section
open Complex
namespace PGM

def cepsKernelPairJetModel (p : ℕ → ℝ) (N : ℕ) (lam : ℝ) (z b : ℂ) : ℂ :=
  exp ((b * z) * (1 + b * lam)) * (cepsKernelEntranceJetModel p N lam z b) ^ 2 *
    (-(1 / (1 + b * lam)) * deriv (fun w => cepsKernelBridgeJetModel p N lam w b) z -
      b * cepsKernelBridgeJetModel p N lam z b)

def cepsKernelHalfPairJetModel (p : ℕ → ℝ) (N : ℕ) (lam : ℝ) (z b : ℂ) : ℂ :=
  exp ((b * z) * (1 + b * lam)) * (cepsKernelHalfEntranceJetModel p N lam z b) ^ 2 *
    (-(1 / (1 + b * lam)) * deriv (fun w => cepsKernelHalfBridgeJetModel p N lam w b) z -
      b * cepsKernelHalfBridgeJetModel p N lam z b)

def cepsKernelSubtractedPairJetModel (p : ℕ → ℝ) (N : ℕ) (lam : ℝ) (z b : ℂ) : ℂ :=
  cepsKernelPairJetModel p N lam z b - if 1 ≤ lam then cepsKernelHalfPairJetModel p N lam z b else 0

theorem cepsKernelPairModels_congr {p p' : ℕ → ℝ} (N : ℕ)
    (hp : ∀ i, i < cepsJetDim (4 * N) → p i = p' i) (lam : ℝ) (z : ℂ) :
    cepsKernelPairJetModel p N lam z = cepsKernelPairJetModel p' N lam z ∧
    cepsKernelHalfPairJetModel p N lam z = cepsKernelHalfPairJetModel p' N lam z ∧
    cepsKernelSubtractedPairJetModel p N lam z = cepsKernelSubtractedPairJetModel p' N lam z := by
  have hB (w : ℂ) := (cepsKernelFiniteFactors_congr N hp lam w).2.2.1
  have hE := (cepsKernelFiniteFactors_congr N hp lam z).2.2.2
  have hHB (w : ℂ) := (cepsKernelHalfFactors_congr N hp lam w).2.1
  have hHE := (cepsKernelHalfFactors_congr N hp lam z).1
  have hdB (b : ℂ) : (fun w => cepsKernelBridgeJetModel p N lam w b) =
      (fun w => cepsKernelBridgeJetModel p' N lam w b) := by funext w; rw [hB w]
  have hdHB (b : ℂ) : (fun w => cepsKernelHalfBridgeJetModel p N lam w b) =
      (fun w => cepsKernelHalfBridgeJetModel p' N lam w b) := by funext w; rw [hHB w]
  have heP : cepsKernelPairJetModel p N lam z = cepsKernelPairJetModel p' N lam z := by
    funext b; simp only [cepsKernelPairJetModel, hE, hB z, hdB]
  have heH : cepsKernelHalfPairJetModel p N lam z = cepsKernelHalfPairJetModel p' N lam z := by
    funext b; simp only [cepsKernelHalfPairJetModel, hHE, hHB z, hdHB]
  exact ⟨heP, heH, by funext b; simp only [cepsKernelSubtractedPairJetModel, heP, heH]⟩

end PGM
