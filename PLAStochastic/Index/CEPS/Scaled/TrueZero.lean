import PLAStochastic.Index.CEPS.Scaled.TrueEntranceError

/-! # Exact zero-drift agreement of the actual and surrogate scaled forms

This includes zero scale at every scaled drift. The actual canonical
factor has no drift approximation error at zero drift; the agreement
holds as an identity of spatial functions, so every collision is retained.
-/

noncomputable section
open Complex MeasureTheory
namespace PGM

variable {D θ v : ℝ} (dom : CepsCanonDomain D θ v) (ρW : Measure ℝ)

theorem cepsScaledTrueG_eq_surrogate_of_drift_zero (N : ℕ) (lam : ℝ) (z : ℂ) {b : ℝ}
    (hμ : b * lam = 0) : cepsScaledTrueG dom ρW lam z b = cepsScaledSurrogateG dom ρW N lam z b := by
  have hC : (b : ℂ) * lam = 0 := by rw [← ofReal_mul, hμ, ofReal_zero]
  funext ξ
  unfold cepsScaledTrueG cepsScaledSurrogateG cepsCanonTrueWeight cepsCanonSurrogateWeight
  rw [hμ, hC, ofReal_zero, cepsCanonDriftTaylor_zero]

theorem cepsScaledTrueMarkPrefactor_eq_surrogate_of_drift_zero (N : ℕ) (lam : ℝ) (z : ℂ) {b : ℝ}
    (hμ : b * lam = 0) :
    cepsScaledTrueMarkPrefactor dom ρW lam z b = cepsScaledSurrogateMarkPrefactor dom ρW N lam z b := by
  have hC : (b : ℂ) * lam = 0 := by rw [← ofReal_mul, hμ, ofReal_zero]
  unfold cepsScaledTrueMarkPrefactor cepsScaledSurrogateMarkPrefactor
  rw [hC, cepsCanonDriftTaylor_zero]

theorem cepsScaledTrueDenominator_eq_surrogate_of_drift_zero (N : ℕ) (lam : ℝ) (z : ℂ) {b : ℝ}
    (hμ : b * lam = 0) :
    cepsScaledTrueDenominator dom ρW lam z b = cepsScaledSurrogateDenominator dom ρW N lam z b := by
  unfold cepsScaledTrueDenominator cepsScaledSurrogateDenominator
  rw [cepsScaledTrueG_eq_surrogate_of_drift_zero dom ρW N lam z hμ]

theorem cepsScaledTrueBridge_eq_surrogate_of_drift_zero (N : ℕ) (lam : ℝ) (z : ℂ) {b : ℝ}
    (hμ : b * lam = 0) : cepsScaledTrueBridge dom ρW lam z b = cepsScaledSurrogateBridge dom ρW N lam z b := by
  unfold cepsScaledTrueBridge cepsScaledSurrogateBridge
  rw [cepsScaledTrueG_eq_surrogate_of_drift_zero dom ρW N lam z hμ,
    cepsScaledTrueDenominator_eq_surrogate_of_drift_zero dom ρW N lam z hμ]

theorem cepsScaledTrueEntrance_eq_surrogate_of_drift_zero (N : ℕ) (lam : ℝ) (z : ℂ) {b : ℝ}
    (hμ : b * lam = 0) : cepsScaledTrueEntrance dom ρW lam z b = cepsScaledSurrogateEntrance dom ρW N lam z b := by
  rw [cepsScaledSurrogateEntrance_eq_prefactor]
  unfold cepsScaledTrueEntrance cepsScaledTrueEntranceNumerator
  rw [cepsScaledTrueG_eq_surrogate_of_drift_zero dom ρW N lam z hμ,
    cepsScaledTrueMarkPrefactor_eq_surrogate_of_drift_zero dom ρW N lam z hμ,
    cepsScaledTrueDenominator_eq_surrogate_of_drift_zero dom ρW N lam z hμ]

theorem cepsScaledTrueBridge_zero (N : ℕ) (lam : ℝ) (z : ℂ) :
    cepsScaledTrueBridge dom ρW lam z 0 = cepsScaledSurrogateBridge dom ρW N lam z 0 :=
  cepsScaledTrueBridge_eq_surrogate_of_drift_zero dom ρW N lam z (by simp)

theorem cepsScaledTrueEntrance_zero (N : ℕ) (lam : ℝ) (z : ℂ) :
    cepsScaledTrueEntrance dom ρW lam z 0 = cepsScaledSurrogateEntrance dom ρW N lam z 0 :=
  cepsScaledTrueEntrance_eq_surrogate_of_drift_zero dom ρW N lam z (by simp)

end PGM
