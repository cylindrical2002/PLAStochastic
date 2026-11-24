import PLAStochastic.Index.CEPS.Scaled.TruePositiveBridge

/-! # Half-line bridge subtraction at every nonzero divided denominator -/

noncomputable section
open Complex Set Metric MeasureTheory
namespace PGM

theorem cepsBridge_minus_half_eq_square (G : ℂ → ℂ) (a p : ℂ) (hS : dslope G a p ≠ 0) :
    -G p * G a / dslope G a p - (p - a) * G p = -(G p) ^ 2 / dslope G a p := by
  have hid := sub_smul_dslope G a p
  rw [smul_eq_mul] at hid
  field_simp
  linear_combination -G p * hid

theorem cepsScaledTrueBridgeCorrection_eq_square_of_nonzero {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (ρW : Measure ℝ) (lam : ℝ) (z : ℂ) (b : ℝ)
    (hS : cepsScaledTrueDenominator dom ρW lam z b ≠ 0) :
    cepsScaledTrueBridgeCorrection dom ρW lam z b =
      -(cepsScaledTrueG dom ρW lam z b (cepsScaledSignedRoot D θ ρW lam z 1 b)) ^ 2 /
        cepsScaledTrueDenominator dom ρW lam z b :=
  cepsBridge_minus_half_eq_square _ _ _ hS

theorem cepsScaledSurrogateBridgeCorrection_eq_square_of_nonzero {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (ρW : Measure ℝ) (N : ℕ) (lam : ℝ) (z b : ℂ)
    (hS : cepsScaledSurrogateDenominator dom ρW N lam z b ≠ 0) :
    cepsScaledSurrogateBridgeCorrection dom ρW N lam z b =
      -(cepsScaledSurrogateG dom ρW N lam z b (cepsScaledSignedRoot D θ ρW lam z 1 b)) ^ 2 /
        cepsScaledSurrogateDenominator dom ρW N lam z b :=
  cepsBridge_minus_half_eq_square _ _ _ hS

end PGM
