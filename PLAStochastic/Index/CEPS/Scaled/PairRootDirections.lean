import PLAStochastic.Index.CEPS.Scaled.PairPolynomialRadius

/-! # Root combinations keep their decay after insertion of the scaled marker -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledPairRoot_negative_directions (N : ℕ) (M lam : ℝ) (hlam : lam ≤ 0)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.pairPolynomialScaleBase N M / (1 + |lam| + Real.sqrt ‖z‖))) :
    (‖cepsScaledRootCoordinate D θ ρW lam z b‖ / (32 * Real.sqrt v) ≤
      ((cepsScaledSignedRoot D θ ρW lam z 1 b - b * z) * (1 + b * lam)).re) ∧
    (‖cepsScaledRootCoordinate D θ ρW lam z b‖ / (32 * Real.sqrt v) ≤
      ((cepsScaledSignedRoot D θ ρW lam z 1 b - 2 * cepsScaledSignedRoot D θ ρW lam z (-1) b + b * z) * (1 + b * lam)).re) := by
  have hbP := ball_subset_ball (pairPolynomialScaleRadius_le dom hW hθ hD N M lam z).1 hb
  have hp := (cepsScaledRoot_complex_width_directions dom hW hθ hD N M lam hz
    (ball_subset_ball (min_le_left _ _) hbP)).1 hlam
  have hc := (cepsScaledCombinedRoots_width_lower dom hW hθ hD N M lam hz hbP).2
  have ht := cepsScaledMarker_width_small dom hW hθ hD N M lam hz hb
  have hr := re_le_norm ((b * z) * (1 + b * lam))
  have hn := (neg_le_abs ((b * z) * (1 + b * lam)).re).trans
    ((abs_re_le_norm _).trans ht)
  have hcoef : 0 ≤ ‖cepsScaledRootCoordinate D θ ρW lam z b‖ * (Real.sqrt v)⁻¹ :=
    mul_nonneg (norm_nonneg _) (inv_nonneg.mpr (Real.sqrt_nonneg _))
  constructor
  · rw [sub_mul, sub_re]
    ring_nf at hp ht hr ⊢
    linarith
  · rw [add_mul, add_re]
    ring_nf at hc hn ⊢
    linarith

include hW hθ hD in
theorem cepsScaledPairRoot_positive_directions (N : ℕ) (M lam : ℝ) (hlam : 0 ≤ lam)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.pairPolynomialScaleBase N M / (1 + |lam| + Real.sqrt ‖z‖))) :
    (‖cepsScaledRootCoordinate D θ ρW lam z b‖ / (32 * Real.sqrt v) ≤
      ((-cepsScaledSignedRoot D θ ρW lam z (-1) b + b * z) * (1 + b * lam)).re) ∧
    (‖cepsScaledRootCoordinate D θ ρW lam z b‖ / (32 * Real.sqrt v) ≤
      ((2 * cepsScaledSignedRoot D θ ρW lam z 1 b - cepsScaledSignedRoot D θ ρW lam z (-1) b - b * z) * (1 + b * lam)).re) := by
  have hbP := ball_subset_ball (pairPolynomialScaleRadius_le dom hW hθ hD N M lam z).1 hb
  have hm := (cepsScaledRoot_complex_width_directions dom hW hθ hD N M lam hz
    (ball_subset_ball (min_le_left _ _) hbP)).2 hlam
  have hc := (cepsScaledCombinedRoots_width_lower dom hW hθ hD N M lam hz hbP).1
  have ht := cepsScaledMarker_width_small dom hW hθ hD N M lam hz hb
  have hr := re_le_norm ((b * z) * (1 + b * lam))
  have hn := (neg_le_abs ((b * z) * (1 + b * lam)).re).trans
    ((abs_re_le_norm _).trans ht)
  have hcoef : 0 ≤ ‖cepsScaledRootCoordinate D θ ρW lam z b‖ * (Real.sqrt v)⁻¹ :=
    mul_nonneg (norm_nonneg _) (inv_nonneg.mpr (Real.sqrt_nonneg _))
  constructor
  · rw [add_mul, add_re]
    ring_nf at hm hn ⊢
    linarith
  · rw [sub_mul, sub_re]
    ring_nf at hc ht hr ⊢
    linarith

end PGM
