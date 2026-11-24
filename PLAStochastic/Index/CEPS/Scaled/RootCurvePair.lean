import PLAStochastic.Index.CEPS.Scaled.CanonScaleCurve
import PLAStochastic.Index.CEPS.Normal.ActualQuotient

/-! # Actual unordered roots along the complex scale curve

The scaled coordinate need not have the principal sign for complex scale.
The unordered pair is nevertheless the exact actual root pair, including
zero scale and root merging.
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledRootCurve_eq_morse (lam : ℝ) (z sign b : ℂ) :
    b * cepsScaledSignedRoot D θ ρW lam z sign b =
      cepsMorseRoot D θ ρW (b * lam) (b * sign * cepsScaledRootCoordinate D θ ρW lam z b) := by
  by_cases hb : b = 0
  · subst b
    rw [zero_mul, zero_mul, zero_mul, zero_mul,
      cepsMorseRoot_zero hW hθ hD (by simpa using cepsChartMu_pos hD hθ),
      cepsMorseCenter_at_zero hW hθ hD]
  · rw [cepsScaledSignedRoot_eq_div hW hθ hD lam z sign hb,
      mul_div_cancel₀ _ hb]

include hW hθ hD in
theorem cepsScaledRootCurve_pair (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z)) :
    (b * cepsScaledSignedRoot D θ ρW lam z 1 b,
      b * cepsScaledSignedRoot D θ ρW lam z (-1) b) =
      (cepsRootPlus D θ ρW (b * lam) (cepsComplexScaledDiscount lam z b),
        cepsRootMinus D θ ρW (b * lam) (cepsComplexScaledDiscount lam z b)) ∨
    (b * cepsScaledSignedRoot D θ ρW lam z 1 b,
      b * cepsScaledSignedRoot D θ ρW lam z (-1) b) =
      (cepsRootMinus D θ ρW (b * lam) (cepsComplexScaledDiscount lam z b),
        cepsRootPlus D θ ρW (b * lam) (cepsComplexScaledDiscount lam z b)) := by
  have hμ := (canonScaleCurve_bounds dom hW hθ hD lam hz (sign := 1) (by norm_num) hb).1
  have hmc : ‖b * (lam : ℂ)‖ < cepsChartMu D θ :=
    dom.μ_lt_chart (hμ.le.trans (by linarith [dom.μ₀_pos]))
  let r := b * cepsScaledRootCoordinate D θ ρW lam z b
  have hsq : (cepsRootR D θ ρW (b * lam) (cepsComplexScaledDiscount lam z b)) ^ 2 = r ^ 2 := by
    rw [cepsRootR, sqrt_sq_eq, cepsComplexScaledDiscount,
      cepsScaledMorseRadicand_actual hW hθ hD hmc]
    dsimp [r]
    rw [mul_pow, cepsScaledRootCoordinate, sqrt_sq_eq]
  have hp : b * cepsScaledSignedRoot D θ ρW lam z 1 b = cepsMorseRoot D θ ρW (b * lam) r := by
    simpa only [mul_one] using cepsScaledRootCurve_eq_morse hW hθ hD lam z 1 b
  have hm : b * cepsScaledSignedRoot D θ ρW lam z (-1) b = cepsMorseRoot D θ ρW (b * lam) (-r) := by
    simpa only [mul_neg_one, neg_mul] using cepsScaledRootCurve_eq_morse hW hθ hD lam z (-1) b
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsq with hr | hr
  · left
    rw [hp, hm, cepsRootPlus, cepsRootMinus, hr]
  · right
    rw [hp, hm, cepsRootPlus, cepsRootMinus, hr, neg_neg]

end PGM
