import PLAStochastic.Index.CEPS.Scaled.QuotientCurve

/-! # Actual quotient identification without a frequency half-plane restriction -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledQuotient_eq_actual_of_morse_bounds (lam : ℝ) (z b ζ : ℂ)
    (hμ : ‖b * (lam : ℂ)‖ ≤ dom.μ₀)
    (hr : ‖b * cepsScaledRootCoordinate D θ ρW lam z b‖ < dom.rmax) :
    cepsScaledQuotient D θ ρW lam z b ζ =
      cepsQ D θ ρW (b * lam) (cepsComplexScaledDiscount lam z b) ζ := by
  let r := b * cepsScaledRootCoordinate D θ ρW lam z b
  have hsq : (cepsRootR D θ ρW (b * lam) (cepsComplexScaledDiscount lam z b)) ^ 2 = r ^ 2 := by
    rw [cepsRootR, sqrt_sq_eq, cepsComplexScaledDiscount,
      cepsScaledMorseRadicand_actual hW hθ hD (dom.μ_lt_chart hμ)]
    dsimp [r]
    rw [mul_pow, cepsScaledRootCoordinate, sqrt_sq_eq]
  have hp : b * cepsScaledSignedRoot D θ ρW lam z 1 b = cepsMorseRoot D θ ρW (b * lam) r := by
    simpa only [mul_one] using cepsScaledRootCurve_eq_morse hW hθ hD lam z 1 b
  have hm : b * cepsScaledSignedRoot D θ ρW lam z (-1) b = cepsMorseRoot D θ ρW (b * lam) (-r) := by
    simpa only [mul_neg_one, neg_mul] using cepsScaledRootCurve_eq_morse hW hθ hD lam z (-1) b
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsq with he | he
  · rw [cepsScaledQuotient, hp, hm, cepsQ, cepsRootPlus, cepsRootMinus, he]
  · have hM := (differentiableOn_stepTransform_ball hW hθ hD.le).mono
      (ball_subset_ball (show dom.ρA ≤ θ / 2 by
        have := CepsC6.ρA_lt_cgfRadius dom hθ hD
        have := cepsCgfRadius_le (D := D) (θ := θ)
        linarith))
    have hG : DifferentiableOn ℂ
        (fun w => -cepsD ρW (b * lam) (cepsComplexScaledDiscount lam z b) w)
        (ball 0 dom.ρA) := by
      unfold cepsD
      fun_prop
    have hpr := cepsMorseRoot_mem_rootZone dom hW hθ hD hμ hr
    have hmr := cepsMorseRoot_mem_rootZone dom hW hθ hD hμ (r := -r) (by simpa [r] using hr)
    rw [cepsScaledQuotient, hp, hm, cepsQ, cepsRootPlus, cepsRootMinus, he, neg_neg]
    exact (cepsNormal_second_dslope_swap
      ((hG _ hpr).differentiableAt (isOpen_ball.mem_nhds hpr))
      ((hG _ hmr).differentiableAt (isOpen_ball.mem_nhds hmr)) ζ).symm

end PGM
