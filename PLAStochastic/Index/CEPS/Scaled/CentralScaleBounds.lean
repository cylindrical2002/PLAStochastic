import PLAStochastic.Index.CEPS.Scaled.SignedSurrogateDefs

/-! # Coordinate budgets on the central signed-root chart -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledCentral_scale_bounds (N : ℕ) (M : ℝ) {lam r b : ℂ}
    (hlam : ‖lam‖ ≤ dom.centralDriftRadius N M)
    (hr : ‖r‖ ≤ dom.centralCoordinateRadius N M)
    (hb : b ∈ ball (0 : ℂ) (dom.centralScaleRadius N M)) :
    ‖b‖ ≤ dom.c₀ / 4 ∧ ‖b‖ ≤ 1 / 2 ∧
      ‖b‖ ≤ 1 / (4 * (1 + dom.canonSurrogatePiBound N M)) ∧
      ‖cepsScaledSignedDiscount D θ ρW lam r b‖ < dom.q₀ / 2 ∧
      ‖(1 + b * lam) - 1‖ ≤ 1 / 2 := by
  have hbn := mem_ball_zero_iff.mp hb
  have hbc : ‖b‖ ≤ dom.c₀ / 4 := hbn.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hbhalf : ‖b‖ ≤ 1 / 2 := hbn.le.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hbP : ‖b‖ ≤ 1 / (4 * (1 + dom.canonSurrogatePiBound N M)) := hbn.le.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hbq : ‖b‖ < dom.q₀ / (8 * (1 + dom.morseMinUnitBound + dom.centralCoordinateRadius N M ^ 2)) :=
    hbn.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))
  have hlam1 : ‖lam‖ ≤ 1 := hlam.trans (min_le_left _ _)
  obtain ⟨_, hmu, _, _⟩ := cepsScaledCentral_chart_bounds dom hW hθ hD N M hlam hr hb
  have hmuHalf : b * lam ∈ ball (0 : ℂ) (dom.μ₀ / 2) := mem_ball_zero_iff.mpr
    (hmu.trans (by linarith [dom.μ₀_pos]))
  have hUnit := (cepsMorseMinUnit_class_budget dom hW hθ hD).2 _ hmuHalf
  have hU : 0 ≤ dom.morseMinUnitBound := by
    unfold CepsCanonDomain.morseMinUnitBound
    positivity
  have hR := centralCoordinateRadius_pos dom hW hθ hD N M
  have hcoef : ‖lam‖ ^ 2 * ‖cepsMorseMinUnit D θ ρW (b * lam)‖ + ‖r‖ ^ 2 ≤
      1 + dom.morseMinUnitBound + dom.centralCoordinateRadius N M ^ 2 := by
    have h1 := mul_le_mul (pow_le_pow_left₀ (norm_nonneg lam) hlam1 2) hUnit
      (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 ^ 2)
    have h2 := pow_le_pow_left₀ (norm_nonneg r) hr 2
    norm_num only [one_pow, one_mul] at h1
    linarith
  have hqnorm : ‖cepsScaledSignedDiscount D θ ρW lam r b‖ ≤
      ‖b‖ ^ 2 * (‖lam‖ ^ 2 * ‖cepsMorseMinUnit D θ ρW (b * lam)‖ + ‖r‖ ^ 2) := by
    unfold cepsScaledSignedDiscount
    rw [cepsMorseMin_eq_sq_mul_unit hW hθ hD (dom.μ_lt_chart
      (hmu.le.trans (by linarith [dom.μ₀_pos])))]
    apply (norm_add_le _ _).trans_eq
    rw [norm_mul, norm_pow, norm_mul, norm_pow, norm_mul]
    ring
  have hQ : ‖cepsScaledSignedDiscount D θ ρW lam r b‖ < dom.q₀ / 2 := by
    let C := 1 + dom.morseMinUnitBound + dom.centralCoordinateRadius N M ^ 2
    have hC : 0 < C := by dsimp [C]; positivity
    have hbC := (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 8) hC)).mp hbq
    have hb1 : ‖b‖ ≤ 1 := by linarith
    have hs : ‖b‖ ^ 2 ≤ ‖b‖ := by nlinarith [norm_nonneg b]
    have hsmall : ‖b‖ * C < dom.q₀ / 8 := by nlinarith
    have hle := (hqnorm.trans (mul_le_mul_of_nonneg_left hcoef (sq_nonneg ‖b‖))).trans
      (mul_le_mul_of_nonneg_right hs hC.le)
    exact hle.trans_lt (hsmall.trans (by linarith [dom.q₀_pos]))
  have hw : ‖(1 + b * lam) - 1‖ ≤ 1 / 2 := by
    rw [add_sub_cancel_left, norm_mul]
    exact (mul_le_mul_of_nonneg_left hlam1 (norm_nonneg b)).trans (by simpa using hbhalf)
  exact ⟨hbc, hbhalf, hbP, hQ, hw⟩

end PGM
