import PLAStochastic.Index.CEPS.Scaled.CentralScaleBounds

/-! # Uniform bridge bounds on the central signed-root chart -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.centralBridgeBound {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  dom.boundedSpatialGUpper N M ^ 2 / (dom.boundedSpatialWeightLower N M / 8)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSignedSurrogateDenominator_central_lower {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m) {lam r b : ℂ}
    (hlam : ‖lam‖ ≤ dom.centralDriftRadius N M)
    (hr : ‖r‖ ≤ dom.centralCoordinateRadius N M)
    (hb : b ∈ ball (0 : ℂ) (dom.centralScaleRadius N M)) :
    dom.boundedSpatialWeightLower N M / 8 ≤
      ‖cepsScaledSignedSurrogateDenominator dom ρW N lam r b‖ := by
  obtain ⟨_, hmu, _, hp⟩ := cepsScaledCentral_chart_bounds dom hW hθ hD N M hlam hr hb
  have hm := (cepsScaledCentral_chart_bounds dom hW hθ hD N M hlam
    (show ‖-r‖ ≤ dom.centralCoordinateRadius N M by simpa using hr) hb).2.2.2
  obtain ⟨hbc, _, hbP, hq, hw⟩ := cepsScaledCentral_scale_bounds dom hW hθ hD N M hlam hr hb
  have hR := boundedSpatialRootRadius_pos dom hW hθ hD N M
  exact cepsScaledBoundedSpatialSlope_lower dom hW hθ hD hf hη hM N hN hmu.le hq hw hbc hbP
    (hm.trans (by linarith)) (hp.trans (by linarith))

include hW hθ hD in
theorem cepsScaledSignedSurrogateBridge_central_bound {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m) {lam r b : ℂ}
    (hlam : ‖lam‖ ≤ dom.centralDriftRadius N M)
    (hr : ‖r‖ ≤ dom.centralCoordinateRadius N M)
    (hb : b ∈ ball (0 : ℂ) (dom.centralScaleRadius N M)) :
    ‖cepsScaledSignedSurrogateBridge dom ρW N lam r b‖ ≤ dom.centralBridgeBound N M := by
  obtain ⟨_, hmu, _, hp⟩ := cepsScaledCentral_chart_bounds dom hW hθ hD N M hlam hr hb
  have hm := (cepsScaledCentral_chart_bounds dom hW hθ hD N M hlam
    (show ‖-r‖ ≤ dom.centralCoordinateRadius N M by simpa using hr) hb).2.2.2
  obtain ⟨hbc, _, _, hq, hw⟩ := cepsScaledCentral_scale_bounds dom hW hθ hD N M hlam hr hb
  have hw2 : ‖1 + b * lam‖ ≤ 2 := by
    have ht := norm_add_le ((1 + b * lam) - 1) (1 : ℂ)
    rw [sub_add_cancel, norm_one] at ht
    linarith
  have hB := (cepsScaledBoundedSpatialG_budget dom hW hθ hD hf hη hM N hN hmu.le hq hw2 hbc).2
  have hsmall : dom.boundedSpatialRootRadius N M / 4 < 1 := by
    have hR : dom.boundedSpatialRootRadius N M ≤ 1 / 4 := min_le_left _ _
    linarith
  have hBp := hB _ (mem_ball_zero_iff.mpr (hp.trans_lt hsmall))
  have hBm := hB _ (mem_ball_zero_iff.mpr (hm.trans_lt hsmall))
  have hden := cepsScaledSignedSurrogateDenominator_central_lower dom hW hθ hD hf hη hM N hN hlam hr hb
  have hlo : 0 < dom.boundedSpatialWeightLower N M / 8 := div_pos
    (boundedSpatialWeightLower_pos dom hD N M) (by norm_num)
  have hnum := mul_le_mul hBp hBm (norm_nonneg _)
    (boundedSpatialGUpper_pos dom hW hθ hD N M).le
  rw [cepsScaledSignedSurrogateBridge, norm_div, norm_mul, norm_neg]
  exact div_le_div₀ (sq_nonneg _)
    (by simpa only [pow_two, cepsScaledSignedSurrogateG] using hnum) hlo hden

theorem cepsScaledSignedSurrogateBridge_neg (N : ℕ) (lam r b : ℂ) :
    cepsScaledSignedSurrogateBridge dom ρW N lam (-r) b =
      cepsScaledSignedSurrogateBridge dom ρW N lam r b := by
  have hg : cepsScaledSignedSurrogateG dom ρW N lam (-r) b =
      cepsScaledSignedSurrogateG dom ρW N lam r b := by
    unfold cepsScaledSignedSurrogateG cepsScaledSignedDiscount
    rw [mul_neg, neg_sq]
  unfold cepsScaledSignedSurrogateBridge cepsScaledSignedSurrogateDenominator
  rw [hg, neg_neg, cepsNormal_dslope_swap]
  ring

end PGM
