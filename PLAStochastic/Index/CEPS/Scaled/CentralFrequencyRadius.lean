import PLAStochastic.Index.CEPS.Scaled.SignedBridgeDescent
import PLAStochastic.Index.CEPS.Scaled.Radicand

/-! # Class-controlled central complex-frequency discs -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.centralFrequencyDriftRadius {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  min (dom.centralDriftRadius N M)
    (dom.centralCoordinateRadius N M ^ 2 / (64 * (1 + dom.morseMinUnitBound)))

def CepsCanonDomain.centralFrequencyRadius {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  dom.centralCoordinateRadius N M ^ 2 / 16

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem centralFrequencyDriftRadius_pos (N : ℕ) (M : ℝ) :
    0 < dom.centralFrequencyDriftRadius N M := by
  have hR := centralCoordinateRadius_pos dom hW hθ hD N M
  have hU : 0 ≤ dom.morseMinUnitBound := by unfold CepsCanonDomain.morseMinUnitBound; positivity
  exact lt_min (centralDriftRadius_pos dom hW hθ hD N M) (by positivity)

include hW hθ hD in
theorem centralFrequencyRadius_pos (N : ℕ) (M : ℝ) :
    0 < dom.centralFrequencyRadius N M := by
  have := centralCoordinateRadius_pos dom hW hθ hD N M
  unfold CepsCanonDomain.centralFrequencyRadius
  positivity

include hW hθ hD in
theorem cepsScaledCentral_radicand_bounds (N : ℕ) (M : ℝ) {lam z b : ℂ}
    (hlam : ‖lam‖ ≤ dom.centralFrequencyDriftRadius N M)
    (hz : ‖z‖ ≤ dom.centralFrequencyRadius N M)
    (hb : b ∈ ball (0 : ℂ) (dom.centralScaleRadius N M)) :
    ‖cepsScaledMorseRadicand D θ ρW lam z b‖ < dom.centralCoordinateRadius N M ^ 2 / 2 := by
  have hL : ‖lam‖ ≤ dom.centralDriftRadius N M := hlam.trans (min_le_left _ _)
  have hL1 : ‖lam‖ ≤ 1 := hL.trans (min_le_left _ _)
  have hR := centralCoordinateRadius_pos dom hW hθ hD N M
  have hmu := (cepsScaledCentral_chart_bounds dom hW hθ hD N M hL
    (show ‖(0 : ℂ)‖ ≤ dom.centralCoordinateRadius N M by simpa using hR.le) hb).2.1
  have hUnit := (cepsMorseMinUnit_class_budget dom hW hθ hD).2 (b * lam)
    (mem_ball_zero_iff.mpr (hmu.trans (by linarith [dom.μ₀_pos])))
  have hU : 0 ≤ dom.morseMinUnitBound := by unfold CepsCanonDomain.morseMinUnitBound; positivity
  have hmuHalf : ‖b * lam‖ ≤ 1 / 2 := by
    have hw := (cepsScaledCentral_scale_bounds dom hW hθ hD N M hL
      (show ‖(0 : ℂ)‖ ≤ dom.centralCoordinateRadius N M by simpa using hR.le) hb).2.2.2.2
    simpa only [add_sub_cancel_left] using hw
  have hw2 : ‖1 + b * lam‖ ≤ 2 := (norm_add_le (1 : ℂ) (b * lam)).trans
    (by rw [norm_one]; linarith)
  have hLamSmall := (le_div_iff₀ (by positivity : 0 < 64 * (1 + dom.morseMinUnitBound))).mp
    (hlam.trans (min_le_right _ _))
  have hLamSq : ‖lam‖ ^ 2 ≤ ‖lam‖ := by nlinarith [norm_nonneg lam]
  have hmin : ‖lam‖ ^ 2 * ‖cepsMorseMinUnit D θ ρW (b * lam)‖ ≤
      dom.centralCoordinateRadius N M ^ 2 / 64 := by
    have hle := (mul_le_mul_of_nonneg_left hUnit (sq_nonneg ‖lam‖)).trans
      (mul_le_mul_of_nonneg_right hLamSq hU)
    have hlast : ‖lam‖ * dom.morseMinUnitBound ≤ dom.centralCoordinateRadius N M ^ 2 / 64 := by
      nlinarith [norm_nonneg lam]
    exact hle.trans hlast
  have hnorm := norm_sub_le (z * (1 + b * lam)) (lam ^ 2 * cepsMorseMinUnit D θ ρW (b * lam))
  rw [norm_mul, norm_mul, norm_pow] at hnorm
  have hzterm := mul_le_mul hz hw2 (norm_nonneg _) (by
    unfold CepsCanonDomain.centralFrequencyRadius; positivity)
  change ‖cepsScaledMorseRadicand D θ ρW lam z b‖ ≤ _ at hnorm
  unfold CepsCanonDomain.centralFrequencyRadius at hzterm
  nlinarith [sq_pos_of_pos hR]

end PGM
