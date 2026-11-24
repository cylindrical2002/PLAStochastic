import PLAStochastic.Index.CEPS.Scaled.TruePairRadius
import PLAStochastic.Index.CEPS.Normal.NegativeDiscountDerivatives

/-! # Scaled root bounds in genuine complex frequency neighborhoods -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.scaledFrequencyRadius {D θ v : ℝ} (dom : CepsCanonDomain D θ v) : ℝ :=
  dom.normalDiscountRadius / 8

def CepsCanonDomain.frequencyRootBound {D θ v : ℝ} (dom : CepsCanonDomain D θ v) : ℝ :=
  2 + dom.μ₀ + dom.morseMinUnitBound + dom.scaledFrequencyRadius

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hD in
theorem scaledFrequencyRadius_pos : 0 < dom.scaledFrequencyRadius :=
  div_pos (cepsNormal_discountRadius_pos dom hD) (by norm_num)

include hD in
theorem frequencyRootBound_pos : 0 < dom.frequencyRootBound := by
  have := dom.μ₀_pos
  have := scaledFrequencyRadius_pos dom hD
  have hU : 0 ≤ dom.morseMinUnitBound := by unfold CepsCanonDomain.morseMinUnitBound; positivity
  unfold CepsCanonDomain.frequencyRootBound
  positivity

include hW hθ hD in
theorem cepsScaledRootCoordinate_near_frequency_budget (lam : ℝ) (z : ℂ) {b ζ : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.minimumScaleRadius (lam : ℂ)))
    (hζ : ζ ∈ ball z dom.scaledFrequencyRadius) :
    ‖cepsScaledRootCoordinate D θ ρW lam ζ b‖ ≤
      dom.frequencyRootBound * (1 + |lam| + Real.sqrt ‖z‖) := by
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let a := 1 + dom.μ₀ / 2
  let u := dom.morseMinUnitBound
  let δ := dom.scaledFrequencyRadius
  let C := dom.frequencyRootBound
  have hX : 1 ≤ X := by dsimp [X]; linarith [abs_nonneg lam, Real.sqrt_nonneg ‖z‖]
  have hXz : ‖z‖ ≤ X ^ 2 := by
    have hs := Real.sq_sqrt (norm_nonneg z)
    dsimp [X]
    nlinarith [abs_nonneg lam, Real.sqrt_nonneg ‖z‖]
  have hXl : lam ^ 2 ≤ X ^ 2 := by
    have hs := sq_abs lam
    dsimp [X]
    nlinarith [abs_nonneg lam, Real.sqrt_nonneg ‖z‖]
  have ha : 0 ≤ a := by dsimp [a]; linarith [dom.μ₀_pos]
  have hu : 0 ≤ u := by dsimp [u, CepsCanonDomain.morseMinUnitBound]; positivity
  have hδ : 0 ≤ δ := (scaledFrequencyRadius_pos dom hD).le
  have hζB : ‖ζ‖ ≤ (1 + δ) * X ^ 2 := by
    have hn := norm_add_le (ζ - z) z
    rw [sub_add_cancel] at hn
    have hdist : ‖ζ - z‖ < δ := by simpa only [dist_eq_norm] using mem_ball.mp hζ
    nlinarith [mul_nonneg hδ (by nlinarith : 0 ≤ X ^ 2 - 1)]
  have hrad := (cepsScaledMorseRadicand_budget dom hW hθ hD (lam : ℂ) ζ).2 b hb
  simp only [CepsCanonDomain.scaledRadicandBound, norm_real, Real.norm_eq_abs, sq_abs] at hrad
  have hrad' : ‖cepsScaledMorseRadicand D θ ρW lam ζ b‖ ≤ (a * (1 + δ) + u) * X ^ 2 :=
    hrad.trans ((add_le_add (mul_le_mul_of_nonneg_right hζB ha)
      (mul_le_mul_of_nonneg_right hXl hu)).trans_eq (by dsimp [a, u]; ring))
  have hcoef : a * (1 + δ) + u ≤ C ^ 2 := by
    dsimp [a, C, CepsCanonDomain.frequencyRootBound]
    nlinarith [dom.μ₀_pos]
  have hsq : ‖cepsScaledRootCoordinate D θ ρW lam ζ b‖ ^ 2 ≤ (C * X) ^ 2 := by
    rw [cepsScaledRootCoordinate, norm_complex_sqrt_sq]
    exact (hrad'.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg X))).trans_eq (by ring)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg (frequencyRootBound_pos dom hD).le
    (by linarith : 0 ≤ X)) (by norm_num : 2 ≠ 0)).mp hsq

end PGM
