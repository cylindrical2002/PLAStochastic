import PLAStochastic.Index.CEPS.Scaled.OuterTimeOperator
import PLAStochastic.Index.CEPS.Scaled.TruePairScaling
import PLAStochastic.Index.CEPS.Scaled.EntranceBridgeDecay
import PLAStochastic.Index.CEPS.Scaled.WeightedSquareSubtraction

/-! # The complete outer-frequency pair on the negative drift half-line -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

attribute [local irreducible] cepsScaledSurrogateBridge cepsScaledSurrogateEntrance

def CepsCanonDomain.outerNegativePairConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  10 * dom.surrogateEntrancePolynomialConstant N M ^ 2 * dom.outerTimeOperatorConstant N M

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSurrogatePair_outer_negative_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) (hlam : lam ≤ 0) {z : ℂ} (hz : 0 ≤ z.re)
    (houter : dom.centralFrequencyDriftRadius N M < |lam| ∨ dom.centralFrequencyRadius N M ≤ ‖z‖)
    {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.pairPolynomialScaleBase N M / (1 + |lam| + Real.sqrt ‖z‖)))
    (hbWidth : b ∈ ball (0 : ℂ) (1 / (2 * (1 + |lam|)))) :
    ‖cepsScaledSurrogatePair dom ρW N lam z b‖ ≤
      dom.outerNegativePairConstant N M * (1 + |lam| + Real.sqrt ‖z‖) ^ 4 *
        Real.exp (-dom.entranceBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) := by
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let p := (cepsScaledSignedRoot D θ ρW lam z 1 b * (1 + b * lam)).re
  let m := (cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + b * lam)).re
  let t := ((b * z) * (1 + b * lam)).re
  have hR := pairPolynomialScaleRadius_le dom hW hθ hD N M lam z
  have hbE := ball_subset_ball hR.2 hb
  have hH := cepsScaledSurrogateEntrance_polynomial_budget dom hW hθ hD hf hη hM N hN lam hz hbE
  have hU := cepsScaledSurrogateBridge_outer_timeOperator_budget dom hW hθ hD
    hf hη hM N hN lam hz houter hbE hbWidth
  have hdirs := cepsScaledPairRoot_negative_directions dom hW hθ hD N M lam hlam hz hb
  have ht : dom.scaledCoordinateLower lam z ≤ ‖cepsScaledRootCoordinate D θ ρW lam z b‖ :=
    cepsScaledRootCoordinate_lower dom hW hθ hD N M lam hz (ball_subset_ball (min_le_left _ _) (ball_subset_ball (min_le_left _ _) hbE))
  have hτ := scaledCoordinateLower_drift_frequency_le dom hW hθ hD lam z
  have hv := Real.sqrt_pos.mpr (CepsCanonDomain.v_pos hW hθ hD)
  have hsmall : dom.entranceBridgeDecayRate * (|lam| + Real.sqrt ‖z‖) ≤
      ‖cepsScaledRootCoordinate D θ ρW lam z b‖ / (32 * Real.sqrt v) := by
    calc
      _ = ((|lam| + Real.sqrt ‖z‖) / Real.sqrt (8 * v + 8)) / (32 * Real.sqrt v) := by
        unfold CepsCanonDomain.entranceBridgeDecayRate
        ring
      _ ≤ _ := div_le_div_of_nonneg_right (hτ.trans ht) (by positivity)
  have hd₁ : dom.entranceBridgeDecayRate * (|lam| + Real.sqrt ‖z‖) ≤ p - t := by
    exact hsmall.trans (by simpa only [sub_mul, sub_re] using hdirs.1)
  have hd₂ : dom.entranceBridgeDecayRate * (|lam| + Real.sqrt ‖z‖) ≤ p - 2 * m + t := by
    have he : (2 * cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + b * lam)).re = 2 * m := by
      rw [mul_assoc]
      exact re_ofReal_mul 2 _
    have hd := hdirs.2
    rw [add_mul, sub_mul, add_re, sub_re, he] at hd
    exact hsmall.trans hd
  have hH' : ‖cepsScaledSurrogateEntrance dom ρW N lam z b‖ ≤
      dom.surrogateEntrancePolynomialConstant N M * X * (2 + Real.exp (m - t)) := by
    simpa only [sub_mul, sub_re] using hH
  have hAU : 0 ≤ dom.outerTimeOperatorConstant N M * X ^ 2 :=
    mul_nonneg (outerTimeOperatorConstant_pos dom hW hθ hD N M).le (sq_nonneg X)
  have hh := cepsNorm_weighted_square_bridge_le hAU
    (show ‖exp ((b * z) * (1 + b * lam))‖ ≤ Real.exp t by rw [norm_exp]) hH' hU hd₁ hd₂
  change ‖exp ((b * z) * (1 + b * lam)) *
    (cepsScaledSurrogateEntrance dom ρW N lam z b) ^ 2 *
      cepsComplexScaledTimeOperator lam b (fun ζ => cepsScaledSurrogateBridge dom ρW N lam ζ b) z‖ ≤ _
  apply hh.trans_eq
  unfold CepsCanonDomain.outerNegativePairConstant
  dsimp only [X]
  ring

end PGM
