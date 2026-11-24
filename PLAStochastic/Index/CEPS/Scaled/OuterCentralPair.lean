import PLAStochastic.Index.CEPS.Scaled.OuterTimeOperator
import PLAStochastic.Index.CEPS.Scaled.TruePairScaling
import PLAStochastic.Index.CEPS.Scaled.RootDriftDirection
import PLAStochastic.Index.CEPS.Scaled.EntranceBridgeDecay
import PLAStochastic.Index.CEPS.Scaled.WeightedSquareSubtraction

/-! # The complete outer-frequency pair on the bounded drift interval -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.outerCentralPairConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  10 * dom.surrogateEntrancePolynomialConstant N M ^ 2 *
    dom.outerTimeOperatorConstant N M * Real.exp (2 / cepsVarLo D)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSurrogatePair_outer_central_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) (hlam : |lam| ≤ 1) {z : ℂ} (hz : 0 ≤ z.re)
    (houter : dom.centralFrequencyDriftRadius N M < |lam| ∨ dom.centralFrequencyRadius N M ≤ ‖z‖)
    {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.pairPolynomialScaleBase N M / (1 + |lam| + Real.sqrt ‖z‖)))
    (hbWidth : b ∈ ball (0 : ℂ) (1 / (2 * (1 + |lam|)))) :
    ‖cepsScaledSurrogatePair dom ρW N lam z b‖ ≤
      dom.outerCentralPairConstant N M * (1 + |lam| + Real.sqrt ‖z‖) ^ 4 *
        Real.exp (-dom.entranceBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) := by
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let F := |lam| + Real.sqrt ‖z‖
  let R := ‖cepsScaledRootCoordinate D θ ρW lam z b‖
  let p := (cepsScaledSignedRoot D θ ρW lam z 1 b * (1 + b * lam)).re
  let m := (cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + b * lam)).re
  let t := ((b * z) * (1 + b * lam)).re
  let C := 2 / cepsVarLo D
  have hRadii := pairPolynomialScaleRadius_le dom hW hθ hD N M lam z
  have hbP := ball_subset_ball hRadii.1 hb
  have hbE := ball_subset_ball hRadii.2 hb
  have hbReg := ball_subset_ball (min_le_left _ _) hbE
  have hbDir := ball_subset_ball (min_le_left _ _) hbP
  have hpre := cepsScaledRootPlus_width_drift_loss dom hW hθ hD N M lam hz hbDir
  have hcubic := (cepsScaledCombinedRoots_width_lower dom hW hθ hD N M lam hz hbP).2
  have hmark := cepsScaledMarker_width_small dom hW hθ hD N M lam hz hb
  have hmarkLo := (neg_le_abs ((b * z) * (1 + b * lam)).re).trans ((abs_re_le_norm _).trans hmark)
  have hmarkHi := (re_le_norm ((b * z) * (1 + b * lam))).trans hmark
  have hcoef : 0 ≤ R * (Real.sqrt v)⁻¹ := mul_nonneg (norm_nonneg _) (inv_nonneg.mpr (Real.sqrt_nonneg _))
  have hC : 0 ≤ C := div_nonneg (by norm_num) (cepsVarLo_pos hD).le
  have hloss : C * |lam| ≤ C := mul_le_of_le_one_right hC hlam
  have hsmall : dom.entranceBridgeDecayRate * F ≤ R / (32 * Real.sqrt v) := by
    have hRc := (scaledCoordinateLower_drift_frequency_le dom hW hθ hD lam z).trans
      (cepsScaledRootCoordinate_lower dom hW hθ hD N M lam hz
        (ball_subset_ball (min_le_left _ _) hbReg))
    calc
      _ = (F / Real.sqrt (8 * v + 8)) / (32 * Real.sqrt v) := by
        unfold CepsCanonDomain.entranceBridgeDecayRate
        ring
      _ ≤ _ := div_le_div_of_nonneg_right hRc (by positivity)
  have hdir₁ : dom.entranceBridgeDecayRate * F - C ≤ p - t := by
    change R / (8 * Real.sqrt v) - C * |lam| ≤ p at hpre
    change t ≤ R / (128 * Real.sqrt v) at hmarkHi
    ring_nf at hpre hmarkHi hsmall ⊢
    linarith
  have hRe : ((cepsScaledSignedRoot D θ ρW lam z 1 b -
      2 * cepsScaledSignedRoot D θ ρW lam z (-1) b) * (1 + b * lam)).re = p - 2 * m := by
    rw [sub_mul, sub_re, mul_assoc]
    congr 1
    exact re_ofReal_mul 2 _
  have hdir₂ : dom.entranceBridgeDecayRate * F - C ≤ p - 2 * m + t := by
    rw [hRe] at hcubic
    change R / (16 * Real.sqrt v) ≤ p - 2 * m at hcubic
    change -t ≤ R / (128 * Real.sqrt v) at hmarkLo
    ring_nf at hcubic hmarkLo hsmall ⊢
    linarith
  have hH : ‖cepsScaledSurrogateEntrance dom ρW N lam z b‖ ≤
      dom.surrogateEntrancePolynomialConstant N M * X * (2 + Real.exp (m - t)) := by
    simpa only [sub_mul, sub_re] using
      cepsScaledSurrogateEntrance_polynomial_budget dom hW hθ hD hf hη hM N hN lam hz hbE
  have hU := cepsScaledSurrogateBridge_outer_timeOperator_budget dom hW hθ hD
    hf hη hM N hN lam hz houter hbE hbWidth
  have hAU : 0 ≤ dom.outerTimeOperatorConstant N M * X ^ 2 :=
    mul_nonneg (outerTimeOperatorConstant_pos dom hW hθ hD N M).le (sq_nonneg X)
  have hh := cepsNorm_weighted_square_bridge_le hAU
    (show ‖exp ((b * z) * (1 + b * lam))‖ ≤ Real.exp t by rw [norm_exp]) hH hU hdir₁ hdir₂
  change ‖exp ((b * z) * (1 + b * lam)) *
    (cepsScaledSurrogateEntrance dom ρW N lam z b) ^ 2 *
      cepsComplexScaledTimeOperator lam b (fun ζ => cepsScaledSurrogateBridge dom ρW N lam ζ b) z‖ ≤ _
  apply hh.trans_eq
  unfold CepsCanonDomain.outerCentralPairConstant
  rw [show -(dom.entranceBridgeDecayRate * F - C) = C + -dom.entranceBridgeDecayRate * F by ring, Real.exp_add]
  dsimp only [C, F, X]
  ring

end PGM
