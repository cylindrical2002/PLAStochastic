import PLAStochastic.Index.CEPS.Scaled.OuterHalfFrequency
import PLAStochastic.Index.CEPS.Scaled.PositivePairError
import PLAStochastic.Index.CEPS.Scaled.PositiveEntranceBridgeDecay

/-! # Complete positive-tail pair cancellation at complex scale -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

attribute [local irreducible] cepsScaledSurrogateEntrance cepsScaledSurrogateHalfEntrance

def CepsCanonDomain.outerPositivePairConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  9 * dom.surrogateEntrancePolynomialConstant N M ^ 2 * dom.outerTimeOperatorConstant N M +
    2 * dom.positiveEntranceCorrectionConstant N M *
      (3 * dom.surrogateEntrancePolynomialConstant N M + dom.surrogateHalfEntranceBound N M) *
        dom.outerHalfTimeOperatorConstant N M

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSurrogatePair_outer_positive_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) (hlam : 1 ≤ lam) {z : ℂ} (hz : 0 ≤ z.re)
    (houter : dom.centralFrequencyDriftRadius N M < |lam| ∨ dom.centralFrequencyRadius N M ≤ ‖z‖)
    {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.pairPolynomialScaleBase N M / (1 + |lam| + Real.sqrt ‖z‖)))
    (hbWidth : b ∈ ball (0 : ℂ) (1 / (2 * (1 + |lam|)))) :
    ‖cepsScaledSurrogatePair dom ρW N lam z b - cepsScaledSurrogateHalfPair dom ρW N lam z b‖ ≤
      dom.outerPositivePairConstant N M * (1 + |lam| + Real.sqrt ‖z‖) ^ 4 *
        Real.exp (-dom.positiveEntranceBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) := by
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let F := |lam| + Real.sqrt ‖z‖
  let R := ‖cepsScaledRootCoordinate D θ ρW lam z b‖
  let p := (cepsScaledSignedRoot D θ ρW lam z 1 b * (1 + b * lam)).re
  let m := (cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + b * lam)).re
  let t := ((b * z) * (1 + b * lam)).re
  let H := cepsScaledSurrogateEntrance dom ρW N lam z b
  let Hh := cepsScaledSurrogateHalfEntrance dom ρW N lam z b
  let U := cepsComplexScaledTimeOperator lam b (fun ζ => cepsScaledSurrogateBridge dom ρW N lam ζ b) z
  let Uh := cepsComplexScaledTimeOperator lam b (fun ζ => cepsScaledSurrogateHalfBridge dom ρW N lam ζ b) z
  let E := exp ((b * z) * (1 + b * lam))
  have hRadii := pairPolynomialScaleRadius_le dom hW hθ hD N M lam z
  have hbE := ball_subset_ball hRadii.2 hb
  have hbReg := ball_subset_ball (min_le_left _ _) hbE
  have hbS := ball_subset_ball (min_le_left _ _) hbReg
  have hH := cepsScaledSurrogateEntrance_positive_budget dom hW hθ hD hf hη hM N hN lam (by linarith) hz hb
  have hHalf := cepsScaledSurrogateHalfEntrance_positive_budget dom hW hθ hD hf hη hM N hN lam hlam hz hb
  have hCorr := cepsScaledSurrogateEntranceCorrection_positive_weighted_budget dom hW hθ hD hf hη hM N hN lam hlam hz hb
  have hUc := cepsScaledSurrogateBridgeCorrection_outer_timeOperator_budget dom hW hθ hD
    hf hη hM N hN lam hz houter hbE hbWidth
  have hprod := (cepsScaledSurrogateRootProduct_outer_frequency_profile dom hW hθ hD
    hf hη hM N hN lam hz houter (by norm_num : ‖(1 : ℂ)‖ ≤ 1)
      (by norm_num : ‖(-1 : ℂ)‖ ≤ 1) hbE).1
  have hFull : DifferentiableAt ℂ (fun ζ => cepsScaledSurrogateBridge dom ρW N lam ζ b) z := by
    have he : (fun ζ => cepsScaledSurrogateBridge dom ρW N lam ζ b) =
        -(fun ζ => cepsScaledSurrogateG dom ρW N lam ζ b (cepsScaledSignedRoot D θ ρW lam ζ 1 b) *
          cepsScaledSurrogateG dom ρW N lam ζ b (cepsScaledSignedRoot D θ ρW lam ζ (-1) b) *
            (cepsScaledSurrogateDenominator dom ρW N lam ζ b)⁻¹) := by
      funext ζ
      simp only [cepsScaledSurrogateBridge, Pi.neg_apply, div_eq_mul_inv, neg_mul]
    rw [he]
    exact hprod.neg
  have hHalfD := (cepsScaledSurrogateHalfBridge_outer_frequency_profile dom hW hθ hD
    hf hη hM N hN lam hz houter hbE).1
  have hOperator : cepsComplexScaledTimeOperator lam b
      (fun ζ => cepsScaledSurrogateBridgeCorrection dom ρW N lam ζ b) z = U - Uh := by
    unfold cepsComplexScaledTimeOperator
    dsimp only [U, Uh]
    unfold cepsComplexScaledTimeOperator
    rw [show (fun ζ => cepsScaledSurrogateBridgeCorrection dom ρW N lam ζ b) =
      (fun ζ => cepsScaledSurrogateBridge dom ρW N lam ζ b -
        cepsScaledSurrogateHalfBridge dom ρW N lam ζ b) by rfl, deriv_fun_sub hFull hHalfD]
    simp only [cepsScaledSurrogateBridgeCorrection]
    ring
  rw [hOperator] at hUc
  have hUh := cepsScaledSurrogateHalfBridge_outer_timeOperator_budget dom hW hθ hD
    hf hη hM N hN lam hz houter hbE hbWidth
  have hCombo : ((2 * cepsScaledSignedRoot D θ ρW lam z 1 b -
      cepsScaledSignedRoot D θ ρW lam z (-1) b) * (1 + b * lam)).re = 2 * p - m := by
    rw [sub_mul, sub_re, mul_assoc]
    congr 1
    exact re_ofReal_mul 2 _
  rw [hCombo] at hUc
  have hRc : F / Real.sqrt (8 * v + 8) ≤ R :=
    (scaledCoordinateLower_drift_frequency_le dom hW hθ hD lam z).trans
      (cepsScaledRootCoordinate_lower dom hW hθ hD N M lam hz hbS)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hc := (cepsScaledSurrogate_constants dom hW hθ hD N M).2.1.le
  have hbound : dom.positiveEntranceBridgeDecayRate * F ≤ R / (32 * Real.sqrt v) := by
    calc
      _ ≤ dom.entranceBridgeDecayRate * F := mul_le_mul_of_nonneg_right (min_le_left _ _) hF
      _ = (F / Real.sqrt (8 * v + 8)) / (32 * Real.sqrt v) := by
        unfold CepsCanonDomain.entranceBridgeDecayRate
        ring
      _ ≤ _ := div_le_div_of_nonneg_right hRc (by positivity)
  have hdir₁ : dom.positiveEntranceBridgeDecayRate * F ≤ 2 * p - m - t := by
    have hd := (cepsScaledPairRoot_positive_directions dom hW hθ hD N M lam (by linarith) hz hb).2
    rw [sub_mul, sub_re, hCombo] at hd
    exact hbound.trans hd
  have hdir₂ : dom.positiveEntranceBridgeDecayRate * F ≤ p - m := by
    calc
      _ ≤ (dom.scaledComplexSector / Real.sqrt (8 * v + 8)) * F :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hF
      _ = dom.scaledComplexSector * (F / Real.sqrt (8 * v + 8)) := by ring
      _ ≤ dom.scaledComplexSector * R := mul_le_mul_of_nonneg_left hRc hc
      _ ≤ _ := by
        simpa only [cepsScaledEffectiveGap, sub_mul, sub_re] using
          cepsScaledEffectiveGap_sector dom hW hθ hD N M lam hz hbS
  have hX : 1 ≤ X := by dsimp [X]; linarith [abs_nonneg lam, Real.sqrt_nonneg ‖z‖]
  have hX0 : 0 ≤ X := by linarith
  have hKh := (surrogateHalfEntranceBound_pos dom hW hθ hD N M).le
  have hKH := (surrogateEntrancePolynomialConstant_pos dom hW hθ hD N M).le
  have hKC := (positiveEntranceCorrectionConstant_pos dom hW hθ hD N M).le
  have hKU := (outerTimeOperatorConstant_pos dom hW hθ hD N M).le
  have hKUh := (outerHalfFrequency_constants dom hW hθ hD N M).2.le
  have hHalf' : ‖Hh‖ ≤ dom.surrogateHalfEntranceBound N M * X := hHalf.trans
    (le_mul_of_one_le_right hKh hX)
  have hCorr' : ‖H - Hh‖ ≤ dom.positiveEntranceCorrectionConstant N M * X *
      (Real.exp (m - p) + Real.exp (m - t)) := by
    simpa only [cepsScaledSurrogateEntranceCorrection, sub_mul, sub_re] using hCorr
  have hh := cepsNorm_weighted_square_subtraction_le
    (by positivity : 0 ≤ 3 * dom.surrogateEntrancePolynomialConstant N M * X)
    (mul_nonneg hKh hX0) (mul_nonneg hKC hX0) (mul_nonneg hKU (sq_nonneg X)) (mul_nonneg hKUh (sq_nonneg X))
    hH hHalf' (show ‖E‖ ≤ Real.exp t by change ‖exp ((b * z) * (1 + b * lam))‖ ≤ _; rw [norm_exp])
      hCorr' hUc hUh hdir₁ hdir₂
  have he : cepsScaledSurrogatePair dom ρW N lam z b - cepsScaledSurrogateHalfPair dom ρW N lam z b =
      E * (H ^ 2 * U - Hh ^ 2 * Uh) := by
    dsimp only [cepsScaledSurrogatePair, cepsScaledSurrogateHalfPair, cepsComplexScaledTimeOperator, E, H, U, Hh, Uh]
    ring
  rw [he]
  apply hh.trans_eq
  unfold CepsCanonDomain.outerPositivePairConstant
  dsimp only [F, X]
  ring

end PGM
