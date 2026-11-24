import PLAStochastic.Index.CEPS.Scaled.PositiveEntranceCorrection
import PLAStochastic.Index.CEPS.Scaled.SurrogateBridgeSquareBudget
import PLAStochastic.Index.CEPS.Scaled.EntranceBridgeDecay
import PLAStochastic.Index.CEPS.Scaled.WeightedSquareSubtraction

/-! # Positive-drift half-line subtraction of the entrance-square bridge -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def cepsScaledSurrogateEntranceBridgeCorrection {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (N : ℕ) (lam : ℝ) (z b : ℂ) : ℂ :=
  cepsScaledSurrogateEntranceBridge dom ρW N lam z b -
    exp ((b * z) * (1 + b * lam)) * (cepsScaledSurrogateHalfEntrance dom ρW N lam z b) ^ 2 *
      cepsScaledSurrogateHalfBridge dom ρW N lam z b

def CepsCanonDomain.positiveEntranceBridgeDecayRate {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) : ℝ :=
  min dom.entranceBridgeDecayRate (dom.scaledComplexSector / Real.sqrt (8 * v + 8))

def CepsCanonDomain.positiveEntranceBridgeConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  9 * (dom.surrogateEntrancePolynomialConstant N M) ^ 2 * dom.surrogateBridgeWeightedConstant N M +
    2 * dom.positiveEntranceCorrectionConstant N M *
      (3 * dom.surrogateEntrancePolynomialConstant N M + dom.surrogateHalfEntranceBound N M) *
        dom.surrogateHalfBridgeWeightedConstant N M

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem positiveEntranceBridge_constants (N : ℕ) (M : ℝ) :
    0 < dom.positiveEntranceBridgeConstant N M ∧ 0 < dom.positiveEntranceBridgeDecayRate := by
  have := surrogateEntrancePolynomialConstant_pos dom hW hθ hD N M
  have := surrogateSlopePolynomialConstant_pos dom hW hθ hD N M
  have := positiveEntranceCorrectionConstant_pos dom hW hθ hD N M
  have := surrogateHalfEntranceBound_pos dom hW hθ hD N M
  have := CepsCanonDomain.v_pos hW hθ hD
  have := (cepsScaledSurrogate_constants dom hW hθ hD N M).1
  have := (cepsScaledSurrogate_constants dom hW hθ hD N M).2.1
  have := (entranceBridgePolynomial_constants dom hW hθ hD N M).2
  have hA : 0 ≤ dom.scaledCoordinateRatioBound := Real.sqrt_nonneg _
  unfold CepsCanonDomain.positiveEntranceBridgeConstant CepsCanonDomain.positiveEntranceBridgeDecayRate
    CepsCanonDomain.surrogateBridgeWeightedConstant CepsCanonDomain.surrogateHalfBridgeWeightedConstant
  constructor <;> positivity

include hW hθ hD in
theorem cepsScaledSurrogateEntranceBridgeCorrection_positive_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) (hlam : 1 ≤ lam) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.pairPolynomialScaleBase N M / (1 + |lam| + Real.sqrt ‖z‖))) :
    ‖cepsScaledSurrogateEntranceBridgeCorrection dom ρW N lam z b‖ ≤
      dom.positiveEntranceBridgeConstant N M * (1 + |lam| + Real.sqrt ‖z‖) ^ 3 *
        Real.exp (-dom.positiveEntranceBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) := by
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let F := |lam| + Real.sqrt ‖z‖
  let R := ‖cepsScaledRootCoordinate D θ ρW lam z b‖
  let p := (cepsScaledSignedRoot D θ ρW lam z 1 b * (1 + b * lam)).re
  let m := (cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + b * lam)).re
  let t := ((b * z) * (1 + b * lam)).re
  let H := cepsScaledSurrogateEntrance dom ρW N lam z b
  let Hh := cepsScaledSurrogateHalfEntrance dom ρW N lam z b
  let U := cepsScaledSurrogateBridge dom ρW N lam z b
  let Uh := cepsScaledSurrogateHalfBridge dom ρW N lam z b
  let E := exp ((b * z) * (1 + b * lam))
  have hRadii := pairPolynomialScaleRadius_le dom hW hθ hD N M lam z
  have hbE := ball_subset_ball hRadii.2 hb
  have hbReg := ball_subset_ball (min_le_left _ _) hbE
  have hbS := ball_subset_ball (min_le_left _ _) hbReg
  have hbC : b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z) := ball_subset_ball
    ((min_le_right _ _).trans (div_le_self (canonScaleRadius_pos dom hW hθ hD lam z).le (by norm_num))) hbE
  have hH := cepsScaledSurrogateEntrance_positive_budget dom hW hθ hD hf hη hM N hN lam (by linarith) hz hb
  have hHalf := cepsScaledSurrogateHalfEntrance_positive_budget dom hW hθ hD hf hη hM N hN lam hlam hz hb
  have hCorr := cepsScaledSurrogateEntranceCorrection_positive_weighted_budget dom hW hθ hD hf hη hM N hN lam hlam hz hb
  have hUc := cepsScaledSurrogateBridgeCorrection_weighted_budget dom hW hθ hD hf hη hM N hN lam hz hbReg
  have hUh := cepsScaledSurrogateHalfBridge_weighted_budget dom hW hθ hD hf hη hM N hN lam hz hbC
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
  have hKU : 0 ≤ dom.surrogateBridgeWeightedConstant N M := by
    unfold CepsCanonDomain.surrogateBridgeWeightedConstant
    exact mul_nonneg (sq_nonneg _) (surrogateSlopePolynomialConstant_pos dom hW hθ hD N M).le
  have hKUh : 0 ≤ dom.surrogateHalfBridgeWeightedConstant N M := by
    unfold CepsCanonDomain.surrogateHalfBridgeWeightedConstant
    have := (cepsScaledSurrogate_constants dom hW hθ hD N M).1.le
    have hA : 0 ≤ dom.scaledCoordinateRatioBound := Real.sqrt_nonneg _
    have := (CepsCanonDomain.v_pos hW hθ hD).le
    positivity
  have hHalf' : ‖Hh‖ ≤ dom.surrogateHalfEntranceBound N M * X := hHalf.trans
    (le_mul_of_one_le_right hKh hX)
  have hCorr' : ‖H - Hh‖ ≤ dom.positiveEntranceCorrectionConstant N M * X *
      (Real.exp (m - p) + Real.exp (m - t)) := by
    simpa only [cepsScaledSurrogateEntranceCorrection, sub_mul, sub_re] using hCorr
  have hh := cepsNorm_weighted_square_subtraction_le
    (by positivity : 0 ≤ 3 * dom.surrogateEntrancePolynomialConstant N M * X)
    (mul_nonneg hKh hX0) (mul_nonneg hKC hX0) (mul_nonneg hKU hX0) (mul_nonneg hKUh hX0)
    hH hHalf' (show ‖E‖ ≤ Real.exp t by change ‖exp ((b * z) * (1 + b * lam))‖ ≤ _; rw [norm_exp])
      hCorr' hUc hUh hdir₁ hdir₂
  have he : cepsScaledSurrogateEntranceBridgeCorrection dom ρW N lam z b =
      E * (H ^ 2 * U - Hh ^ 2 * Uh) := by
    dsimp only [cepsScaledSurrogateEntranceBridgeCorrection, cepsScaledSurrogateEntranceBridge, E, H, U, Hh, Uh]
    ring
  rw [he]
  apply hh.trans_eq
  unfold CepsCanonDomain.positiveEntranceBridgeConstant
  dsimp only [F, X]
  ring

end PGM
