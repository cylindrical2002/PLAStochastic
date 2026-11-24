import PLAStochastic.Index.CEPS.Scaled.SurrogateBridgeCorrection
import PLAStochastic.Index.CEPS.Scaled.SurrogateBridgeBudget
import PLAStochastic.Index.CEPS.Scaled.CoordinateBudgets

/-! # Exponential budgets after positive-drift half-line bridge subtraction -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.positiveBridgePolynomialConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  dom.scaledGapBound * (4 * dom.scaledCoordinateRatioBound / dom.scaledComplexSector) *
      (v * Real.exp (2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8))) * dom.surrogatePiNormBound N M +
    8 * v ^ 2 / cepsVarLo D * Real.exp (6 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8))

def CepsCanonDomain.positiveBridgeDecayRate {D θ v : ℝ} (_dom : CepsCanonDomain D θ v) : ℝ :=
  1 / (Real.sqrt (8 * v + 8) * (16 * Real.sqrt v))

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem positiveBridgePolynomial_constants (N : ℕ) (M : ℝ) :
    0 < dom.positiveBridgePolynomialConstant N M ∧ 0 < dom.positiveBridgeDecayRate := by
  have hv := CepsCanonDomain.v_pos hW hθ hD
  have hvl := cepsVarLo_pos hD
  have hK := (cepsScaledSurrogate_constants dom hW hθ hD N M).1
  have hc := (cepsScaledSurrogate_constants dom hW hθ hD N M).2.1
  have hA : 0 ≤ dom.scaledCoordinateRatioBound := Real.sqrt_nonneg _
  unfold CepsCanonDomain.positiveBridgePolynomialConstant CepsCanonDomain.positiveBridgeDecayRate
    CepsCanonDomain.surrogatePiNormBound
  constructor <;> positivity

include hW hθ hD in
theorem cepsScaledSurrogateBridgeCorrection_positive_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) (hlam : 0 ≤ lam) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.positiveCorrectionScaleRadius N M lam z)) :
    ‖cepsScaledSurrogateBridgeCorrection dom ρW N lam z b‖ ≤
      dom.positiveBridgePolynomialConstant N M * (1 + |lam| + Real.sqrt ‖z‖) *
        Real.exp (-dom.positiveBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) := by
  have hbD := ball_subset_ball (min_le_left _ _) hb
  have hbReg := ball_subset_ball (min_le_left _ _) hbD
  have hbS := ball_subset_ball (min_le_left _ _) hbReg
  have hbC : b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z) :=
    ball_subset_ball (half_le_self (canonScaleRadius_pos dom hW hθ hD lam z).le)
      (complexDirectionScaleCurve_bounds dom N M lam hbD).1
  have hv := CepsCanonDomain.v_pos hW hθ hD
  have hvl := cepsVarLo_pos hD
  have hK := (cepsScaledSurrogate_constants dom hW hθ hD N M).1.le
  have hc := (cepsScaledSurrogate_constants dom hW hθ hD N M).2.1
  have hA : 0 ≤ dom.scaledCoordinateRatioBound := Real.sqrt_nonneg _
  let B := dom.canonDriftTaylorBound N M (dom.μ₀ / 8)
  let F := v * Real.exp (2 * B)
  let P := dom.surrogatePiNormBound N M
  let C := 8 * v ^ 2 / cepsVarLo D * Real.exp (6 * B)
  let X := 1 + |lam| + Real.sqrt ‖z‖
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hP : 0 ≤ P := by dsimp [P, CepsCanonDomain.surrogatePiNormBound]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hX : 1 ≤ X := by dsimp [X]; linarith [abs_nonneg lam, Real.sqrt_nonneg ‖z‖]
  by_cases hne : 0 < lam ^ 2 + ‖z‖
  · have hgap0 := cepsScaledRootGap_ne_zero dom hW hθ hD N M lam hz hne hbS
    have hS0 := cepsScaledSurrogateDenominator_ne_zero dom hW hθ hD hf hη hM N hN lam hz hbReg
    have hid := cepsScaledSurrogateDelta_mul_rootG dom hW hθ hD hf hη hM N hN lam hz hbC
    have hΔ0 : cepsScaledSurrogateDelta dom ρW N lam z b ≠ 0 := by
      intro he
      rw [he, zero_mul] at hid
      exact mul_ne_zero (neg_ne_zero.mpr hgap0) hS0 hid.symm
    have he := (eq_div_iff hΔ0).mpr
      (cepsScaledSurrogateBridgeCorrection_mul_delta dom hW hθ hD hf hη hM N hN lam hz hbReg)
    have he' : cepsScaledSurrogateBridgeCorrection dom ρW N lam z b =
        (cepsScaledSignedRoot D θ ρW lam z 1 b - cepsScaledSignedRoot D θ ρW lam z (-1) b) *
          (cepsScaledSurrogateG dom ρW N lam z b (cepsScaledSignedRoot D θ ρW lam z 1 b) *
            exp (-cepsScaledEffectiveGap D θ ρW lam z b)) *
              cepsScaledSurrogatePi dom ρW N lam z b /
                cepsScaledSurrogateDelta dom ρW N lam z b := by rw [he]; ring
    have hbRad := ball_subset_ball (min_le_left _ _) (ball_subset_ball (min_le_left _ _) hbC)
    have hgap : ‖cepsScaledSignedRoot D θ ρW lam z 1 b - cepsScaledSignedRoot D θ ρW lam z (-1) b‖ ≤
        dom.scaledGapBound * dom.scaledRootCoordinateBound lam z :=
      (cepsScaledRootGap_norm_le dom hW hθ hD lam hz hbC).trans
        (mul_le_mul_of_nonneg_left ((cepsScaledRootCoordinate_budget dom hW hθ hD lam hz).2 b hbRad) hK)
    obtain ⟨hμ, hq, hζ⟩ := canonScaleCurve_bounds dom hW hθ hD lam hz (sign := 1) (by norm_num) hbC
    have hWgt := (cepsCanonSurrogateWeight_bounds dom hW hθ hD hf hη hM N hN hμ.le hq.le hζ.le).2
    have hExp := cepsScaledPositiveCorrectionRoot_exp_decay dom hW hθ hD N M lam hlam hz hb
    have hGpE : ‖cepsScaledSurrogateG dom ρW N lam z b (cepsScaledSignedRoot D θ ρW lam z 1 b) *
        exp (-cepsScaledEffectiveGap D θ ρW lam z b)‖ ≤
          Real.exp (-dom.scaledCoordinateLower lam z / (16 * Real.sqrt v)) * F := by
      rw [cepsScaledSurrogateG_mul_decay, norm_mul]
      exact mul_le_mul hExp hWgt (norm_nonneg _) (Real.exp_pos _).le
    have hPi := (cepsScaledSurrogatePi_budget dom hW hθ hD hf hη hM N hN lam hz).2 b hbC
    have hInv := (cepsScaledSurrogateDelta_inverse_budget dom hW hθ hD hf hη hM N hN lam hz hne).2 b hbS
    have hprod := mul_le_mul
      (mul_le_mul (mul_le_mul hgap hGpE (norm_nonneg _) ((norm_nonneg _).trans hgap)) hPi
        (norm_nonneg _) (mul_nonneg ((norm_nonneg _).trans hgap) ((norm_nonneg _).trans hGpE)))
      hInv (norm_nonneg _) (mul_nonneg
        (mul_nonneg ((norm_nonneg _).trans hgap) ((norm_nonneg _).trans hGpE)) hP)
    have hSI := scaledCoordinateBound_mul_deltaInverse_le dom hW hθ hD lam hne
    have hpre : (dom.scaledGapBound * dom.scaledRootCoordinateBound lam z) * F * P *
        dom.surrogateDeltaInverseBound lam z ≤ dom.positiveBridgePolynomialConstant N M * X := by
      have hh := mul_le_mul_of_nonneg_left hSI (mul_nonneg (mul_nonneg hK hF) hP)
      have hhC := mul_nonneg hC (by dsimp [X]; positivity : 0 ≤ X)
      change _ ≤ (dom.scaledGapBound * (4 * dom.scaledCoordinateRatioBound / dom.scaledComplexSector) * F * P + C) * X
      nlinarith
    have hlo := div_le_div_of_nonneg_right (scaledCoordinateLower_drift_frequency_le dom hW hθ hD lam z)
      (by positivity : 0 ≤ 16 * Real.sqrt v)
    have hrate : -dom.scaledCoordinateLower lam z / (16 * Real.sqrt v) ≤
        -dom.positiveBridgeDecayRate * (|lam| + Real.sqrt ‖z‖) := by
      have hr : ((|lam| + Real.sqrt ‖z‖) / Real.sqrt (8 * v + 8)) / (16 * Real.sqrt v) =
          dom.positiveBridgeDecayRate * (|lam| + Real.sqrt ‖z‖) := by
        unfold CepsCanonDomain.positiveBridgeDecayRate
        ring
      rw [hr] at hlo
      simpa only [neg_div, neg_mul] using neg_le_neg hlo
    rw [he', div_eq_mul_inv, norm_mul, norm_mul, norm_mul]
    apply hprod.trans
    have hh := mul_le_mul hpre (Real.exp_le_exp.mpr hrate) (Real.exp_pos _).le
      (mul_nonneg (positiveBridgePolynomial_constants dom hW hθ hD N M).1.le (by dsimp [X]; positivity))
    convert hh using 1
    ring
  · have hl : lam = 0 := by nlinarith [sq_nonneg lam, norm_nonneg z]
    have hz0 : z = 0 := norm_eq_zero.mp (by nlinarith [sq_nonneg lam, norm_nonneg z])
    subst lam
    subst z
    rw [cepsScaledSurrogateBridgeCorrection_joint_origin dom hW hθ hD]
    have hbnd := cepsScaledSurrogateBridge_origin_bound dom hW hθ hD hf hη hM N hN hbReg
    simp only [abs_zero, norm_zero, Real.sqrt_zero, add_zero, mul_zero, Real.exp_zero, mul_one]
    apply hbnd.trans
    unfold CepsCanonDomain.positiveBridgePolynomialConstant
    have ht : 0 ≤ dom.scaledGapBound * (4 * dom.scaledCoordinateRatioBound / dom.scaledComplexSector) * F * P :=
      mul_nonneg (mul_nonneg (mul_nonneg hK (by positivity)) hF) hP
    change C ≤ dom.scaledGapBound * (4 * dom.scaledCoordinateRatioBound / dom.scaledComplexSector) * F * P + C
    linarith

include hW hθ hD in
theorem cepsScaledSurrogateBridgeCorrection_positive_taylor_le {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) (hlam : 0 ≤ lam) {z : ℂ} (hz : 0 ≤ z.re) (n : ℕ) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.positiveCorrectionScaleRadius N M lam z / 2)) :
    ‖cepsScaledSurrogateBridgeCorrection dom ρW N lam z b -
      complexTaylorSum (cepsScaledSurrogateBridgeCorrection dom ρW N lam z) n 0 b‖ ≤
      ((n.factorial : ℝ) *
        (dom.positiveBridgePolynomialConstant N M * (1 + |lam| + Real.sqrt ‖z‖) *
          Real.exp (-dom.positiveBridgeDecayRate * (|lam| + Real.sqrt ‖z‖))) /
        (dom.positiveCorrectionScaleRadius N M lam z / 4) ^ n) * ‖b‖ ^ n := by
  have hsub : ball (0 : ℂ) (dom.positiveCorrectionScaleRadius N M lam z) ⊆
      ball 0 (dom.surrogateRegularScaleRadius N M lam z) :=
    ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _))
  have hd := (cepsScaledSurrogateBridgeCorrection_differentiableOn dom hW hθ hD hf hη hM N hN lam hz).mono hsub
  have hm := fun b hb => cepsScaledSurrogateBridgeCorrection_positive_budget dom hW hθ hD hf hη hM N hN lam hlam hz (b := b) hb
  simpa only [sub_zero] using norm_sub_complexTaylorSum_le_of_ball n
    (positiveCorrectionScaleRadius_pos dom hW hθ hD N M lam z) hd hm hb

end PGM
