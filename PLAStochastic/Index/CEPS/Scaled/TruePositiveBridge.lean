import PLAStochastic.Index.CEPS.Scaled.TrueNegativePair
import PLAStochastic.Index.CEPS.Scaled.PositiveBridgeBudget

/-! # Actual positive-drift bridge half-line subtraction -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def cepsScaledTrueHalfBridge {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (lam : ℝ) (z : ℂ) (b : ℝ) : ℂ :=
  (cepsScaledSignedRoot D θ ρW lam z 1 b - cepsScaledSignedRoot D θ ρW lam z (-1) b) *
    cepsScaledTrueG dom ρW lam z b (cepsScaledSignedRoot D θ ρW lam z 1 b)

def cepsScaledTrueBridgeCorrection {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (lam : ℝ) (z : ℂ) (b : ℝ) : ℂ :=
  cepsScaledTrueBridge dom ρW lam z b - cepsScaledTrueHalfBridge dom ρW lam z b

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrueBridgeCorrection_eq_square {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m) (lam : ℝ)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDenominatorScaleRadius M lam z)) :
    cepsScaledTrueBridgeCorrection dom ρW lam z b =
      -(cepsScaledTrueG dom ρW lam z b (cepsScaledSignedRoot D θ ρW lam z 1 b)) ^ 2 /
        cepsScaledTrueDenominator dom ρW lam z b := by
  let G := cepsScaledTrueG dom ρW lam z b
  let p := cepsScaledSignedRoot D θ ρW lam z 1 (b : ℂ)
  let a := cepsScaledSignedRoot D θ ρW lam z (-1) (b : ℂ)
  have hS := cepsScaledTrueDenominator_ne_zero dom hW hθ hD hf hη hM hm lam hz hb
  have hid := sub_smul_dslope G a p
  rw [smul_eq_mul] at hid
  change (p - a) * cepsScaledTrueDenominator dom ρW lam z b = G p - G a at hid
  unfold cepsScaledTrueBridgeCorrection cepsScaledTrueBridge cepsScaledTrueHalfBridge
  change -G p * G a / cepsScaledTrueDenominator dom ρW lam z b - (p - a) * G p =
    -(G p) ^ 2 / cepsScaledTrueDenominator dom ρW lam z b
  field_simp
  linear_combination -G p * hid

include hW hθ hD in
theorem cepsScaledTrueBridgeCorrection_weighted_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m) (lam : ℝ)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDenominatorScaleRadius M lam z)) :
    ‖cepsScaledTrueBridgeCorrection dom ρW lam z b‖ ≤
      dom.trueBridgeWeightedConstant M * (1 + |lam| + Real.sqrt ‖z‖) *
        Real.exp (-((2 * cepsScaledSignedRoot D θ ρW lam z 1 b -
          cepsScaledSignedRoot D θ ρW lam z (-1) b) * (1 + (b : ℂ) * lam)).re) := by
  have hT := trueSpatialBound_nonneg dom hW hθ hD ((cepsSobolev_nonneg m η fW).trans hM) 0
  have hp := cepsScaledTrueG_root_weighted_budget dom hW hθ hD hf hη hM hm lam hz hb
    (by norm_num : ‖(1 : ℂ)‖ ≤ 1)
  have hI := cepsScaledTrueDenominator_inverse_weighted_budget dom hW hθ hD hf hη hM hm lam hz hb
  have hn := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hp 2) hI (norm_nonneg _) (by positivity)
  rw [cepsScaledTrueBridgeCorrection_eq_square dom hW hθ hD hf hη hM hm lam hz hb,
    div_eq_mul_inv, norm_mul, norm_neg, norm_pow]
  apply hn.trans_eq
  unfold CepsCanonDomain.trueBridgeWeightedConstant
  let p := (cepsScaledSignedRoot D θ ρW lam z 1 b * (1 + (b : ℂ) * lam)).re
  let a := (cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + (b : ℂ) * lam)).re
  have he : Real.exp (-p) ^ 2 * Real.exp a = Real.exp (-(2 * p - a)) := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hr : ((2 * cepsScaledSignedRoot D θ ρW lam z 1 b -
      cepsScaledSignedRoot D θ ρW lam z (-1) b) * (1 + (b : ℂ) * lam)).re = 2 * p - a := by
    dsimp [p, a]
    rw [sub_mul, mul_assoc, sub_re]
    simp
  rw [hr, mul_pow]
  calc
    _ = (dom.trueSpatialBound M 0 ^ 2 * (2 * dom.surrogateSlopePolynomialConstant 0 M) *
        (1 + |lam| + Real.sqrt ‖z‖)) * (Real.exp (-p) ^ 2 * Real.exp a) := by ring
    _ = _ := by rw [he]

include hW hθ hD in
theorem cepsScaledTrueBridgeCorrection_positive_polynomial_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m) (lam : ℝ) (hlam : 0 ≤ lam)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDenominatorScaleRadius M lam z)) :
    ‖cepsScaledTrueBridgeCorrection dom ρW lam z b‖ ≤
      dom.trueBridgeWeightedConstant M * (1 + |lam| + Real.sqrt ‖z‖) *
        Real.exp (-dom.positiveBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) := by
  have hbP : (b : ℂ) ∈ ball (0 : ℂ) (dom.pairPolynomialScaleBase 0 M /
      (1 + |lam| + Real.sqrt ‖z‖)) :=
    ball_subset_ball (div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)) hb
  have hbC := ball_subset_ball (pairPolynomialScaleRadius_le dom hW hθ hD 0 M lam z).1 hbP
  have he := cepsScaledPositiveCorrectionRoot_exp_decay dom hW hθ hD 0 M lam hlam hz hbC
  rw [norm_exp, neg_mul, neg_re] at he
  have hv : 0 < 16 * Real.sqrt v := by have := CepsCanonDomain.v_pos hW hθ hD; positivity
  have hlo := div_le_div_of_nonneg_right
    (scaledCoordinateLower_drift_frequency_le dom hW hθ hD lam z) hv.le
  have hrate : -dom.scaledCoordinateLower lam z / (16 * Real.sqrt v) ≤
      -dom.positiveBridgeDecayRate * (|lam| + Real.sqrt ‖z‖) := by
    unfold CepsCanonDomain.positiveBridgeDecayRate
    have hr : ((|lam| + Real.sqrt ‖z‖) / Real.sqrt (8 * v + 8)) / (16 * Real.sqrt v) =
        (1 / (Real.sqrt (8 * v + 8) * (16 * Real.sqrt v))) * (|lam| + Real.sqrt ‖z‖) := by ring
    rw [hr] at hlo
    simpa only [neg_div, neg_mul] using neg_le_neg hlo
  have hK : 0 ≤ dom.trueBridgeWeightedConstant M := by
    have := surrogateSlopePolynomialConstant_pos dom hW hθ hD 0 M
    unfold CepsCanonDomain.trueBridgeWeightedConstant
    positivity
  exact (cepsScaledTrueBridgeCorrection_weighted_budget dom hW hθ hD hf hη hM hm lam hz hb).trans
    (mul_le_mul_of_nonneg_left (he.trans (Real.exp_le_exp.mpr hrate)) (by positivity))

end PGM
