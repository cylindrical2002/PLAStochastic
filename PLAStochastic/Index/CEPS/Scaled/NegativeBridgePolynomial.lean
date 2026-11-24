import PLAStochastic.Index.CEPS.Scaled.NegativeBridge
import PLAStochastic.Index.CEPS.Scaled.CoordinateBudgets

/-! # Polynomial exponential envelopes for negative-drift surrogate bridges -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.negativeBridgePolynomialConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  dom.scaledGapBound * (4 * dom.scaledCoordinateRatioBound / dom.scaledComplexSector) *
      (v * Real.exp (2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8))) +
    8 * v ^ 2 / cepsVarLo D * Real.exp (6 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8))

def CepsCanonDomain.negativeBridgeDecayRate {D θ v : ℝ} (_dom : CepsCanonDomain D θ v) : ℝ :=
  1 / (Real.sqrt (8 * v + 8) * (8 * Real.sqrt v))

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem negativeBridgePolynomial_constants (N : ℕ) (M : ℝ) :
    0 < dom.negativeBridgePolynomialConstant N M ∧ 0 < dom.negativeBridgeDecayRate := by
  have hv := CepsCanonDomain.v_pos hW hθ hD
  have hvl := cepsVarLo_pos hD
  have hK := (cepsScaledSurrogate_constants dom hW hθ hD N M).1
  have hc := (cepsScaledSurrogate_constants dom hW hθ hD N M).2.1
  have hA : 0 ≤ dom.scaledCoordinateRatioBound := Real.sqrt_nonneg _
  unfold CepsCanonDomain.negativeBridgePolynomialConstant CepsCanonDomain.negativeBridgeDecayRate
  constructor <;> positivity

include hW hθ hD in
theorem negativeSurrogateBridgeBound_le_polynomial (N : ℕ) (M lam : ℝ) (z : ℂ) :
    dom.negativeSurrogateBridgeBound N M lam z ≤
      dom.negativeBridgePolynomialConstant N M * (1 + |lam| + Real.sqrt ‖z‖) *
        Real.exp (-dom.negativeBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) := by
  have hv := CepsCanonDomain.v_pos hW hθ hD
  have hvl := cepsVarLo_pos hD
  have hK := (cepsScaledSurrogate_constants dom hW hθ hD N M).1.le
  have hc := (cepsScaledSurrogate_constants dom hW hθ hD N M).2.1
  have hA : 0 ≤ dom.scaledCoordinateRatioBound := Real.sqrt_nonneg _
  let B := dom.canonDriftTaylorBound N M (dom.μ₀ / 8)
  let F := v * Real.exp (2 * B)
  let C := 8 * v ^ 2 / cepsVarLo D * Real.exp (6 * B)
  let X := 1 + |lam| + Real.sqrt ‖z‖
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hX : 1 ≤ X := by dsimp [X]; linarith [abs_nonneg lam, Real.sqrt_nonneg ‖z‖]
  have hSI : dom.scaledRootCoordinateBound lam z * dom.surrogateDeltaInverseBound lam z ≤
      (4 * dom.scaledCoordinateRatioBound / dom.scaledComplexSector) * X := by
    by_cases hne : 0 < lam ^ 2 + ‖z‖
    · exact scaledCoordinateBound_mul_deltaInverse_le dom hW hθ hD lam hne
    · have hl : lam = 0 := by nlinarith [sq_nonneg lam, norm_nonneg z]
      have hz : z = 0 := norm_eq_zero.mp (by nlinarith [sq_nonneg lam, norm_nonneg z])
      subst lam
      subst z
      simp only [CepsCanonDomain.scaledRootCoordinateBound, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
        zero_div, add_zero, mul_zero, Real.sqrt_zero, zero_mul]
      positivity
  have hpre : (dom.scaledGapBound * dom.scaledRootCoordinateBound lam z) * F *
      dom.surrogateDeltaInverseBound lam z + C ≤ dom.negativeBridgePolynomialConstant N M * X := by
    have hh := mul_le_mul_of_nonneg_left hSI (mul_nonneg hK hF)
    have hhC := mul_le_mul_of_nonneg_left hX hC
    change _ ≤ (dom.scaledGapBound * (4 * dom.scaledCoordinateRatioBound / dom.scaledComplexSector) * F + C) * X
    nlinarith
  have hden : 0 < 8 * Real.sqrt v := by positivity
  have hlo := div_le_div_of_nonneg_right
    (scaledCoordinateLower_drift_frequency_le dom hW hθ hD lam z) hden.le
  have he : -dom.scaledCoordinateLower lam z / (8 * Real.sqrt v) ≤
      -dom.negativeBridgeDecayRate * (|lam| + Real.sqrt ‖z‖) := by
    unfold CepsCanonDomain.negativeBridgeDecayRate
    have hr : ((|lam| + Real.sqrt ‖z‖) / Real.sqrt (8 * v + 8)) / (8 * Real.sqrt v) =
        (1 / (Real.sqrt (8 * v + 8) * (8 * Real.sqrt v))) * (|lam| + Real.sqrt ‖z‖) := by ring
    rw [hr] at hlo
    simpa only [neg_div, neg_mul] using neg_le_neg hlo
  unfold CepsCanonDomain.negativeSurrogateBridgeBound
  exact mul_le_mul hpre (Real.exp_le_exp.mpr he) (Real.exp_pos _).le
    (mul_nonneg (negativeBridgePolynomial_constants dom hW hθ hD N M).1.le (by positivity))

include hW hθ hD in
theorem cepsScaledSurrogateBridge_negative_polynomial_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) (hlam : lam ≤ 0) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.complexDirectionScaleRadius N M lam z)) :
    ‖cepsScaledSurrogateBridge dom ρW N lam z b‖ ≤
      dom.negativeBridgePolynomialConstant N M * (1 + |lam| + Real.sqrt ‖z‖) *
        Real.exp (-dom.negativeBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) :=
  ((cepsScaledSurrogateBridge_negative_budget dom hW hθ hD hf hη hM N hN lam hlam hz).2 b hb).trans
    (negativeSurrogateBridgeBound_le_polynomial dom hW hθ hD N M lam z)

end PGM
