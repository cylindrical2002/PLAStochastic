import PLAStochastic.Index.CEPS.Scaled.EndpointSurrogate
import PLAStochastic.ForMathlib.Analysis.Complex.PolynomialTaylorDisc

/-! # Marked endpoint decay and all-order scale Taylor budgets -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.endpointSurrogateTaylorBound {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) (n : ℕ) (z : ℂ) : ℝ :=
  ((n.factorial : ℝ) * dom.endpointSurrogateConstant N M /
    (dom.pairPolynomialScaleBase N M / 4) ^ n) * (2 + Real.sqrt ‖z‖) ^ (n + 1) *
      Real.exp (-dom.entranceBridgeDecayRate * Real.sqrt ‖z‖)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem endpointSurrogateConstant_pos (N : ℕ) (M : ℝ) :
    0 < dom.endpointSurrogateConstant N M := by
  have := surrogateHalfEntranceBound_pos dom hW hθ hD N M
  have := (cepsScaledSurrogate_constants dom hW hθ hD N M).1
  have := CepsCanonDomain.v_pos hW hθ hD
  have := cepsVarLo_pos hD
  unfold CepsCanonDomain.endpointSurrogateConstant CepsCanonDomain.surrogateHalfBridgeWeightedConstant
    CepsCanonDomain.scaledCoordinateRatioBound
  positivity

include hW hθ hD in
theorem cepsScaledSurrogateMarkedEndpoint_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.pairPolynomialScaleBase N M / (2 + Real.sqrt ‖z‖))) :
    ‖cepsScaledSurrogateMarkedEndpoint dom ρW N z b‖ ≤
      dom.endpointSurrogateConstant N M * (2 + Real.sqrt ‖z‖) *
        Real.exp (-dom.entranceBridgeDecayRate * Real.sqrt ‖z‖) := by
  let X := 2 + Real.sqrt ‖z‖
  let B := dom.canonDriftTaylorBound N M (dom.μ₀ / 8)
  let p := (cepsScaledSignedRoot D θ ρW 1 z 1 b * (1 + b)).re
  let t := ((b * z) * (1 + b)).re
  let C := 2 / cepsVarLo D
  have hb' : b ∈ ball (0 : ℂ) (dom.pairPolynomialScaleBase N M / (1 + |(1 : ℝ)| + Real.sqrt ‖z‖)) := by
    simpa only [abs_one, one_add_one_eq_two] using hb
  have hR := pairPolynomialScaleRadius_le dom hW hθ hD N M 1 z
  have hbE := ball_subset_ball hR.2 hb'
  have hbC := ball_subset_ball ((min_le_right _ _).trans
    (div_le_self (canonScaleRadius_pos dom hW hθ hD 1 z).le (by norm_num))) hbE
  have hL := cepsScaledSurrogateMarkExp_budget dom hW hθ hD hf hη hM N hN 1 hz hbE
  simp only [ofReal_one, mul_one] at hL
  have hH := cepsScaledSurrogateHalfEntrance_positive_budget dom hW hθ hD hf hη hM N hN 1 le_rfl hz hb'
  have hU := cepsScaledSurrogateHalfBridge_weighted_budget dom hW hθ hD hf hη hM N hN 1 hz hbC
  simp only [abs_one, one_add_one_eq_two, ofReal_one, mul_one] at hU
  have hdir := cepsScaledRootPlus_marker_drift_loss dom hW hθ hD N M 1 hz hb'
  simp only [abs_one, ofReal_one, mul_one, sub_mul, sub_re] at hdir
  have hc := (entranceBridgePolynomial_constants dom hW hθ hD N M).2
  have he : t - p ≤ C - dom.entranceBridgeDecayRate * Real.sqrt ‖z‖ := by
    dsimp only [t, p, C]
    linarith [hc.le]
  have hE : ‖exp ((b * z) * (1 + b))‖ = Real.exp t := norm_exp _
  have hH0 := (surrogateHalfEntranceBound_pos dom hW hθ hD N M).le
  have hnorm : ‖cepsScaledSurrogateMarkedEndpoint dom ρW N z b‖ ≤
      Real.exp t * Real.exp B * dom.surrogateHalfEntranceBound N M *
        (dom.surrogateHalfBridgeWeightedConstant N M * X * Real.exp (-p)) := by
    unfold cepsScaledSurrogateMarkedEndpoint
    rw [norm_mul, norm_mul, norm_mul, hE]
    gcongr
  have hKU : 0 ≤ dom.surrogateHalfBridgeWeightedConstant N M := by
    have := (cepsScaledSurrogate_constants dom hW hθ hD N M).1.le
    have hA : 0 ≤ dom.scaledCoordinateRatioBound := Real.sqrt_nonneg _
    have := CepsCanonDomain.v_pos hW hθ hD
    unfold CepsCanonDomain.surrogateHalfBridgeWeightedConstant
    positivity
  apply hnorm.trans
  calc
    _ = (Real.exp B * dom.surrogateHalfEntranceBound N M *
        dom.surrogateHalfBridgeWeightedConstant N M * X) * (Real.exp t * Real.exp (-p)) := by ring
    _ = (Real.exp B * dom.surrogateHalfEntranceBound N M *
        dom.surrogateHalfBridgeWeightedConstant N M * X) * Real.exp (t - p) := by
      rw [← Real.exp_add]
      congr 1
    _ ≤ (Real.exp B * dom.surrogateHalfEntranceBound N M *
        dom.surrogateHalfBridgeWeightedConstant N M * X) *
          Real.exp (C - dom.entranceBridgeDecayRate * Real.sqrt ‖z‖) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by
        have := (surrogateHalfEntranceBound_pos dom hW hθ hD N M).le
        dsimp only [X]
        positivity)
    _ = _ := by
      unfold CepsCanonDomain.endpointSurrogateConstant
      rw [show C - dom.entranceBridgeDecayRate * Real.sqrt ‖z‖ =
        C + -dom.entranceBridgeDecayRate * Real.sqrt ‖z‖ by ring, Real.exp_add]
      dsimp only [B, C, X]
      ring

include hW hθ hD in
theorem cepsScaledSurrogateMarkedEndpoint_taylor_le {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    {z : ℂ} (hz : 0 ≤ z.re) (n : ℕ) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) ((dom.pairPolynomialScaleBase N M / (2 + Real.sqrt ‖z‖)) / 2)) :
    ‖cepsScaledSurrogateMarkedEndpoint dom ρW N z b -
      complexTaylorSum (cepsScaledSurrogateMarkedEndpoint dom ρW N z) n 0 b‖ ≤
        dom.endpointSurrogateTaylorBound N M n z * ‖b‖ ^ n := by
  have hh := norm_sub_complexTaylorSum_le_polynomial_disc
    (pairPolynomialScaleBase_pos dom hW hθ hD N M) (by positivity : 0 < 2 + Real.sqrt ‖z‖)
    (cepsScaledSurrogateMarkedEndpoint_differentiableOn dom hW hθ hD hf hη hM N hN hz)
    (fun b hb => cepsScaledSurrogateMarkedEndpoint_budget dom hW hθ hD hf hη hM N hN hz hb) n hb
  exact hh

end PGM
