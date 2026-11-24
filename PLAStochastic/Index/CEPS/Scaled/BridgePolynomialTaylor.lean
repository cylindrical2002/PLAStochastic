import PLAStochastic.Index.CEPS.Scaled.BridgePolynomialRadius
import PLAStochastic.Index.CEPS.Scaled.NegativeBridgePolynomial
import PLAStochastic.ForMathlib.Analysis.Complex.PolynomialTaylorDisc
import PLAStochastic.Index.CEPS.BrownianCoeff.IntegralBudget

/-! # Drift-integrable all-order polynomial Taylor envelopes for surrogate bridges -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.bridgePolynomialTaylorBound {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (N : ℕ) (M K c : ℝ) (n : ℕ) (lam : ℝ) (z : ℂ) : ℝ :=
  ((n.factorial : ℝ) * K / (dom.bridgePolynomialScaleBase N M / 4) ^ n) *
    (1 + |lam| + Real.sqrt ‖z‖) ^ (n + 1) * Real.exp (-c * (|lam| + Real.sqrt ‖z‖))

theorem cepsBridge_polynomialEnvelope_integrable (d : ℕ) {c : ℝ} (hc : 0 < c)
    (K : ℝ) (z : ℂ) :
    Integrable (fun lam : ℝ => K * (1 + |lam| + Real.sqrt ‖z‖) ^ d *
      Real.exp (-c * (|lam| + Real.sqrt ‖z‖))) := by
  have hi := (cepsBrownian_driftEnvelope_integrable d hc).const_mul
    (|K| * (1 + Real.sqrt ‖z‖) ^ d * Real.exp (-c * Real.sqrt ‖z‖))
  refine hi.mono' (by fun_prop) (ae_of_all _ fun lam => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ (1 + |lam| + Real.sqrt ‖z‖) ^ d),
    abs_of_pos (Real.exp_pos _)]
  have hp : 1 + |lam| + Real.sqrt ‖z‖ ≤ (1 + |lam|) * (1 + Real.sqrt ‖z‖) := by
    nlinarith [mul_nonneg (abs_nonneg lam) (Real.sqrt_nonneg ‖z‖)]
  calc
    _ ≤ |K| * ((1 + |lam|) * (1 + Real.sqrt ‖z‖)) ^ d *
        Real.exp (-c * (|lam| + Real.sqrt ‖z‖)) := by gcongr
    _ = _ := by
      rw [mul_pow, show -c * (|lam| + Real.sqrt ‖z‖) =
        -c * |lam| + -c * Real.sqrt ‖z‖ by ring, Real.exp_add]
      ring

theorem cepsBridge_polynomialTaylorBound_integrable {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (N : ℕ) (M K : ℝ) {c : ℝ} (hc : 0 < c)
    (n : ℕ) (z : ℂ) : Integrable (fun lam : ℝ => dom.bridgePolynomialTaylorBound N M K c n lam z) :=
  cepsBridge_polynomialEnvelope_integrable (n + 1) hc
    ((n.factorial : ℝ) * K / (dom.bridgePolynomialScaleBase N M / 4) ^ n) z

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSurrogateBridge_negative_polynomial_taylor_le {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) (hlam : lam ≤ 0) {z : ℂ} (hz : 0 ≤ z.re) (n : ℕ) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) ((dom.bridgePolynomialScaleBase N M / (1 + |lam| + Real.sqrt ‖z‖)) / 2)) :
    ‖cepsScaledSurrogateBridge dom ρW N lam z b -
      complexTaylorSum (cepsScaledSurrogateBridge dom ρW N lam z) n 0 b‖ ≤
      dom.bridgePolynomialTaylorBound N M (dom.negativeBridgePolynomialConstant N M)
        dom.negativeBridgeDecayRate n lam z * ‖b‖ ^ n := by
  have hrad := (bridgePolynomialScaleRadius_le dom hW hθ hD N M lam z).trans (min_le_left _ _)
  have hsub := ball_subset_ball (x := (0 : ℂ)) hrad
  have hd := ((cepsScaledSurrogateBridge_negative_budget dom hW hθ hD hf hη hM N hN lam hlam hz).1).mono hsub
  have hm := fun b hb => cepsScaledSurrogateBridge_negative_polynomial_budget dom hW hθ hD hf hη hM N hN lam hlam hz (b := b) (hsub hb)
  exact norm_sub_complexTaylorSum_le_polynomial_disc
    (bridgePolynomialScaleBase_pos dom hW hθ hD N M) (by positivity) hd hm n hb

include hW hθ hD in
theorem cepsScaledSurrogateBridgeCorrection_positive_polynomial_taylor_le {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) (hlam : 0 ≤ lam) {z : ℂ} (hz : 0 ≤ z.re) (n : ℕ) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) ((dom.bridgePolynomialScaleBase N M / (1 + |lam| + Real.sqrt ‖z‖)) / 2)) :
    ‖cepsScaledSurrogateBridgeCorrection dom ρW N lam z b -
      complexTaylorSum (cepsScaledSurrogateBridgeCorrection dom ρW N lam z) n 0 b‖ ≤
      dom.bridgePolynomialTaylorBound N M (dom.positiveBridgePolynomialConstant N M)
        dom.positiveBridgeDecayRate n lam z * ‖b‖ ^ n := by
  have hsub := ball_subset_ball (x := (0 : ℂ)) (bridgePolynomialScaleRadius_le dom hW hθ hD N M lam z)
  have hregSub := hsub.trans (ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _)))
  have hd := (cepsScaledSurrogateBridgeCorrection_differentiableOn dom hW hθ hD hf hη hM N hN lam hz).mono hregSub
  have hm := fun b hb => cepsScaledSurrogateBridgeCorrection_positive_budget dom hW hθ hD hf hη hM N hN lam hlam hz (b := b) (hsub hb)
  exact norm_sub_complexTaylorSum_le_polynomial_disc
    (bridgePolynomialScaleBase_pos dom hW hθ hD N M) (by positivity) hd hm n hb

end PGM
