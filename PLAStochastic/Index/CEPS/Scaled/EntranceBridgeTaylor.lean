import PLAStochastic.Index.CEPS.Scaled.EntranceBridgeDecay
import PLAStochastic.Index.CEPS.Scaled.BridgePolynomialTaylor

/-! # Integrable all-order scale Taylor envelopes for entrance-square bridges -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.entranceBridgeTaylorBound {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (N : ℕ) (M : ℝ) (n : ℕ) (lam : ℝ) (z : ℂ) : ℝ :=
  ((n.factorial : ℝ) * dom.entranceBridgePolynomialConstant N M /
    (dom.pairPolynomialScaleBase N M / 4) ^ n) *
      (1 + |lam| + Real.sqrt ‖z‖) ^ (n + 3) *
        Real.exp (-dom.entranceBridgeDecayRate * (|lam| + Real.sqrt ‖z‖))

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSurrogateEntranceBridge_negative_taylor_le {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) (hlam : lam ≤ 0) {z : ℂ} (hz : 0 ≤ z.re) (n : ℕ) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) ((dom.pairPolynomialScaleBase N M / (1 + |lam| + Real.sqrt ‖z‖)) / 2)) :
    ‖cepsScaledSurrogateEntranceBridge dom ρW N lam z b -
      complexTaylorSum (cepsScaledSurrogateEntranceBridge dom ρW N lam z) n 0 b‖ ≤
        dom.entranceBridgeTaylorBound N M n lam z * ‖b‖ ^ n := by
  let X := 1 + |lam| + Real.sqrt ‖z‖
  have hd := cepsScaledSurrogateEntranceBridge_differentiableOn dom hW hθ hD hf hη hM N hN lam hz
  have hm : ∀ b ∈ ball (0 : ℂ) (dom.pairPolynomialScaleBase N M / X),
      ‖cepsScaledSurrogateEntranceBridge dom ρW N lam z b‖ ≤
        (dom.entranceBridgePolynomialConstant N M * X ^ 2) * X *
          Real.exp (-dom.entranceBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) := by
    intro b hb
    exact (cepsScaledSurrogateEntranceBridge_negative_budget dom hW hθ hD hf hη hM N hN lam hlam hz hb).trans_eq (by ring)
  have hh := norm_sub_complexTaylorSum_le_polynomial_disc
    (pairPolynomialScaleBase_pos dom hW hθ hD N M) (by positivity) hd hm n hb
  apply hh.trans_eq
  unfold CepsCanonDomain.entranceBridgeTaylorBound
  change _ = _ * X ^ (n + 3) * _ * _
  rw [show n + 3 = 2 + (n + 1) by omega, pow_add]
  ring

include hW hθ hD in
theorem cepsScaledSurrogateEntranceBridge_taylorEnvelope_integrable (N : ℕ) (M : ℝ)
    (n : ℕ) (z : ℂ) : Integrable (fun lam : ℝ => dom.entranceBridgeTaylorBound N M n lam z) :=
  cepsBridge_polynomialEnvelope_integrable (n + 3)
    (entranceBridgePolynomial_constants dom hW hθ hD N M).2
    ((n.factorial : ℝ) * dom.entranceBridgePolynomialConstant N M /
      (dom.pairPolynomialScaleBase N M / 4) ^ n) z

end PGM
