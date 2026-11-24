import PLAStochastic.Index.CEPS.Scaled.CompletePairBudget
import PLAStochastic.ForMathlib.Analysis.Complex.PolynomialTaylorDisc

/-! # Complete-pair scale jets and drift-integrable Taylor remainders at every frequency -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.completePairScaleJetBound {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (N : ℕ) (M : ℝ) (n : ℕ) (lam : ℝ) (z : ℂ) : ℝ :=
  ((n.factorial : ℝ) * dom.completePairConstant N M /
    (dom.completePairScaleBase N M / 2) ^ n) *
      (1 + |lam| + Real.sqrt ‖z‖) ^ (n + 4) *
        Real.exp (-dom.positiveEntranceBridgeDecayRate * (|lam| + Real.sqrt ‖z‖))

def CepsCanonDomain.completePairTaylorBound {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (N : ℕ) (M : ℝ) (n : ℕ) (lam : ℝ) (z : ℂ) : ℝ :=
  ((n.factorial : ℝ) * dom.completePairConstant N M /
    (dom.completePairScaleBase N M / 4) ^ n) *
      (1 + |lam| + Real.sqrt ‖z‖) ^ (n + 4) *
        Real.exp (-dom.positiveEntranceBridgeDecayRate * (|lam| + Real.sqrt ‖z‖))

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSurrogateSubtractedPair_complete_scale_jet_le {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    (n : ℕ) :
    ‖iteratedDeriv n (cepsScaledSurrogateSubtractedPair dom ρW N lam z) 0‖ ≤
      dom.completePairScaleJetBound N M n lam z := by
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let R := dom.completePairScaleBase N M
  have hX : 0 < X := by dsimp [X]; positivity
  have hR : 0 < R := completePairScaleBase_pos dom hW hθ hD N M
  have hd := cepsScaledSurrogateSubtractedPair_complete_differentiableOn dom hW hθ hD hf hη hM N hN lam hz
  have hm : ∀ b ∈ ball (0 : ℂ) (R / X),
      ‖cepsScaledSurrogateSubtractedPair dom ρW N lam z b‖ ≤ dom.completePairConstant N M * X ^ 4 *
        Real.exp (-dom.positiveEntranceBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) :=
    fun _ hb => cepsScaledSurrogateSubtractedPair_complete_budget dom hW hθ hD hf hη hM N hN lam hz hb
  have h := norm_iteratedDeriv_le_of_ball n (div_pos hR hX) hd hm
  apply h.trans_eq
  unfold CepsCanonDomain.completePairScaleJetBound
  change _ = _ * X ^ (n + 4) * _
  rw [show (R / X / 2) ^ n = (R / 2) ^ n / X ^ n by rw [show R / X / 2 = R / 2 / X by ring, div_pow],
    div_div_eq_mul_div, pow_add]
  ring

include hW hθ hD in
theorem cepsScaledSurrogateSubtractedPair_complete_taylor_le {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    (n : ℕ) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ)
      ((dom.completePairScaleBase N M / (1 + |lam| + Real.sqrt ‖z‖)) / 2)) :
    ‖cepsScaledSurrogateSubtractedPair dom ρW N lam z b -
      complexTaylorSum (cepsScaledSurrogateSubtractedPair dom ρW N lam z) n 0 b‖ ≤
      dom.completePairTaylorBound N M n lam z * ‖b‖ ^ n := by
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let R := dom.completePairScaleBase N M
  have hd := cepsScaledSurrogateSubtractedPair_complete_differentiableOn dom hW hθ hD hf hη hM N hN lam hz
  have hm : ∀ c ∈ ball (0 : ℂ) (R / X),
      ‖cepsScaledSurrogateSubtractedPair dom ρW N lam z c‖ ≤
        (dom.completePairConstant N M * X ^ 3) * X *
          Real.exp (-dom.positiveEntranceBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) := by
    intro c hc
    exact (cepsScaledSurrogateSubtractedPair_complete_budget dom hW hθ hD hf hη hM N hN lam hz hc).trans_eq (by ring)
  have h := norm_sub_complexTaylorSum_le_polynomial_disc
    (completePairScaleBase_pos dom hW hθ hD N M) (by positivity) hd hm n hb
  apply h.trans_eq
  unfold CepsCanonDomain.completePairTaylorBound
  change _ = _ * X ^ (n + 4) * _ * _
  rw [show n + 4 = 3 + (n + 1) by omega, pow_add]
  ring

include hW hθ hD in
theorem cepsScaledSurrogateSubtractedPair_complete_taylorEnvelope_integrable
    (N : ℕ) (M : ℝ) (n : ℕ) (z : ℂ) :
    Integrable (fun lam : ℝ => dom.completePairTaylorBound N M n lam z) :=
  cepsBridge_polynomialEnvelope_integrable (n + 4)
    (positiveEntranceBridge_constants dom hW hθ hD N M).2
      ((n.factorial : ℝ) * dom.completePairConstant N M /
        (dom.completePairScaleBase N M / 4) ^ n) z

end PGM
