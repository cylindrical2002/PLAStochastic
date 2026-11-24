import PLAStochastic.Index.CEPS.Scaled.OuterPairPolynomialRadius
import PLAStochastic.Index.CEPS.Scaled.OuterSubtractedPair
import PLAStochastic.ForMathlib.Analysis.Complex.PolynomialTaylorDisc

/-! # Genuine complete-pair scale jets and drift-integrable outer Taylor remainders -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.outerPairScaleJetBound {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (N : ℕ) (M : ℝ) (n : ℕ) (lam : ℝ) (z : ℂ) : ℝ :=
  ((n.factorial : ℝ) * dom.outerSubtractedPairConstant N M /
    (dom.outerPairPolynomialScaleBase N M / 2) ^ n) *
      (1 + |lam| + Real.sqrt ‖z‖) ^ (n + 4) *
        Real.exp (-dom.positiveEntranceBridgeDecayRate * (|lam| + Real.sqrt ‖z‖))

def CepsCanonDomain.outerPairTaylorBound {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (N : ℕ) (M : ℝ) (n : ℕ) (lam : ℝ) (z : ℂ) : ℝ :=
  ((n.factorial : ℝ) * dom.outerSubtractedPairConstant N M /
    (dom.outerPairPolynomialScaleBase N M / 4) ^ n) *
      (1 + |lam| + Real.sqrt ‖z‖) ^ (n + 4) *
        Real.exp (-dom.positiveEntranceBridgeDecayRate * (|lam| + Real.sqrt ‖z‖))

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSurrogateSubtractedPair_outer_scale_jet_le {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    (houter : dom.centralFrequencyDriftRadius N M < |lam| ∨ dom.centralFrequencyRadius N M ≤ ‖z‖)
    (n : ℕ) :
    ‖iteratedDeriv n (cepsScaledSurrogateSubtractedPair dom ρW N lam z) 0‖ ≤
      dom.outerPairScaleJetBound N M n lam z := by
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let R := dom.outerPairPolynomialScaleBase N M
  have hX : 0 < X := by dsimp [X]; positivity
  have hR : 0 < R := outerPairPolynomialScaleBase_pos dom hW hθ hD N M
  have hsub : ball (0 : ℂ) (R / X) ⊆ ball 0 (dom.outerPairScaleRadius N M lam z) :=
    ball_subset_ball (outerPairPolynomialScaleRadius_le dom hW hθ hD N M lam z)
  have hd := (cepsScaledSurrogateSubtractedPair_outer_differentiableOn dom hW hθ hD hf hη hM N hN lam hz
    (outerFrequency_ne_origin dom hW hθ hD N M lam z houter)).mono hsub
  have hm : ∀ b ∈ ball (0 : ℂ) (R / X),
      ‖cepsScaledSurrogateSubtractedPair dom ρW N lam z b‖ ≤ dom.outerSubtractedPairConstant N M * X ^ 4 *
        Real.exp (-dom.positiveEntranceBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) :=
    fun _ hb => cepsScaledSurrogateSubtractedPair_outer_budget dom hW hθ hD hf hη hM N hN lam hz houter (hsub hb)
  have h := norm_iteratedDeriv_le_of_ball n (div_pos hR hX) hd hm
  apply h.trans_eq
  unfold CepsCanonDomain.outerPairScaleJetBound
  change _ = _ * X ^ (n + 4) * _
  rw [show (R / X / 2) ^ n = (R / 2) ^ n / X ^ n by rw [show R / X / 2 = R / 2 / X by ring, div_pow],
    div_div_eq_mul_div, pow_add]
  ring

include hW hθ hD in
theorem cepsScaledSurrogateSubtractedPair_outer_taylor_le {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    (houter : dom.centralFrequencyDriftRadius N M < |lam| ∨ dom.centralFrequencyRadius N M ≤ ‖z‖)
    (n : ℕ) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ)
      ((dom.outerPairPolynomialScaleBase N M / (1 + |lam| + Real.sqrt ‖z‖)) / 2)) :
    ‖cepsScaledSurrogateSubtractedPair dom ρW N lam z b -
      complexTaylorSum (cepsScaledSurrogateSubtractedPair dom ρW N lam z) n 0 b‖ ≤
      dom.outerPairTaylorBound N M n lam z * ‖b‖ ^ n := by
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let R := dom.outerPairPolynomialScaleBase N M
  have hsub : ball (0 : ℂ) (R / X) ⊆ ball 0 (dom.outerPairScaleRadius N M lam z) :=
    ball_subset_ball (outerPairPolynomialScaleRadius_le dom hW hθ hD N M lam z)
  have hd := (cepsScaledSurrogateSubtractedPair_outer_differentiableOn dom hW hθ hD hf hη hM N hN lam hz
    (outerFrequency_ne_origin dom hW hθ hD N M lam z houter)).mono hsub
  have hm : ∀ c ∈ ball (0 : ℂ) (R / X),
      ‖cepsScaledSurrogateSubtractedPair dom ρW N lam z c‖ ≤
        (dom.outerSubtractedPairConstant N M * X ^ 3) * X *
          Real.exp (-dom.positiveEntranceBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) := by
    intro c hc
    exact (cepsScaledSurrogateSubtractedPair_outer_budget dom hW hθ hD hf hη hM N hN lam hz houter (hsub hc)).trans_eq (by ring)
  have h := norm_sub_complexTaylorSum_le_polynomial_disc
    (outerPairPolynomialScaleBase_pos dom hW hθ hD N M) (by dsimp [X]; positivity) hd hm n hb
  apply h.trans_eq
  unfold CepsCanonDomain.outerPairTaylorBound
  change _ = _ * X ^ (n + 4) * _ * _
  rw [show n + 4 = 3 + (n + 1) by omega, pow_add]
  ring

include hW hθ hD in
theorem cepsScaledSurrogateSubtractedPair_outer_taylorEnvelope_integrable
    (N : ℕ) (M : ℝ) (n : ℕ) (z : ℂ) :
    Integrable (fun lam : ℝ => dom.outerPairTaylorBound N M n lam z) :=
  cepsBridge_polynomialEnvelope_integrable (n + 4)
    (positiveEntranceBridge_constants dom hW hθ hD N M).2
      ((n.factorial : ℝ) * dom.outerSubtractedPairConstant N M /
        (dom.outerPairPolynomialScaleBase N M / 4) ^ n) z

end PGM
