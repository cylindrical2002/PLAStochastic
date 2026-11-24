import PLAStochastic.Index.CEPS.Scaled.PositiveEntranceBridgeDecay
import PLAStochastic.Index.CEPS.Scaled.SurrogateHalfEntranceHolomorphy
import PLAStochastic.Index.CEPS.Scaled.BridgePolynomialTaylor

/-! # Drift-integrable scale Taylor envelopes after positive half-line subtraction -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.positiveEntranceBridgeTaylorBound {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (N : ℕ) (M : ℝ) (n : ℕ) (lam : ℝ) (z : ℂ) : ℝ :=
  ((n.factorial : ℝ) * dom.positiveEntranceBridgeConstant N M /
    (dom.pairPolynomialScaleBase N M / 4) ^ n) *
      (1 + |lam| + Real.sqrt ‖z‖) ^ (n + 3) *
        Real.exp (-dom.positiveEntranceBridgeDecayRate * (|lam| + Real.sqrt ‖z‖))

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSurrogateEntranceBridgeCorrection_differentiableOn {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) (hlam : 1 ≤ lam) {z : ℂ} (hz : 0 ≤ z.re) :
    DifferentiableOn ℂ (cepsScaledSurrogateEntranceBridgeCorrection dom ρW N lam z)
      (ball 0 (dom.pairPolynomialScaleBase N M / (1 + |lam| + Real.sqrt ‖z‖))) := by
  let U : Set ℂ := ball 0 (dom.pairPolynomialScaleBase N M / (1 + |lam| + Real.sqrt ‖z‖))
  have hsub : U ⊆ ball (0 : ℂ) (dom.surrogateRegularScaleRadius N M lam z) :=
    ball_subset_ball ((pairPolynomialScaleRadius_le dom hW hθ hD N M lam z).2.trans (min_le_left _ _))
  have hU := (cepsScaledSurrogateBridge_differentiableOn dom hW hθ hD hf hη hM N hN lam hz).mono hsub
  have hUc := (cepsScaledSurrogateBridgeCorrection_differentiableOn dom hW hθ hD hf hη hM N hN lam hz).mono hsub
  have hUh : DifferentiableOn ℂ (cepsScaledSurrogateHalfBridge dom ρW N lam z) U :=
    (hU.sub hUc).congr (fun b _ => by
      change cepsScaledSurrogateHalfBridge dom ρW N lam z b =
        cepsScaledSurrogateBridge dom ρW N lam z b -
          (cepsScaledSurrogateBridge dom ρW N lam z b - cepsScaledSurrogateHalfBridge dom ρW N lam z b)
      ring)
  have hHh := cepsScaledSurrogateHalfEntrance_differentiableOn dom hW hθ hD (M := M) hf hη N hN lam hlam hz
  have hE : DifferentiableOn ℂ (fun b : ℂ => exp ((b * z) * (1 + b * lam))) U := by fun_prop
  exact (cepsScaledSurrogateEntranceBridge_differentiableOn dom hW hθ hD hf hη hM N hN lam hz).sub
    ((hE.mul (hHh.pow 2)).mul hUh)

include hW hθ hD in
theorem cepsScaledSurrogateEntranceBridgeCorrection_positive_taylor_le {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) (hlam : 1 ≤ lam) {z : ℂ} (hz : 0 ≤ z.re) (n : ℕ) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) ((dom.pairPolynomialScaleBase N M / (1 + |lam| + Real.sqrt ‖z‖)) / 2)) :
    ‖cepsScaledSurrogateEntranceBridgeCorrection dom ρW N lam z b -
      complexTaylorSum (cepsScaledSurrogateEntranceBridgeCorrection dom ρW N lam z) n 0 b‖ ≤
        dom.positiveEntranceBridgeTaylorBound N M n lam z * ‖b‖ ^ n := by
  let X := 1 + |lam| + Real.sqrt ‖z‖
  have hd := cepsScaledSurrogateEntranceBridgeCorrection_differentiableOn dom hW hθ hD hf hη hM N hN lam hlam hz
  have hm : ∀ b ∈ ball (0 : ℂ) (dom.pairPolynomialScaleBase N M / X),
      ‖cepsScaledSurrogateEntranceBridgeCorrection dom ρW N lam z b‖ ≤
        (dom.positiveEntranceBridgeConstant N M * X ^ 2) * X *
          Real.exp (-dom.positiveEntranceBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) := by
    intro b hb
    exact (cepsScaledSurrogateEntranceBridgeCorrection_positive_budget dom hW hθ hD hf hη hM N hN lam hlam hz hb).trans_eq (by ring)
  have hh := norm_sub_complexTaylorSum_le_polynomial_disc
    (pairPolynomialScaleBase_pos dom hW hθ hD N M) (by positivity) hd hm n hb
  apply hh.trans_eq
  unfold CepsCanonDomain.positiveEntranceBridgeTaylorBound
  change _ = _ * X ^ (n + 3) * _ * _
  rw [show n + 3 = 2 + (n + 1) by omega, pow_add]
  ring

include hW hθ hD in
theorem cepsScaledSurrogateEntranceBridgeCorrection_taylorEnvelope_integrable (N : ℕ) (M : ℝ)
    (n : ℕ) (z : ℂ) : Integrable (fun lam : ℝ => dom.positiveEntranceBridgeTaylorBound N M n lam z) :=
  cepsBridge_polynomialEnvelope_integrable (n + 3)
    (positiveEntranceBridge_constants dom hW hθ hD N M).2
    ((n.factorial : ℝ) * dom.positiveEntranceBridgeConstant N M /
      (dom.pairPolynomialScaleBase N M / 4) ^ n) z

end PGM
