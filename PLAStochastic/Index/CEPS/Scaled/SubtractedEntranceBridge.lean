import PLAStochastic.Index.CEPS.Scaled.CentralEntranceBridgeDecay
import PLAStochastic.Index.CEPS.Scaled.PositiveEntranceBridgeTaylor
import PLAStochastic.Index.CEPS.Scaled.EntranceBridgeTaylor

/-! # One subtracted entrance-square bridge amplitude for all scaled drifts -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def cepsScaledSurrogateSubtractedEntranceBridge {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (N : ℕ) (lam : ℝ) (z b : ℂ) : ℂ :=
  if 1 ≤ lam then cepsScaledSurrogateEntranceBridgeCorrection dom ρW N lam z b
  else cepsScaledSurrogateEntranceBridge dom ρW N lam z b

def CepsCanonDomain.subtractedEntranceBridgeConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  dom.entranceBridgePolynomialConstant N M + dom.centralEntranceBridgeConstant N M +
    dom.positiveEntranceBridgeConstant N M

def CepsCanonDomain.subtractedEntranceBridgeTaylorBound {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) (n : ℕ) (lam : ℝ) (z : ℂ) : ℝ :=
  ((n.factorial : ℝ) * dom.subtractedEntranceBridgeConstant N M /
    (dom.pairPolynomialScaleBase N M / 4) ^ n) *
      (1 + |lam| + Real.sqrt ‖z‖) ^ (n + 3) *
        Real.exp (-dom.positiveEntranceBridgeDecayRate * (|lam| + Real.sqrt ‖z‖))

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSurrogateSubtractedEntranceBridge_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) :
    DifferentiableOn ℂ (cepsScaledSurrogateSubtractedEntranceBridge dom ρW N lam z)
      (ball 0 (dom.pairPolynomialScaleBase N M / (1 + |lam| + Real.sqrt ‖z‖))) ∧
    ∀ b ∈ ball (0 : ℂ) (dom.pairPolynomialScaleBase N M / (1 + |lam| + Real.sqrt ‖z‖)),
      ‖cepsScaledSurrogateSubtractedEntranceBridge dom ρW N lam z b‖ ≤
        dom.subtractedEntranceBridgeConstant N M * (1 + |lam| + Real.sqrt ‖z‖) ^ 3 *
          Real.exp (-dom.positiveEntranceBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) := by
  have hn := (entranceBridgePolynomial_constants dom hW hθ hD N M).1.le
  have hc : 0 ≤ dom.centralEntranceBridgeConstant N M := by
    unfold CepsCanonDomain.centralEntranceBridgeConstant
    exact mul_nonneg hn (Real.exp_pos _).le
  have hp := (positiveEntranceBridge_constants dom hW hθ hD N M).1.le
  have hKneg : dom.entranceBridgePolynomialConstant N M ≤ dom.subtractedEntranceBridgeConstant N M := by
    unfold CepsCanonDomain.subtractedEntranceBridgeConstant
    linarith
  have hKcentral : dom.centralEntranceBridgeConstant N M ≤ dom.subtractedEntranceBridgeConstant N M := by
    unfold CepsCanonDomain.subtractedEntranceBridgeConstant
    linarith
  have hKpositive : dom.positiveEntranceBridgeConstant N M ≤ dom.subtractedEntranceBridgeConstant N M := by
    unfold CepsCanonDomain.subtractedEntranceBridgeConstant
    linarith
  have hKpos : 0 ≤ dom.subtractedEntranceBridgeConstant N M := hn.trans hKneg
  have hExp : Real.exp (-dom.entranceBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) ≤
      Real.exp (-dom.positiveEntranceBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) := by
    apply Real.exp_le_exp.mpr
    simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_right
      (show dom.positiveEntranceBridgeDecayRate ≤ dom.entranceBridgeDecayRate from min_le_left _ _)
      (by positivity : (0 : ℝ) ≤ |lam| + Real.sqrt ‖z‖))
  by_cases hlam : 1 ≤ lam
  · have heq : cepsScaledSurrogateSubtractedEntranceBridge dom ρW N lam z =
        cepsScaledSurrogateEntranceBridgeCorrection dom ρW N lam z := by
      funext b
      exact if_pos hlam
    rw [heq]
    refine ⟨cepsScaledSurrogateEntranceBridgeCorrection_differentiableOn dom hW hθ hD hf hη hM N hN lam hlam hz, fun b hb => ?_⟩
    apply (cepsScaledSurrogateEntranceBridgeCorrection_positive_budget dom hW hθ hD hf hη hM N hN lam hlam hz hb).trans
    gcongr
  · have heq : cepsScaledSurrogateSubtractedEntranceBridge dom ρW N lam z =
        cepsScaledSurrogateEntranceBridge dom ρW N lam z := by
      funext b
      exact if_neg hlam
    rw [heq]
    refine ⟨cepsScaledSurrogateEntranceBridge_differentiableOn dom hW hθ hD hf hη hM N hN lam hz, fun b hb => ?_⟩
    by_cases hneg : lam ≤ 0
    · apply (cepsScaledSurrogateEntranceBridge_negative_budget dom hW hθ hD hf hη hM N hN lam hneg hz hb).trans
      exact mul_le_mul (mul_le_mul_of_nonneg_right hKneg (by positivity)) hExp
        (Real.exp_pos _).le (by positivity)
    · have hcentral : |lam| ≤ 1 := by rw [abs_of_nonneg (le_of_not_ge hneg)]; linarith
      apply (cepsScaledSurrogateEntranceBridge_central_budget dom hW hθ hD hf hη hM N hN lam hcentral hz hb).trans
      exact mul_le_mul (mul_le_mul_of_nonneg_right hKcentral (by positivity)) hExp
        (Real.exp_pos _).le (by positivity)

include hW hθ hD in
theorem cepsScaledSurrogateSubtractedEntranceBridge_taylor_le {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) (n : ℕ) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) ((dom.pairPolynomialScaleBase N M / (1 + |lam| + Real.sqrt ‖z‖)) / 2)) :
    ‖cepsScaledSurrogateSubtractedEntranceBridge dom ρW N lam z b -
      complexTaylorSum (cepsScaledSurrogateSubtractedEntranceBridge dom ρW N lam z) n 0 b‖ ≤
        dom.subtractedEntranceBridgeTaylorBound N M n lam z * ‖b‖ ^ n := by
  let X := 1 + |lam| + Real.sqrt ‖z‖
  obtain ⟨hd, hbound⟩ := cepsScaledSurrogateSubtractedEntranceBridge_budget dom hW hθ hD hf hη hM N hN lam hz
  have hm : ∀ b ∈ ball (0 : ℂ) (dom.pairPolynomialScaleBase N M / X),
      ‖cepsScaledSurrogateSubtractedEntranceBridge dom ρW N lam z b‖ ≤
        (dom.subtractedEntranceBridgeConstant N M * X ^ 2) * X *
          Real.exp (-dom.positiveEntranceBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) := by
    intro b hb
    exact (hbound b hb).trans_eq (by ring)
  have hh := norm_sub_complexTaylorSum_le_polynomial_disc
    (pairPolynomialScaleBase_pos dom hW hθ hD N M) (by positivity) hd hm n hb
  apply hh.trans_eq
  unfold CepsCanonDomain.subtractedEntranceBridgeTaylorBound
  change _ = _ * X ^ (n + 3) * _ * _
  rw [show n + 3 = 2 + (n + 1) by omega, pow_add]
  ring

include hW hθ hD in
theorem cepsScaledSurrogateSubtractedEntranceBridge_taylorEnvelope_integrable (N : ℕ) (M : ℝ)
    (n : ℕ) (z : ℂ) : Integrable (fun lam : ℝ => dom.subtractedEntranceBridgeTaylorBound N M n lam z) :=
  cepsBridge_polynomialEnvelope_integrable (n + 3)
    (positiveEntranceBridge_constants dom hW hθ hD N M).2
    ((n.factorial : ℝ) * dom.subtractedEntranceBridgeConstant N M /
      (dom.pairPolynomialScaleBase N M / 4) ^ n) z

end PGM
