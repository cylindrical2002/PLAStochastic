import PLAStochastic.Index.CEPS.Scaled.SurrogateEntranceBudget
import PLAStochastic.Index.CEPS.Scaled.SurrogateBridgeWeighted
import PLAStochastic.Index.CEPS.Scaled.PairRootDirections

/-! # Exponential decay of the negative-drift entrance-square bridge amplitude -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

private theorem weighted_square_decay {p m t d : ℝ}
    (h₁ : d ≤ p - t) (h₂ : d ≤ p - 2 * m + t) :
    Real.exp t * (2 + Real.exp (m - t)) ^ 2 * Real.exp (-p) ≤ 10 * Real.exp (-d) := by
  have hs : (2 + Real.exp (m - t)) ^ 2 ≤ 8 + 2 * (Real.exp (m - t)) ^ 2 := by
    nlinarith [sq_nonneg (Real.exp (m - t) - 2)]
  have he₁ : Real.exp (t - p) ≤ Real.exp (-d) := Real.exp_le_exp.mpr (by linarith)
  have he₂ : Real.exp (2 * m - t - p) ≤ Real.exp (-d) := Real.exp_le_exp.mpr (by linarith)
  calc
    _ ≤ Real.exp t * (8 + 2 * (Real.exp (m - t)) ^ 2) * Real.exp (-p) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le) (Real.exp_pos _).le
    _ = 8 * Real.exp (t - p) + 2 * Real.exp (2 * m - t - p) := by
      rw [pow_two]
      have he : Real.exp t * (Real.exp (m - t) * Real.exp (m - t)) * Real.exp (-p) =
          Real.exp (2 * m - t - p) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      have he' : Real.exp t * Real.exp (-p) = Real.exp (t - p) := by
        rw [← Real.exp_add, sub_eq_add_neg]
      linear_combination 2 * he + 8 * he'
    _ ≤ _ := by linarith

def cepsScaledSurrogateEntranceBridge {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (N : ℕ) (lam : ℝ) (z b : ℂ) : ℂ :=
  exp ((b * z) * (1 + b * lam)) * (cepsScaledSurrogateEntrance dom ρW N lam z b) ^ 2 *
    cepsScaledSurrogateBridge dom ρW N lam z b

def CepsCanonDomain.entranceBridgePolynomialConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  10 * (dom.surrogateEntrancePolynomialConstant N M) ^ 2 * dom.surrogateBridgeWeightedConstant N M

def CepsCanonDomain.entranceBridgeDecayRate {D θ v : ℝ} (_dom : CepsCanonDomain D θ v) : ℝ :=
  1 / (Real.sqrt (8 * v + 8) * (32 * Real.sqrt v))

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem entranceBridgePolynomial_constants (N : ℕ) (M : ℝ) :
    0 < dom.entranceBridgePolynomialConstant N M ∧ 0 < dom.entranceBridgeDecayRate := by
  have := surrogateEntrancePolynomialConstant_pos dom hW hθ hD N M
  have := surrogateSlopePolynomialConstant_pos dom hW hθ hD N M
  have := CepsCanonDomain.v_pos hW hθ hD
  unfold CepsCanonDomain.entranceBridgePolynomialConstant CepsCanonDomain.surrogateBridgeWeightedConstant
    CepsCanonDomain.entranceBridgeDecayRate
  constructor <;> positivity

include hW hθ hD in
theorem cepsScaledSurrogateEntranceBridge_differentiableOn {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) :
    DifferentiableOn ℂ (cepsScaledSurrogateEntranceBridge dom ρW N lam z)
      (ball 0 (dom.pairPolynomialScaleBase N M / (1 + |lam| + Real.sqrt ‖z‖))) := by
  have hR := pairPolynomialScaleRadius_le dom hW hθ hD N M lam z
  have hH := (cepsScaledSurrogateEntrance_differentiableOn dom hW hθ hD hf hη hM N hN lam hz).mono
    (ball_subset_ball hR.2)
  have hU := (cepsScaledSurrogateBridge_differentiableOn dom hW hθ hD hf hη hM N hN lam hz).mono
    (ball_subset_ball (hR.2.trans (min_le_left _ _)))
  exact ((by fun_prop : DifferentiableOn ℂ (fun b : ℂ => exp ((b * z) * (1 + b * lam))) _).mul
    (hH.pow 2)).mul hU

include hW hθ hD in
theorem cepsScaledSurrogateEntranceBridge_negative_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) (hlam : lam ≤ 0) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.pairPolynomialScaleBase N M / (1 + |lam| + Real.sqrt ‖z‖))) :
    ‖cepsScaledSurrogateEntranceBridge dom ρW N lam z b‖ ≤
      dom.entranceBridgePolynomialConstant N M * (1 + |lam| + Real.sqrt ‖z‖) ^ 3 *
        Real.exp (-dom.entranceBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) := by
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let p := (cepsScaledSignedRoot D θ ρW lam z 1 b * (1 + b * lam)).re
  let m := (cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + b * lam)).re
  let t := ((b * z) * (1 + b * lam)).re
  have hR := pairPolynomialScaleRadius_le dom hW hθ hD N M lam z
  have hbE := ball_subset_ball hR.2 hb
  have hbReg := ball_subset_ball (min_le_left _ _) hbE
  have hH := cepsScaledSurrogateEntrance_polynomial_budget dom hW hθ hD hf hη hM N hN lam hz hbE
  have hU := cepsScaledSurrogateBridge_weighted_budget dom hW hθ hD hf hη hM N hN lam hz hbReg
  have hdirs := cepsScaledPairRoot_negative_directions dom hW hθ hD N M lam hlam hz hb
  have ht : dom.scaledCoordinateLower lam z ≤ ‖cepsScaledRootCoordinate D θ ρW lam z b‖ :=
    cepsScaledRootCoordinate_lower dom hW hθ hD N M lam hz (ball_subset_ball (min_le_left _ _) hbReg)
  have hτ := scaledCoordinateLower_drift_frequency_le dom hW hθ hD lam z
  have hv := Real.sqrt_pos.mpr (CepsCanonDomain.v_pos hW hθ hD)
  have hsmall : dom.entranceBridgeDecayRate * (|lam| + Real.sqrt ‖z‖) ≤
      ‖cepsScaledRootCoordinate D θ ρW lam z b‖ / (32 * Real.sqrt v) := by
    calc
      _ = ((|lam| + Real.sqrt ‖z‖) / Real.sqrt (8 * v + 8)) / (32 * Real.sqrt v) := by
        unfold CepsCanonDomain.entranceBridgeDecayRate
        ring
      _ ≤ _ := div_le_div_of_nonneg_right (hτ.trans ht) (by positivity)
  have hd₁ : dom.entranceBridgeDecayRate * (|lam| + Real.sqrt ‖z‖) ≤ p - t := by
    exact hsmall.trans (by simpa only [sub_mul, sub_re] using hdirs.1)
  have hd₂ : dom.entranceBridgeDecayRate * (|lam| + Real.sqrt ‖z‖) ≤ p - 2 * m + t := by
    have he : (2 * cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + b * lam)).re = 2 * m := by
      rw [mul_assoc]
      exact re_ofReal_mul 2 _
    have hd := hdirs.2
    rw [add_mul, sub_mul, add_re, sub_re, he] at hd
    exact hsmall.trans hd
  have hdec := weighted_square_decay hd₁ hd₂
  have hH' : ‖cepsScaledSurrogateEntrance dom ρW N lam z b‖ ≤
      dom.surrogateEntrancePolynomialConstant N M * X * (2 + Real.exp (m - t)) := by
    simpa only [sub_mul, sub_re] using hH
  have hHpos : 0 ≤ dom.surrogateEntrancePolynomialConstant N M * X :=
    mul_nonneg (surrogateEntrancePolynomialConstant_pos dom hW hθ hD N M).le (by dsimp [X]; positivity)
  have hUpos : 0 ≤ dom.surrogateBridgeWeightedConstant N M * X := by
    unfold CepsCanonDomain.surrogateBridgeWeightedConstant
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (surrogateSlopePolynomialConstant_pos dom hW hθ hD N M).le)
      (by dsimp [X]; positivity)
  unfold cepsScaledSurrogateEntranceBridge
  rw [norm_mul, norm_mul, norm_exp, norm_pow]
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hH' 2
  apply (mul_le_mul (mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le) hU
    (norm_nonneg _) (by positivity)).trans
  have hh := mul_le_mul_of_nonneg_left hdec (mul_nonneg (sq_nonneg (dom.surrogateEntrancePolynomialConstant N M * X)) hUpos)
  unfold CepsCanonDomain.entranceBridgePolynomialConstant
  convert! hh using 1 <;> dsimp only [X, p, m, t] <;> ring

end PGM
