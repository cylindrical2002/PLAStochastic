import PLAStochastic.Index.CEPS.Scaled.CorrectionValueError
import PLAStochastic.Index.CEPS.Scaled.TruePositiveOperator

/-! # Actual-minus-surrogate errors of the complete time operator -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

theorem cepsNorm_timeOperator_difference_le {lam b : ℝ} {U V : ℂ → ℂ} {z : ℂ}
    {D B K L : ℝ} (hD : ‖deriv U z - deriv V z‖ ≤ D) (hB : ‖U z - V z‖ ≤ B)
    (hK : ‖(1 / (1 + (b : ℂ) * lam) : ℂ)‖ ≤ K) (hL : ‖(b : ℂ)‖ ≤ L) :
    ‖cepsScaledTimeOperator lam b U z - cepsScaledTimeOperator lam b V z‖ ≤ K * D + L * B := by
  have hid : cepsScaledTimeOperator lam b U z - cepsScaledTimeOperator lam b V z =
      -(1 / (1 + (b : ℂ) * lam)) * (deriv U z - deriv V z) - (b : ℂ) * (U z - V z) := by
    unfold cepsScaledTimeOperator
    ring
  rw [hid]
  apply (norm_sub_le _ _).trans
  rw [norm_mul, norm_neg, norm_mul]
  exact add_le_add (mul_le_mul hK hD (norm_nonneg _) ((norm_nonneg _).trans hK))
    (mul_le_mul hL hB (norm_nonneg _) ((norm_nonneg _).trans hL))

def CepsCanonDomain.bridgeTimeErrorConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  18 * dom.kernelFrequencyConstant N M ^ 3 + |dom.trueBridgeErrorConstant N M|

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrueBridge_timeOperator_error_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 3 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z))
    (hbN : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius (N + 1) M lam z)) :
    ‖cepsScaledTimeOperator lam b (fun ζ => cepsScaledTrueBridge dom ρW lam ζ b) z -
      cepsScaledTimeOperator lam b (fun ζ => cepsScaledSurrogateBridge dom ρW (N + 1) lam ζ b) z‖ ≤
        dom.bridgeTimeErrorConstant (N + 1) M * b ^ (N + 2) *
          (1 + |lam| + Real.sqrt ‖z‖) ^ (N + 3) *
            Real.exp (-(cepsScaledSignedRoot D θ ρW lam z 1 b * (1 + (b : ℂ) * lam)).re) := by
  have hK := (kernelFrequencyConstant_pos dom (N + 1) M).le
  have hDerr := cepsScaledTrueBridge_frequency_taylor_error_budget dom hW hθ hD hf hη hM N hN lam hz hb hbs hbN
  rw [cepsScaledBridge_error_deriv_eq dom hW hθ hD hf hη hM (N + 1) (by omega) lam hz hb hbs hbN] at hDerr
  have hbD := ball_subset_ball (truePairScaleRadius_le dom M lam z)
    (ball_subset_ball (trueFrequencyScaleRadius_le dom M lam z) hbs)
  have hV := cepsScaledTrueBridge_error_budget dom hW hθ hD hf hη hM (N + 1) (by omega) lam hz hbD hbN
  have hVabs := hV.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
      (Real.exp_pos _).le) (pow_nonneg (abs_nonneg _) _))
  have hVB := cepsDrift_taylor_value_budget (N + 2) hb.le (abs_nonneg _) (Real.exp_pos _).le
    (by linarith [Real.sqrt_nonneg ‖z‖]) hVabs
  obtain ⟨hb1, hw1⟩ := cepsScaledTrueFrequency_scale_width_budget dom hW hθ hD M lam hz hb hbs
  have h := cepsNorm_timeOperator_difference_le hDerr hVB hw1 hb1
  exact h.trans_eq (by unfold CepsCanonDomain.bridgeTimeErrorConstant; ring)

include hW hθ hD in
theorem cepsScaledTrueBridgeCorrection_timeOperator_error_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 3 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z))
    (hbN : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius (N + 1) M lam z)) :
    ‖cepsScaledTimeOperator lam b (fun ζ => cepsScaledTrueBridgeCorrection dom ρW lam ζ b) z -
      cepsScaledTimeOperator lam b (fun ζ => cepsScaledSurrogateBridgeCorrection dom ρW (N + 1) lam ζ b) z‖ ≤
        (21 * dom.kernelFrequencyConstant (N + 1) M ^ 3) * b ^ (N + 2) *
          (1 + |lam| + Real.sqrt ‖z‖) ^ (N + 3) *
            Real.exp (((cepsScaledSignedRoot D θ ρW lam z (-1) b -
              2 * cepsScaledSignedRoot D θ ρW lam z 1 b) * (1 + (b : ℂ) * lam)).re) := by
  have hK := (kernelFrequencyConstant_pos dom (N + 1) M).le
  have hDerr := cepsScaledTrueBridgeCorrection_frequency_taylor_error_budget dom hW hθ hD hf hη hM N hN lam hz hb hbs hbN
  rw [cepsScaledBridgeCorrection_error_deriv_eq dom hW hθ hD hf hη hM (N + 1) (by omega) lam hz hb hbs hbN] at hDerr
  have hV := cepsScaledTrueBridgeCorrection_error_budget dom hW hθ hD hf hη hM (N + 1) (by omega) lam hz hb hbs hbN
  have hVB := cepsDrift_taylor_value_budget (N + 2) hb.le (by positivity) (Real.exp_pos _).le
    (by linarith [Real.sqrt_nonneg ‖z‖]) hV
  obtain ⟨hb1, hw1⟩ := cepsScaledTrueFrequency_scale_width_budget dom hW hθ hD M lam hz hb hbs
  have h := cepsNorm_timeOperator_difference_le hDerr hVB hw1 hb1
  exact h.trans_eq (by ring)

end PGM
