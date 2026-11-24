import PLAStochastic.Index.CEPS.Scaled.CorrectionFrequencyError
import PLAStochastic.Index.CEPS.Scaled.DriftPowerCancellation

/-! # Frequency errors without inverse drift or scale powers -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

theorem cepsScaledTrueBridgeCorrection_eq_surrogate_of_drift_zero
    (N : ℕ) (lam : ℝ) (z : ℂ) {b : ℝ} (hμ : b * lam = 0) :
    cepsScaledTrueBridgeCorrection dom ρW lam z b =
      cepsScaledSurrogateBridgeCorrection dom ρW N lam z b := by
  unfold cepsScaledTrueBridgeCorrection cepsScaledSurrogateBridgeCorrection
    cepsScaledTrueHalfBridge cepsScaledSurrogateHalfBridge
  rw [cepsScaledTrueBridge_eq_surrogate_of_drift_zero dom ρW N lam z hμ,
    cepsScaledTrueG_eq_surrogate_of_drift_zero dom ρW N lam z hμ]

include hW hθ hD in
theorem cepsScaledTrueBridge_frequency_taylor_error_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 3 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z))
    (hbN : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius (N + 1) M lam z)) :
    ‖deriv (fun ζ => cepsScaledTrueBridge dom ρW lam ζ b -
      cepsScaledSurrogateBridge dom ρW (N + 1) lam ζ b) z‖ ≤
        (9 * dom.kernelFrequencyConstant (N + 1) M ^ 3) * b ^ (N + 2) *
          (1 + |lam| + Real.sqrt ‖z‖) ^ (N + 3) *
            Real.exp (-(cepsScaledSignedRoot D θ ρW lam z 1 b * (1 + (b : ℂ) * lam)).re) := by
  have hK := (kernelFrequencyConstant_pos dom (N + 1) M).le
  by_cases hl : lam = 0
  · subst lam
    have heq : (fun ζ => cepsScaledTrueBridge dom ρW 0 ζ b -
        cepsScaledSurrogateBridge dom ρW (N + 1) 0 ζ b) = 0 := by
      funext ζ
      rw [cepsScaledTrueBridge_eq_surrogate_of_drift_zero dom ρW (N + 1) 0 ζ (by simp)]
      simp
    rw [heq]
    change ‖deriv (fun _ : ℂ => (0 : ℂ)) z‖ ≤ _
    rw [deriv_const, norm_zero]
    positivity
  apply cepsDrift_square_weight_cancel_taylor N hb hl (by positivity) (Real.exp_pos _).le
    (by linarith [Real.sqrt_nonneg ‖z‖])
  simpa only [Nat.add_assoc] using cepsScaledTrueBridge_frequency_deriv_error_budget
    dom hW hθ hD hf hη hM (N + 1) (by omega) lam hz hb hbs hbN

include hW hθ hD in
theorem cepsScaledTrueBridgeCorrection_frequency_taylor_error_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 3 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z))
    (hbN : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius (N + 1) M lam z)) :
    ‖deriv (fun ζ => cepsScaledTrueBridgeCorrection dom ρW lam ζ b -
      cepsScaledSurrogateBridgeCorrection dom ρW (N + 1) lam ζ b) z‖ ≤
        (9 * dom.kernelFrequencyConstant (N + 1) M ^ 3) * b ^ (N + 2) *
          (1 + |lam| + Real.sqrt ‖z‖) ^ (N + 3) *
            Real.exp (((cepsScaledSignedRoot D θ ρW lam z (-1) b -
              2 * cepsScaledSignedRoot D θ ρW lam z 1 b) * (1 + (b : ℂ) * lam)).re) := by
  have hK := (kernelFrequencyConstant_pos dom (N + 1) M).le
  by_cases hl : lam = 0
  · subst lam
    have heq : (fun ζ => cepsScaledTrueBridgeCorrection dom ρW 0 ζ b -
        cepsScaledSurrogateBridgeCorrection dom ρW (N + 1) 0 ζ b) = 0 := by
      funext ζ
      rw [cepsScaledTrueBridgeCorrection_eq_surrogate_of_drift_zero dom (N + 1) 0 ζ (by simp)]
      simp
    rw [heq]
    change ‖deriv (fun _ : ℂ => (0 : ℂ)) z‖ ≤ _
    rw [deriv_const, norm_zero]
    positivity
  apply cepsDrift_square_weight_cancel_taylor N hb hl (by positivity) (Real.exp_pos _).le
    (by linarith [Real.sqrt_nonneg ‖z‖])
  simpa only [Nat.add_assoc] using cepsScaledTrueBridgeCorrection_frequency_deriv_error_budget
    dom hW hθ hD hf hη hM (N + 1) (by omega) lam hz hb hbs hbN

end PGM
