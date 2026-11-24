import PLAStochastic.Index.CEPS.Scaled.BridgeFrequencyTaylorError

/-! # Differentiating actual-minus-surrogate bridge differences -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledBridges_frequency_differentiableAt {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    (lam : ℝ) (hl : lam ≠ 0) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z))
    (hbN : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    DifferentiableAt ℂ (fun ζ => cepsScaledTrueBridge dom ρW lam ζ b) z ∧
    DifferentiableAt ℂ (fun ζ => cepsScaledSurrogateBridge dom ρW N lam ζ b) z ∧
    DifferentiableAt ℂ (fun ζ => cepsScaledTrueBridgeCorrection dom ρW lam ζ b) z ∧
    DifferentiableAt ℂ (fun ζ => cepsScaledSurrogateBridgeCorrection dom ρW N lam ζ b) z := by
  obtain ⟨hA, ha⟩ := cepsScaledG_root_frequency_differentiableAt dom hW hθ hD hf hη N (by omega) M lam hz
    (Or.inl hl) hb hbs (Or.inl rfl : (1 : ℂ) = 1 ∨ (1 : ℂ) = -1)
  obtain ⟨hB, hc⟩ := cepsScaledG_root_frequency_differentiableAt dom hW hθ hD hf hη N (by omega) M lam hz
    (Or.inl hl) hb hbs (Or.inr rfl : (-1 : ℂ) = 1 ∨ (-1 : ℂ) = -1)
  obtain ⟨hI, hJ, _⟩ := cepsScaledInverse_frequency_profile dom hW hθ hD hf hη hM N hN lam hl hz hb hbs hbN
  have hT : DifferentiableAt ℂ (fun ζ => cepsScaledTrueBridge dom ρW lam ζ b) z :=
    (hA.neg.mul hB).mul hI
  have hS : DifferentiableAt ℂ (fun ζ => cepsScaledSurrogateBridge dom ρW N lam ζ b) z :=
    (ha.neg.mul hc).mul hJ
  have hp := (cepsScaledSignedRoot_frequency_hasDerivAt dom hW hθ hD M lam hz (Or.inl hl) hb hbs
    (by norm_num : ‖(1 : ℂ)‖ ≤ 1)).differentiableAt
  have hm := (cepsScaledSignedRoot_frequency_hasDerivAt dom hW hθ hD M lam hz (Or.inl hl) hb hbs
    (by norm_num : ‖(-1 : ℂ)‖ ≤ 1)).differentiableAt
  exact ⟨hT, hS, hT.sub ((hp.sub hm).mul hA), hS.sub ((hp.sub hm).mul ha)⟩

include hW hθ hD in
theorem cepsScaledBridge_error_deriv_eq {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z))
    (hbN : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    deriv (fun ζ => cepsScaledTrueBridge dom ρW lam ζ b - cepsScaledSurrogateBridge dom ρW N lam ζ b) z =
      deriv (fun ζ => cepsScaledTrueBridge dom ρW lam ζ b) z -
        deriv (fun ζ => cepsScaledSurrogateBridge dom ρW N lam ζ b) z := by
  by_cases hl : lam = 0
  · subst lam
    have heq : (fun ζ => cepsScaledTrueBridge dom ρW 0 ζ b) =
        (fun ζ => cepsScaledSurrogateBridge dom ρW N 0 ζ b) := by
      funext ζ
      exact cepsScaledTrueBridge_eq_surrogate_of_drift_zero dom ρW N 0 ζ (by simp)
    change deriv ((fun ζ => cepsScaledTrueBridge dom ρW 0 ζ b) -
      (fun ζ => cepsScaledSurrogateBridge dom ρW N 0 ζ b)) z = _
    rw [heq, sub_self, deriv_zero, Pi.zero_apply, sub_self]
  obtain ⟨hT, hS, _⟩ := cepsScaledBridges_frequency_differentiableAt dom hW hθ hD hf hη hM N hN lam hl hz hb hbs hbN
  exact deriv_sub hT hS

include hW hθ hD in
theorem cepsScaledBridgeCorrection_error_deriv_eq {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z))
    (hbN : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    deriv (fun ζ => cepsScaledTrueBridgeCorrection dom ρW lam ζ b -
      cepsScaledSurrogateBridgeCorrection dom ρW N lam ζ b) z =
        deriv (fun ζ => cepsScaledTrueBridgeCorrection dom ρW lam ζ b) z -
          deriv (fun ζ => cepsScaledSurrogateBridgeCorrection dom ρW N lam ζ b) z := by
  by_cases hl : lam = 0
  · subst lam
    have heq : (fun ζ => cepsScaledTrueBridgeCorrection dom ρW 0 ζ b) =
        (fun ζ => cepsScaledSurrogateBridgeCorrection dom ρW N 0 ζ b) := by
      funext ζ
      exact cepsScaledTrueBridgeCorrection_eq_surrogate_of_drift_zero dom N 0 ζ (by simp)
    change deriv ((fun ζ => cepsScaledTrueBridgeCorrection dom ρW 0 ζ b) -
      (fun ζ => cepsScaledSurrogateBridgeCorrection dom ρW N 0 ζ b)) z = _
    rw [heq, sub_self, deriv_zero, Pi.zero_apply, sub_self]
  obtain ⟨_, _, hT, hS⟩ := cepsScaledBridges_frequency_differentiableAt dom hW hθ hD hf hη hM N hN lam hl hz hb hbs hbN
  exact deriv_sub hT hS

end PGM
