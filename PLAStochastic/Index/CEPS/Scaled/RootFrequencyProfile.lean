import PLAStochastic.Index.CEPS.Scaled.KernelFrequencyConstants

/-! # The actual and surrogate moving-root frequency profiles -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledRoot_frequency_profile {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    (lam : ℝ) (hlam : lam ≠ 0) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z))
    {sign : ℂ} (hsign : sign = 1 ∨ sign = -1) :
    let A : ℂ → ℂ := fun ζ => cepsScaledTrueG dom ρW lam ζ b (cepsScaledSignedRoot D θ ρW lam ζ sign b)
    let B : ℂ → ℂ := fun ζ => cepsScaledSurrogateG dom ρW N lam ζ b (cepsScaledSignedRoot D θ ρW lam ζ sign b)
    let K := dom.kernelFrequencyConstant N M
    let X := 1 + |lam| + Real.sqrt ‖z‖
    let E := Real.exp (-(cepsScaledSignedRoot D θ ρW lam z sign b * (1 + (b : ℂ) * lam)).re)
    let e := |b * lam| ^ (N + 1)
    ‖A z‖ ≤ K * E ∧ ‖B z‖ ≤ K * E ∧ ‖A z - B z‖ ≤ K * E * e ∧
      ‖deriv A z‖ * |lam| ^ 2 ≤ K * X ^ 2 * E ∧
      ‖deriv B z‖ * |lam| ^ 2 ≤ K * X ^ 2 * E ∧
      ‖deriv A z - deriv B z‖ * |lam| ^ 2 ≤ K * X ^ 2 * E * e := by
  dsimp only
  let K := dom.kernelFrequencyConstant N M
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let E := Real.exp (-(cepsScaledSignedRoot D θ ρW lam z sign b * (1 + (b : ℂ) * lam)).re)
  let e := |b * lam| ^ (N + 1)
  have hK : 0 ≤ K := (kernelFrequencyConstant_pos dom N M).le
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have he : 0 ≤ e := by dsimp only [e]; positivity
  have hLX : |lam| ≤ X := by dsimp only [X]; linarith [Real.sqrt_nonneg ‖z‖]
  have h1LX : 1 + |lam| ≤ X := by dsimp only [X]; linarith [Real.sqrt_nonneg ‖z‖]
  have hbound : ∀ c ∈ dom.kernelFrequencyConstants N M, c ≤ K := fun c hc => kernelFrequencyConstant_le dom N M hc
  obtain ⟨hAv, hBv, hEv⟩ := cepsScaledG_root_frequency_value_budgets dom hW hθ hD hf hη hM N hN lam hz hb hbs hsign
  have hAd := cepsScaledTrueG_root_frequency_deriv_budget dom hW hθ hD hf (by omega) hη M lam hz (Or.inl hlam) hb hbs hsign
  have hBd := cepsScaledSurrogateG_root_frequency_deriv_budget dom hW hθ hD hf hη hM N (by omega) lam hz (Or.inl hlam) hb hbs hsign
  have hEd := cepsScaledRootEvaluation_frequency_deriv_error_budget dom hW hθ hD hf hη hM N hN lam hz hb hbs hsign
  obtain ⟨hA, hB⟩ := cepsScaledG_root_frequency_differentiableAt dom hW hθ hD hf hη N (by omega) M lam hz (Or.inl hlam) hb hbs hsign
  have hdiff : deriv (fun ζ => cepsScaledTrueG dom ρW lam ζ b (cepsScaledSignedRoot D θ ρW lam ζ sign b) -
      cepsScaledSurrogateG dom ρW N lam ζ b (cepsScaledSignedRoot D θ ρW lam ζ sign b)) z =
      deriv (fun ζ => cepsScaledTrueG dom ρW lam ζ b (cepsScaledSignedRoot D θ ρW lam ζ sign b)) z -
        deriv (fun ζ => cepsScaledSurrogateG dom ρW N lam ζ b (cepsScaledSignedRoot D θ ρW lam ζ sign b)) z := by
    simpa only [Pi.sub_def] using deriv_sub hA hB
  rw [hdiff] at hEd
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hAv.trans (mul_le_mul_of_nonneg_right
      (hbound _ (by simp [CepsCanonDomain.kernelFrequencyConstants])) hE)
  · exact hBv.trans (mul_le_mul_of_nonneg_right
      (hbound _ (by simp [CepsCanonDomain.kernelFrequencyConstants])) hE)
  · exact hEv.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (hbound _ (by simp [CepsCanonDomain.kernelFrequencyConstants])) hE) he)
  · have hlin := hAd.trans_eq (show _ = ((v * Real.exp (2 * dom.normalLogBound)) *
      dom.rootFrequencyChainConstant) * (1 + |lam|) * E * (1 : ℝ) by ring)
    simpa only [mul_one] using cepsDrift_square_weight_of_linear_weight (abs_nonneg lam) hK hE (by norm_num)
      (hbound _ (by simp [CepsCanonDomain.kernelFrequencyConstants])) hLX h1LX hlin
  · have hlin := hBd.trans_eq (show _ = ((v * Real.exp (2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8))) *
      dom.rootFrequencyChainConstant) * (1 + |lam|) * E * (1 : ℝ) by ring)
    simpa only [mul_one] using cepsDrift_square_weight_of_linear_weight (abs_nonneg lam) hK hE (by norm_num)
      (hbound _ (by simp [CepsCanonDomain.kernelFrequencyConstants])) hLX h1LX hlin
  · exact cepsDrift_square_weight_of_linear_weight (abs_nonneg lam) hK hE he
      (hbound _ (by simp [CepsCanonDomain.kernelFrequencyConstants])) hLX h1LX hEd

end PGM
