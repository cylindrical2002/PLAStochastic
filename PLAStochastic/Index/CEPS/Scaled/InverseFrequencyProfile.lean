import PLAStochastic.Index.CEPS.Scaled.KernelFrequencyConstants

/-! # The actual inverse-denominator frequency profile and its surrogate error -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledInverse_frequency_profile {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    (lam : ℝ) (hlam : lam ≠ 0) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z))
    (hbN : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    let I : ℂ → ℂ := fun ζ => (cepsScaledTrueDenominator dom ρW lam ζ b)⁻¹
    let J : ℂ → ℂ := fun ζ => (cepsScaledSurrogateDenominator dom ρW N lam ζ b)⁻¹
    let K := dom.kernelFrequencyConstant N M
    let X := 1 + |lam| + Real.sqrt ‖z‖
    let E := Real.exp ((cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + (b : ℂ) * lam)).re)
    let e := |b * lam| ^ (N + 1)
    DifferentiableAt ℂ I z ∧ DifferentiableAt ℂ J z ∧
      ‖I z‖ ≤ K * X * E ∧ ‖I z - J z‖ ≤ K * X * E * e ∧
      ‖deriv I z‖ * |lam| ^ 2 ≤ K * X ^ 3 * E ∧
      ‖deriv I z - deriv J z‖ * |lam| ^ 2 ≤ K * X ^ 3 * E * e := by
  dsimp only
  let I : ℂ → ℂ := fun ζ => (cepsScaledTrueDenominator dom ρW lam ζ b)⁻¹
  let J : ℂ → ℂ := fun ζ => (cepsScaledSurrogateDenominator dom ρW N lam ζ b)⁻¹
  let K := dom.kernelFrequencyConstant N M
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let E := Real.exp ((cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + (b : ℂ) * lam)).re)
  let e := |b * lam| ^ (N + 1)
  have hK : 0 ≤ K := (kernelFrequencyConstant_pos dom N M).le
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have h1LX : 1 + |lam| ≤ X := by dsimp [X]; linarith [Real.sqrt_nonneg ‖z‖]
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hbound : ∀ c ∈ dom.kernelFrequencyConstants N M, c ≤ K := fun c hc => kernelFrequencyConstant_le dom N M hc
  have hbD := ball_subset_ball (truePairScaleRadius_le dom M lam z)
    (ball_subset_ball (trueFrequencyScaleRadius_le dom M lam z) hbs)
  obtain ⟨hS, hT⟩ := cepsScaledDenominators_frequency_differentiableAt dom hW hθ hD hf hη N
    (by omega) M lam hlam hz hb hbs
  have hS0 := cepsScaledTrueDenominator_ne_zero dom hW hθ hD hf hη hM (by omega) lam hz hbD
  have hT0 := cepsScaledSurrogateDenominator_ne_zero dom hW hθ hD hf hη hM N (by omega) lam hz
    (ball_subset_ball (min_le_left _ _) hbN)
  have hI : DifferentiableAt ℂ I z := hS.inv hS0
  have hJ : DifferentiableAt ℂ J z := hT.inv hT0
  have hIv := cepsScaledTrueDenominator_inverse_weighted_budget dom hW hθ hD hf hη hM (by omega) lam hz hbD
  have hEv := cepsScaledTrueDenominator_inverse_error_budget dom hW hθ hD hf hη hM N hN lam hz hbD hbN
  have hId := cepsScaledTrueDenominator_inverse_frequency_deriv_budget dom hW hθ hD hf hη hM (by omega) lam hlam hz hb hbs
  have hEd := cepsScaledTrueDenominator_inverse_frequency_deriv_error_budget dom hW hθ hD hf hη hM N hN lam hz hb hbs hbN
  have hdiff : deriv (fun ζ => I ζ - J ζ) z = deriv I z - deriv J z := by
    simpa only [Pi.sub_def] using deriv_sub hI hJ
  change ‖deriv (fun ζ => I ζ - J ζ) z‖ * |lam| ^ 2 ≤ _ at hEd
  rw [hdiff] at hEd
  refine ⟨hI, hJ, ?_, ?_, ?_, ?_⟩
  · exact hIv.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (hbound _ (by simp [CepsCanonDomain.kernelFrequencyConstants])) hX) hE)
  · have hcoeff : 2 * dom.trueDenominatorRelativeConstant N M * dom.surrogateSlopePolynomialConstant 0 M =
        dom.trueDenominatorRelativeConstant N M * (2 * dom.surrogateSlopePolynomialConstant 0 M) := by ring
    rw [hcoeff] at hEv
    exact hEv.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (hbound _ (by simp [CepsCanonDomain.kernelFrequencyConstants])) hX) hE) he)
  · have hC : dom.trueInverseFrequencyConstant M ≤ K := hbound _ (by simp [CepsCanonDomain.kernelFrequencyConstants])
    apply hId.trans
    calc
      _ ≤ K * (1 + |lam|) * X ^ 2 * E := by gcongr
      _ ≤ K * X * X ^ 2 * E := by gcongr
      _ = _ := by ring
  · have hC : dom.inverseFrequencyErrorConstant N M ≤ K := hbound _ (by simp [CepsCanonDomain.kernelFrequencyConstants])
    apply hEd.trans
    calc
      _ ≤ K * (1 + |lam|) * X ^ 2 * E * e := by gcongr
      _ ≤ K * X * X ^ 2 * E * e := by gcongr
      _ = _ := by ring

end PGM
