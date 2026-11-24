import PLAStochastic.Index.CEPS.Scaled.RootFrequencyProfile
import PLAStochastic.Index.CEPS.Scaled.InverseFrequencyProfile

/-! # Actual versus surrogate frequency derivative error of the complete bridge -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrueBridge_frequency_deriv_error_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z))
    (hbN : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    ‖deriv (fun ζ => cepsScaledTrueBridge dom ρW lam ζ b -
      cepsScaledSurrogateBridge dom ρW N lam ζ b) z‖ * |lam| ^ 2 ≤
        (9 * dom.kernelFrequencyConstant N M ^ 3) * (1 + |lam| + Real.sqrt ‖z‖) ^ 3 *
          Real.exp (-(cepsScaledSignedRoot D θ ρW lam z 1 b * (1 + (b : ℂ) * lam)).re) *
            |b * lam| ^ (N + 1) := by
  by_cases hl : lam = 0
  · subst lam
    simp
  let A : ℂ → ℂ := fun ζ => cepsScaledTrueG dom ρW lam ζ b (cepsScaledSignedRoot D θ ρW lam ζ 1 b)
  let B : ℂ → ℂ := fun ζ => cepsScaledTrueG dom ρW lam ζ b (cepsScaledSignedRoot D θ ρW lam ζ (-1) b)
  let a : ℂ → ℂ := fun ζ => cepsScaledSurrogateG dom ρW N lam ζ b (cepsScaledSignedRoot D θ ρW lam ζ 1 b)
  let c : ℂ → ℂ := fun ζ => cepsScaledSurrogateG dom ρW N lam ζ b (cepsScaledSignedRoot D θ ρW lam ζ (-1) b)
  let I : ℂ → ℂ := fun ζ => (cepsScaledTrueDenominator dom ρW lam ζ b)⁻¹
  let J : ℂ → ℂ := fun ζ => (cepsScaledSurrogateDenominator dom ρW N lam ζ b)⁻¹
  let K := dom.kernelFrequencyConstant N M
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let w : ℂ := 1 + (b : ℂ) * lam
  let P := Real.exp (-(cepsScaledSignedRoot D θ ρW lam z 1 b * w).re)
  let Q := Real.exp (-(cepsScaledSignedRoot D θ ρW lam z (-1) b * w).re)
  let T := Real.exp ((cepsScaledSignedRoot D θ ρW lam z (-1) b * w).re)
  let e := |b * lam| ^ (N + 1)
  obtain ⟨_, hav, hAe, _, had, hAde⟩ := cepsScaledRoot_frequency_profile dom hW hθ hD hf hη hM N hN lam hl hz hb hbs
    (Or.inl rfl : (1 : ℂ) = 1 ∨ (1 : ℂ) = -1)
  obtain ⟨hBv, hcv, hBe, hBd, hcd, hBde⟩ := cepsScaledRoot_frequency_profile dom hW hθ hD hf hη hM N hN lam hl hz hb hbs
    (Or.inr rfl : (-1 : ℂ) = 1 ∨ (-1 : ℂ) = -1)
  obtain ⟨hI, hJ, hIv, hIe, hId, hIde⟩ := cepsScaledInverse_frequency_profile dom hW hθ hD hf hη hM N hN lam hl hz hb hbs hbN
  obtain ⟨hA, ha⟩ := cepsScaledG_root_frequency_differentiableAt dom hW hθ hD hf hη N (by omega) M lam hz (Or.inl hl) hb hbs
    (Or.inl rfl : (1 : ℂ) = 1 ∨ (1 : ℂ) = -1)
  obtain ⟨hB, hc⟩ := cepsScaledG_root_frequency_differentiableAt dom hW hθ hD hf hη N (by omega) M lam hz (Or.inl hl) hb hbs
    (Or.inr rfl : (-1 : ℂ) = 1 ∨ (-1 : ℂ) = -1)
  let F : ℂ → ℂ := fun ζ => A ζ * B ζ * I ζ - a ζ * c ζ * J ζ
  have h : ‖deriv F z‖ * |lam| ^ 2 ≤ 9 * K ^ 3 * X ^ 3 * P * Q * T * e :=
    cepsNorm_deriv_three_factor_error_common_budget hA hB hI ha hc hJ hBv hIv hav hcv hAe hBe hIe
      hBd hId had hcd hAde hBde hIde
  have heq : (fun ζ => cepsScaledTrueBridge dom ρW lam ζ b - cepsScaledSurrogateBridge dom ρW N lam ζ b) = -F := by
    funext ζ
    unfold cepsScaledTrueBridge cepsScaledSurrogateBridge
    dsimp only [F, A, B, a, c, I, J]
    simp only [div_eq_mul_inv, Pi.neg_apply]
    ring
  rw [heq, deriv.neg, norm_neg]
  have hQT : Q * T = 1 := by
    dsimp only [Q, T]
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  apply h.trans_eq
  calc
    _ = 9 * K ^ 3 * X ^ 3 * P * (Q * T) * e := by ring
    _ = _ := by rw [hQT]; dsimp only [K, X, P, e, w]; ring

end PGM
