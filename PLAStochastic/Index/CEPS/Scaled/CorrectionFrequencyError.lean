import PLAStochastic.Index.CEPS.Scaled.BridgeFrequencyError
import PLAStochastic.Index.CEPS.Scaled.BridgeCorrectionAlgebra

/-! # Frequency derivative errors retain the positive-tail bridge cancellation -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrueBridgeCorrection_frequency_deriv_error_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z))
    (hbN : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    ‖deriv (fun ζ => cepsScaledTrueBridgeCorrection dom ρW lam ζ b -
      cepsScaledSurrogateBridgeCorrection dom ρW N lam ζ b) z‖ * |lam| ^ 2 ≤
        (9 * dom.kernelFrequencyConstant N M ^ 3) * (1 + |lam| + Real.sqrt ‖z‖) ^ 3 *
          Real.exp (((cepsScaledSignedRoot D θ ρW lam z (-1) b -
            2 * cepsScaledSignedRoot D θ ρW lam z 1 b) * (1 + (b : ℂ) * lam)).re) *
              |b * lam| ^ (N + 1) := by
  by_cases hl : lam = 0
  · subst lam
    simp
  let A : ℂ → ℂ := fun ζ => cepsScaledTrueG dom ρW lam ζ b (cepsScaledSignedRoot D θ ρW lam ζ 1 b)
  let a : ℂ → ℂ := fun ζ => cepsScaledSurrogateG dom ρW N lam ζ b (cepsScaledSignedRoot D θ ρW lam ζ 1 b)
  let I : ℂ → ℂ := fun ζ => (cepsScaledTrueDenominator dom ρW lam ζ b)⁻¹
  let J : ℂ → ℂ := fun ζ => (cepsScaledSurrogateDenominator dom ρW N lam ζ b)⁻¹
  let K := dom.kernelFrequencyConstant N M
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let w : ℂ := 1 + (b : ℂ) * lam
  let P := Real.exp (-(cepsScaledSignedRoot D θ ρW lam z 1 b * w).re)
  let T := Real.exp ((cepsScaledSignedRoot D θ ρW lam z (-1) b * w).re)
  let e := |b * lam| ^ (N + 1)
  obtain ⟨hAv, hav, hAe, hAd, had, hAde⟩ := cepsScaledRoot_frequency_profile dom hW hθ hD hf hη hM N hN lam hl hz hb hbs
    (Or.inl rfl : (1 : ℂ) = 1 ∨ (1 : ℂ) = -1)
  obtain ⟨hI, hJ, hIv, hIe, hId, hIde⟩ := cepsScaledInverse_frequency_profile dom hW hθ hD hf hη hM N hN lam hl hz hb hbs hbN
  obtain ⟨hA, ha⟩ := cepsScaledG_root_frequency_differentiableAt dom hW hθ hD hf hη N (by omega) M lam hz (Or.inl hl) hb hbs
    (Or.inl rfl : (1 : ℂ) = 1 ∨ (1 : ℂ) = -1)
  let F : ℂ → ℂ := fun ζ => A ζ * A ζ * I ζ - a ζ * a ζ * J ζ
  have h : ‖deriv F z‖ * |lam| ^ 2 ≤ 9 * K ^ 3 * X ^ 3 * P * P * T * e :=
    cepsNorm_deriv_three_factor_error_common_budget hA hA hI ha ha hJ hAv hIv hav hav hAe hAe hIe
      hAd hId had had hAde hAde hIde
  have hbD := ball_subset_ball (truePairScaleRadius_le dom M lam z)
    (ball_subset_ball (trueFrequencyScaleRadius_le dom M lam z) hbs)
  have hS0 := cepsScaledTrueDenominator_ne_zero dom hW hθ hD hf hη hM (by omega) lam hz hbD
  have hT0 := cepsScaledSurrogateDenominator_ne_zero dom hW hθ hD hf hη hM N (by omega) lam hz
    (ball_subset_ball (min_le_left _ _) hbN)
  have hevI := hI.continuousAt.eventually_ne (inv_ne_zero hS0)
  have hevJ := hJ.continuousAt.eventually_ne (inv_ne_zero hT0)
  have heq : (fun ζ => cepsScaledTrueBridgeCorrection dom ρW lam ζ b -
      cepsScaledSurrogateBridgeCorrection dom ρW N lam ζ b) =ᶠ[𝓝 z] -F := by
    filter_upwards [hevI, hevJ] with ζ hζI hζJ
    have hζS := inv_ne_zero hζI
    have hζT := inv_ne_zero hζJ
    simp only [inv_inv] at hζS hζT
    rw [cepsScaledTrueBridgeCorrection_eq_square_of_nonzero dom ρW lam ζ b hζS,
      cepsScaledSurrogateBridgeCorrection_eq_square_of_nonzero dom ρW N lam ζ b hζT]
    dsimp only [F, A, a, I, J]
    simp only [Pi.neg_apply, div_eq_mul_inv, pow_two]
    ring
  rw [heq.deriv_eq, deriv.neg, norm_neg]
  have hPT : P * P * T = Real.exp (((cepsScaledSignedRoot D θ ρW lam z (-1) b -
      2 * cepsScaledSignedRoot D θ ρW lam z 1 b) * w).re) := by
    dsimp only [P, T]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    simp only [sub_mul, sub_re, mul_re, mul_im, re_ofNat, im_ofNat, zero_mul, sub_zero]
    ring
  apply h.trans_eq
  calc
    _ = 9 * K ^ 3 * X ^ 3 * (P * P * T) * e := by ring
    _ = _ := by rw [hPT]

end PGM
