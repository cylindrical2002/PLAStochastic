import PLAStochastic.Index.CEPS.Scaled.KernelFrequencyDifferential

/-! # Actual-minus-surrogate value error of the positive-tail correction -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrueBridgeCorrection_error_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z))
    (hbN : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    ‖cepsScaledTrueBridgeCorrection dom ρW lam z b -
      cepsScaledSurrogateBridgeCorrection dom ρW N lam z b‖ ≤
        (3 * dom.kernelFrequencyConstant N M ^ 3) * (1 + |lam| + Real.sqrt ‖z‖) *
          Real.exp (((cepsScaledSignedRoot D θ ρW lam z (-1) b -
            2 * cepsScaledSignedRoot D θ ρW lam z 1 b) * (1 + (b : ℂ) * lam)).re) *
              |b * lam| ^ (N + 1) := by
  by_cases hl : lam = 0
  · subst lam
    rw [cepsScaledTrueBridgeCorrection_eq_surrogate_of_drift_zero dom N 0 z (by simp)]
    simp
  let A := cepsScaledTrueG dom ρW lam z b (cepsScaledSignedRoot D θ ρW lam z 1 b)
  let a := cepsScaledSurrogateG dom ρW N lam z b (cepsScaledSignedRoot D θ ρW lam z 1 b)
  let I := (cepsScaledTrueDenominator dom ρW lam z b)⁻¹
  let J := (cepsScaledSurrogateDenominator dom ρW N lam z b)⁻¹
  let K := dom.kernelFrequencyConstant N M
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let w : ℂ := 1 + (b : ℂ) * lam
  let P := Real.exp (-(cepsScaledSignedRoot D θ ρW lam z 1 b * w).re)
  let T := Real.exp ((cepsScaledSignedRoot D θ ρW lam z (-1) b * w).re)
  let e := |b * lam| ^ (N + 1)
  obtain ⟨hAv, hav, hAe, _⟩ := cepsScaledRoot_frequency_profile dom hW hθ hD hf hη hM N hN lam hl hz hb hbs
    (Or.inl rfl : (1 : ℂ) = 1 ∨ (1 : ℂ) = -1)
  obtain ⟨_, _, hIv, hIe, _⟩ := cepsScaledInverse_frequency_profile dom hW hθ hD hf hη hM N hN lam hl hz hb hbs hbN
  have h1 : ‖(A - a) * A * I‖ ≤ K ^ 3 * X * P * P * T * e := by
    have ht := cepsNorm_three_product_mul_le (by norm_num : (0 : ℝ) ≤ 1)
      (by simpa only [mul_one] using hAe) hAv hIv
    simp only [mul_one] at ht
    exact ht.trans_eq (by ring)
  have h2 : ‖a * (A - a) * I‖ ≤ K ^ 3 * X * P * P * T * e := by
    rw [mul_comm a (A - a)]
    have ht := cepsNorm_three_product_mul_le (by norm_num : (0 : ℝ) ≤ 1)
      (by simpa only [mul_one] using hAe) hav hIv
    simp only [mul_one] at ht
    exact ht.trans_eq (by ring)
  have h3 : ‖a * a * (I - J)‖ ≤ K ^ 3 * X * P * P * T * e := by
    rw [mul_comm (a * a) (I - J), ← mul_assoc]
    have ht := cepsNorm_three_product_mul_le (by norm_num : (0 : ℝ) ≤ 1)
      (by simpa only [mul_one] using hIe) hav hav
    simp only [mul_one] at ht
    exact ht.trans_eq (by ring)
  have h : ‖A * A * I - a * a * J‖ ≤ 3 * K ^ 3 * X * P * P * T * e :=
    ((cepsNorm_three_factor_error_le A A I a a J).trans (add_le_add (add_le_add h1 h2) h3)).trans_eq (by ring)
  have hbD := ball_subset_ball (truePairScaleRadius_le dom M lam z)
    (ball_subset_ball (trueFrequencyScaleRadius_le dom M lam z) hbs)
  have hS0 := cepsScaledTrueDenominator_ne_zero dom hW hθ hD hf hη hM (by omega) lam hz hbD
  have hT0 := cepsScaledSurrogateDenominator_ne_zero dom hW hθ hD hf hη hM N (by omega) lam hz
    (ball_subset_ball (min_le_left _ _) hbN)
  rw [cepsScaledTrueBridgeCorrection_eq_square_of_nonzero dom ρW lam z b hS0,
    cepsScaledSurrogateBridgeCorrection_eq_square_of_nonzero dom ρW N lam z b hT0]
  change ‖-A ^ 2 / _ - -a ^ 2 / _‖ ≤ _
  simp only [div_eq_mul_inv, pow_two, neg_mul]
  change ‖-(A * A * I) - -(a * a * J)‖ ≤ _
  rw [show -(A * A * I) - -(a * a * J) = -(A * A * I - a * a * J) by ring, norm_neg]
  have hPT : P * P * T = Real.exp (((cepsScaledSignedRoot D θ ρW lam z (-1) b -
      2 * cepsScaledSignedRoot D θ ρW lam z 1 b) * w).re) := by
    dsimp only [P, T]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    simp only [sub_mul, sub_re, mul_re, mul_im, re_ofNat, im_ofNat, zero_mul, sub_zero]
    ring
  apply h.trans_eq
  calc
    _ = 3 * K ^ 3 * X * (P * P * T) * e := by ring
    _ = _ := by rw [hPT]

end PGM
