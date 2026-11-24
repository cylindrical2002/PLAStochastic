import PLAStochastic.Index.CEPS.Scaled.RootBounds
import PLAStochastic.Index.CEPS.Normal.ActualRootSector

/-! # Coercivity of the actual Morse parameter for real drift

The minimum is compared quantitatively with the squared drift. Together
with the square-root modulus this provides the drift and frequency scales
used in the scaled root sector. Only nonnegative real discount is used.
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
open scoped ComplexConjugate
namespace PGM

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
/-- The defining inverse equation gives a class lower scale for the center. -/
theorem cepsMorseCenter_drift_le {μ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) :
    ‖μ‖ ≤ (3 * v / 2) * ‖cepsMorseCenter D θ ρW μ‖ := by
  have hμc := dom.μ_lt_chart hμ
  have hb := norm_cepsMorseCenter_lt hW hθ hD hμc
  have hbmem : cepsMorseCenter D θ ρW μ ∈ ball (0 : ℂ) (cepsCenterRadius D θ) :=
    mem_ball_zero_iff.mpr (hb.trans_le (cepsChartRadius_le_center hD hθ))
  have h := (cepsCenter_hyp hW hθ hD).norm_apply_sub_le (p := (0 : ℂ))
    (mem_univ _) (mem_ball_self (cepsCenterRadius_pos hD hθ)) hbmem
  rw [deriv_cepsCgf_zero hW hθ hD, deriv_cepsCgf_cepsMorseCenter hW hθ hD hμc,
    zero_sub, neg_neg, zero_sub, norm_neg, norm_real, Real.norm_eq_abs,
    abs_of_pos (cepsStepVar_pos hW hθ hD)] at h
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith [cepsStepVar_le hW]) (norm_nonneg _))

include hW hθ hD in
/-- Real drift makes the quadratic minimum strictly coercive in the center scale. -/
theorem cepsMorseMin_center_lower {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) :
    cepsVarLo D / 4 * ‖cepsMorseCenter D θ ρW μ‖ ^ 2 ≤
      -(cepsMorseMin D θ ρW μ).re := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hμc := dom.μ_lt_chart hμ'
  let b := cepsMorseCenter D θ ρW (μ : ℂ)
  let k := cepsMorseK ρW b (-b)
  have hb := norm_cepsMorseCenter_lt hW hθ hD hμc
  have hbre : (b.re : ℂ) = b := conj_eq_iff_re.mp (conj_cepsMorseCenter hW hθ hD hμc)
  have hnear := cepsMorseK_near hW hθ hD hb (u := -b) (by
    rw [norm_neg]; linarith [cepsChartRadius_pos hD hθ])
  have hreal : (cepsStepVar ρW : ℂ) / 2 = ((cepsStepVar ρW / 2 : ℝ) : ℂ) := by
    push_cast; rfl
  rw [hreal] at hnear
  have hkre := (abs_re_le_norm _).trans hnear
  rw [sub_re, ofReal_re] at hkre
  have hk : cepsVarLo D / 4 ≤ k.re := by
    have := neg_le_abs ((cepsMorseK ρW b (-b)).re - cepsStepVar ρW / 2)
    linarith [cepsVarLo_le hW hθ hD, cepsVarLo_pos hD]
  have he := cepsCgfShift_center_add hW hθ hD hμc (u := -b) (by
    rw [norm_neg]; have := cepsChartRadius_le_r0 (D := D) (θ := θ)
    have := cepsCgfRadius_pos hD hθ; linarith)
  have he' : cepsMorseMin D θ ρW μ = -(b ^ 2 * k) := by
    rw [add_neg_cancel, cepsCgfShift, cepsCgf_zero hW, mul_zero, add_zero, neg_sq] at he
    linear_combination -he
  have hb2 : b ^ 2 = ((b.re ^ 2 : ℝ) : ℂ) := by
    conv_lhs => rw [← hbre]
    rw [← ofReal_pow]
  have hbn : ‖b‖ ^ 2 = b.re ^ 2 := by rw [← hbre, norm_real, Real.norm_eq_abs, sq_abs, ofReal_re]
  rw [he', neg_re, neg_neg, hb2, re_ofReal_mul]
  change cepsVarLo D / 4 * ‖b‖ ^ 2 ≤ b.re ^ 2 * k.re
  rw [hbn]
  nlinarith [mul_nonneg (sub_nonneg.mpr hk) (sq_nonneg b.re)]

include hW hθ hD in
/-- The Morse parameter controls drift even at zero discount. -/
theorem cepsRootR_norm_ge_drift {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q : ℂ} (hre : 0 ≤ q.re) :
    Real.sqrt (cepsVarLo D) / (3 * v) * |μ| ≤ ‖cepsRootR D θ ρW μ q‖ := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hcenter := cepsMorseCenter_drift_le dom hW hθ hD hμ'
  rw [norm_real, Real.norm_eq_abs] at hcenter
  have hmin := cepsMorseMin_center_lower dom hW hθ hD hμ
  have hr := re_le_norm (q - cepsMorseMin D θ ρW μ)
  rw [sub_re, ← norm_cepsRootR_sq] at hr
  have h2 := pow_le_pow_left₀ (abs_nonneg μ) hcenter 2
  have h3 := mul_le_mul_of_nonneg_left h2 (cepsVarLo_pos hD).le
  have h4 := mul_le_mul_of_nonneg_left
    (hmin.trans (by linarith : -(cepsMorseMin D θ ρW μ).re ≤ ‖cepsRootR D θ ρW μ q‖ ^ 2))
    (sq_nonneg (3 * v))
  have hs2 := Real.sq_sqrt (cepsVarLo_pos hD).le
  have hsq : (Real.sqrt (cepsVarLo D) * |μ|) ^ 2 ≤
      (3 * v * ‖cepsRootR D θ ρW μ q‖) ^ 2 := by nlinarith
  have hlin := (pow_le_pow_iff_left₀ (by positivity)
    (mul_nonneg (by linarith [CepsCanonDomain.v_pos hW hθ hD]) (norm_nonneg _))
    (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
  calc
    _ = (Real.sqrt (cepsVarLo D) * |μ|) / (3 * v) := by ring
    _ ≤ _ := (div_le_iff₀ (by linarith [CepsCanonDomain.v_pos hW hθ hD])).mpr (by nlinarith)

include hW hθ hD in
/-- Nonnegative real discount cannot shrink the modulus by subtracting the minimum. -/
theorem cepsRootR_norm_ge_discount {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q : ℂ} (hre : 0 ≤ q.re) : Real.sqrt ‖q‖ ≤ ‖cepsRootR D θ ρW μ q‖ := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hμc := dom.μ_lt_chart hμ'
  let m := cepsMorseMin D θ ρW (μ : ℂ)
  have hmi : m.im = 0 := by
    have hreal : (m.re : ℂ) = m := conj_eq_iff_re.mp (conj_cepsMorseMin hW hθ hD hμc)
    rw [← hreal, ofReal_im]
  have hm := re_cepsMorseMin_nonpos hW hθ hD hμc
  have hsq : ‖q‖ ^ 2 ≤ ‖q - m‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, sub_re, sub_im, hmi, sub_zero]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hre hm, sq_nonneg m.re]
  have hn := (pow_le_pow_iff_left₀ (norm_nonneg q) (norm_nonneg (q - m))
    (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
  rw [← norm_cepsRootR_sq D θ ρW μ q] at hn
  have hs2 := Real.sq_sqrt (norm_nonneg q)
  nlinarith [Real.sqrt_nonneg ‖q‖, norm_nonneg (cepsRootR D θ ρW μ q)]

end PGM
