import PLAStochastic.Index.CEPS.Scaled.RootCoercivity

/-! # Drift-dependent directions of the actual roots -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
open scoped ComplexConjugate
namespace PGM

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
/-- The real center has the opposite sign to the drift. -/
theorem cepsMorseCenter_re_sign {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) :
    (0 ≤ μ → (cepsMorseCenter D θ ρW μ).re ≤ 0) ∧
      (μ ≤ 0 → 0 ≤ (cepsMorseCenter D θ ρW μ).re) := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hμc := dom.μ_lt_chart hμ'
  let b := cepsMorseCenter D θ ρW (μ : ℂ)
  let V := cepsStepVar ρW
  have hV : 0 < V := cepsStepVar_pos hW hθ hD
  have hbre : (b.re : ℂ) = b := conj_eq_iff_re.mp (conj_cepsMorseCenter hW hθ hD hμc)
  have hbmem : b ∈ ball (0 : ℂ) (cepsCenterRadius D θ) := mem_ball_zero_iff.mpr
    ((norm_cepsMorseCenter_lt hW hθ hD hμc).trans_le (cepsChartRadius_le_center hD hθ))
  have h := (cepsCenter_hyp hW hθ hD).norm_sub_sub_le (p := (0 : ℂ))
    (mem_univ _) hbmem (mem_ball_self (cepsCenterRadius_pos hD hθ))
  rw [deriv_cepsCgf_cepsMorseCenter hW hθ hD hμc, deriv_cepsCgf_zero hW hθ hD,
    mul_zero, sub_self, sub_zero, sub_zero, norm_real, Real.norm_eq_abs, abs_of_pos hV] at h
  have hn : ‖b‖ = |b.re| := by rw [← hbre, norm_real, Real.norm_eq_abs, ofReal_re]
  have hr := (abs_re_le_norm _).trans h
  change |-(μ : ℂ).re - ((V : ℂ) * b).re| ≤ V / 2 * ‖b‖ at hr
  rw [ofReal_re, re_ofReal_mul, hn] at hr
  constructor
  · intro hμ0
    by_contra hb
    have hb0 : 0 < b.re := lt_of_not_ge hb
    rw [abs_of_pos hb0] at hr
    have hh := neg_le_abs (-μ - V * b.re)
    nlinarith [mul_pos hV hb0]
  · intro hμ0
    by_contra hb
    have hb0 : b.re < 0 := lt_of_not_ge hb
    rw [abs_of_neg hb0] at hr
    have hh := le_abs_self (-μ - V * b.re)
    nlinarith [mul_neg_of_pos_of_neg hV hb0]

include hW hθ hD in
/-- The root opposing a nonnegative drift has a strict negative real scale. -/
theorem cepsRootMinus_re_ge_scale {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) (hμ0 : 0 ≤ μ)
    {q : ℂ} (hq : ‖q‖ ≤ dom.q₀) (hre : 0 ≤ q.re) :
    ‖cepsRootR D θ ρW μ q‖ / (4 * Real.sqrt v) ≤ -(cepsRootMinus D θ ρW μ q).re := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hμc := dom.μ_lt_chart hμ'
  let r := cepsRootR D θ ρW μ q
  let s := Real.sqrt (cepsStepVar ρW / 2)
  have hs : 0 < s := Real.sqrt_pos.mpr (by linarith [cepsStepVar_pos hW hθ hD])
  have hsv : s ≤ Real.sqrt v := Real.sqrt_le_sqrt (by linarith [cepsStepVar_le hW, cepsStepVar_pos hW hθ hD])
  have hrsector : ‖r‖ / 2 ≤ r.re := by
    have hnonneg : 0 ≤ (q - cepsMorseMin D θ ρW μ).re := by
      rw [sub_re]; linarith [re_cepsMorseMin_nonpos hW hθ hD hμc]
    have hrootre : 0 ≤ r.re := by
      dsimp [r, cepsRootR, Complex.sqrt]; rw [cpow_inv_two_re]; exact Real.sqrt_nonneg _
    have he : r.re ^ 2 - r.im ^ 2 = (q - cepsMorseMin D θ ρW μ).re := by
      have h := congrArg Complex.re (cepsRootR_sq D θ ρW (μ : ℂ) q)
      simpa [pow_two, mul_re] using h
    have hn := Complex.sq_norm_sub_sq_re r
    nlinarith [norm_nonneg r, sq_nonneg r.re]
  have herr := cepsMorseRoot_linear_error hW hθ hD hμc (r := -r)
    (by simpa only [norm_neg] using dom.norm_cepsRootR_lt hW hθ hD hμ' hq)
  rw [norm_neg] at herr
  change ‖cepsMorseRoot D θ ρW μ (-r) - cepsMorseCenter D θ ρW μ - (-r) / (s : ℂ)‖ ≤ ‖r‖ / (8 * s) at herr
  have hreal : (cepsMorseRoot D θ ρW μ (-r) - cepsMorseCenter D θ ρW μ - (-r) / (s : ℂ)).re =
      (cepsRootMinus D θ ρW μ q).re - (cepsMorseCenter D θ ρW μ).re + r.re / s := by
    simp [Complex.div_ofReal_re, sub_re, r, cepsRootMinus, neg_div]
  have h := (le_abs_self _).trans ((abs_re_le_norm _).trans herr)
  rw [hreal] at h
  have hc := (cepsMorseCenter_re_sign dom hW hθ hD hμ).1 hμ0
  have hrdiv := div_le_div_of_nonneg_right hrsector hs.le
  have hscale : ‖r‖ / (4 * s) ≤ -(cepsRootMinus D θ ρW μ q).re := by
    ring_nf at h hrdiv ⊢
    have hn := mul_nonneg (inv_nonneg.mpr hs.le) (norm_nonneg r)
    linarith
  exact (div_le_div_of_nonneg_left (norm_nonneg r) (by positivity) (by linarith)).trans hscale


include hW hθ hD in
/-- The root opposing a nonpositive drift has a strict positive real scale. -/
theorem cepsRootPlus_re_ge_scale {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) (hμ0 : μ ≤ 0)
    {q : ℂ} (hq : ‖q‖ ≤ dom.q₀) (hre : 0 ≤ q.re) :
    ‖cepsRootR D θ ρW μ q‖ / (4 * Real.sqrt v) ≤ (cepsRootPlus D θ ρW μ q).re := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hμc := dom.μ_lt_chart hμ'
  let r := cepsRootR D θ ρW μ q
  let s := Real.sqrt (cepsStepVar ρW / 2)
  have hs : 0 < s := Real.sqrt_pos.mpr (by linarith [cepsStepVar_pos hW hθ hD])
  have hsv : s ≤ Real.sqrt v := Real.sqrt_le_sqrt (by linarith [cepsStepVar_le hW, cepsStepVar_pos hW hθ hD])
  have hrsector : ‖r‖ / 2 ≤ r.re := by
    have hnonneg : 0 ≤ (q - cepsMorseMin D θ ρW μ).re := by
      rw [sub_re]; linarith [re_cepsMorseMin_nonpos hW hθ hD hμc]
    have hrootre : 0 ≤ r.re := by
      dsimp [r, cepsRootR, Complex.sqrt]; rw [cpow_inv_two_re]; exact Real.sqrt_nonneg _
    have he : r.re ^ 2 - r.im ^ 2 = (q - cepsMorseMin D θ ρW μ).re := by
      have h := congrArg Complex.re (cepsRootR_sq D θ ρW (μ : ℂ) q)
      simpa [pow_two, mul_re] using h
    have hn := Complex.sq_norm_sub_sq_re r
    nlinarith [norm_nonneg r, sq_nonneg r.re]
  have herr := cepsMorseRoot_linear_error hW hθ hD hμc (r := r)
    (dom.norm_cepsRootR_lt hW hθ hD hμ' hq)
  change ‖cepsMorseRoot D θ ρW μ r - cepsMorseCenter D θ ρW μ - r / (s : ℂ)‖ ≤ ‖r‖ / (8 * s) at herr
  have hreal : (cepsMorseRoot D θ ρW μ r - cepsMorseCenter D θ ρW μ - r / (s : ℂ)).re =
      (cepsRootPlus D θ ρW μ q).re - (cepsMorseCenter D θ ρW μ).re - r.re / s := by
    simp [Complex.div_ofReal_re, sub_re, r, cepsRootPlus]
  have h := (neg_le_abs _).trans ((abs_re_le_norm _).trans herr)
  rw [hreal] at h
  have hc := (cepsMorseCenter_re_sign dom hW hθ hD hμ).2 hμ0
  have hrdiv := div_le_div_of_nonneg_right hrsector hs.le
  have hscale : ‖r‖ / (4 * s) ≤ (cepsRootPlus D θ ρW μ q).re := by
    ring_nf at h hrdiv ⊢
    have hn := mul_nonneg (inv_nonneg.mpr hs.le) (norm_nonneg r)
    linarith
  exact (div_le_div_of_nonneg_left (norm_nonneg r) (by positivity) (by linarith)).trans hscale

end PGM
