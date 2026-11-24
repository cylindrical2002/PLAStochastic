import PLAStochastic.Index.CEPS.Scaled.TrueNegativePair

/-! # Actual root-gap size on the common complex frequency disc -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledRoots_frequency_gap_budget (M lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z))
    {ζ : ℂ} (hζ : ζ ∈ ball z dom.scaledFrequencyRadius) :
    ‖cepsScaledSignedRoot D θ ρW lam ζ 1 b - cepsScaledSignedRoot D θ ρW lam ζ (-1) b‖ ≤
      (2 * cepsChartK D * dom.frequencyRootBound) * (1 + |lam| + Real.sqrt ‖z‖) := by
  let μ := b * lam
  let q := cepsComplexScaledDiscount lam ζ b
  let r := cepsRootR D θ ρW μ q
  obtain ⟨hμ, _, _, hbMin, _, _, _⟩ :=
    cepsScaledTrueFrequency_curve_bounds dom hW hθ hD M lam hz hb hbs
  have hq := (cepsScaledTrueFrequency_discount_disc dom hW hθ hD M lam hz hb hbs hζ).1.le
  have hμn : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by simpa only [μ, norm_real, Real.norm_eq_abs] using hμ
  have hμc := dom.μ_lt_chart hμn
  have hr : ‖r‖ < cepsChartRho D θ := dom.norm_cepsRootR_lt hW hθ hD hμn hq
  have hgap := norm_cepsMorseRoot_sub_le hW hθ hD hμc hr
    (show ‖-r‖ < cepsChartRho D θ by simpa only [norm_neg] using hr)
  have hchart := two_div_norm_cepsChartSlope_le hW hθ hD
  have hgap' : ‖cepsRootPlus D θ ρW μ q - cepsRootMinus D θ ρW μ q‖ ≤
      (2 * cepsChartK D) * ‖r‖ := by
    have hh := hgap.trans (mul_le_mul_of_nonneg_right hchart (norm_nonneg (r - -r)))
    exact hh.trans_eq (by rw [sub_neg_eq_add, ← two_mul, norm_mul]; norm_num; ring)
  have hqeq : q = cepsScaledDiscount b lam ζ := by
    simp only [q, cepsComplexScaledDiscount, cepsScaledDiscount, ofReal_mul]
  have hR : ‖r‖ = b * ‖cepsScaledRootCoordinate D θ ρW lam ζ b‖ := by
    dsimp only [r, μ]
    rw [hqeq, ofReal_mul, cepsScaledRootCoordinate_actual hW hθ hD hb hμc,
      norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hb]
  have hscaled : (b : ℂ) * (cepsScaledSignedRoot D θ ρW lam ζ 1 b -
      cepsScaledSignedRoot D θ ρW lam ζ (-1) b) =
        cepsRootPlus D θ ρW μ q - cepsRootMinus D θ ρW μ q := by
    rw [cepsScaledSignedRoot_plus_actual hW hθ hD hb hμc,
      cepsScaledSignedRoot_minus_actual hW hθ hD hb hμc, ← sub_div,
      mul_div_cancel₀ _ (ofReal_ne_zero.mpr hb.ne'), ← hqeq]
  have hn := congrArg norm hscaled
  rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hb] at hn
  have hK := (cepsChartK_pos hD).le
  have hroot := cepsScaledRootCoordinate_near_frequency_budget dom hW hθ hD lam z hbMin hζ
  apply le_of_mul_le_mul_left (a := b) _ hb
  calc
    _ = _ := hn
    _ ≤ (2 * cepsChartK D) * ‖r‖ := hgap'
    _ = (2 * cepsChartK D) * (b * ‖cepsScaledRootCoordinate D θ ρW lam ζ b‖) := by rw [hR]
    _ ≤ (2 * cepsChartK D) * (b * (dom.frequencyRootBound *
        (1 + |lam| + Real.sqrt ‖z‖))) := by gcongr
    _ = _ := by ring

end PGM
