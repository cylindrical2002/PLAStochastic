import PLAStochastic.Index.CEPS.Scaled.FrequencyGapBudget
import PLAStochastic.Index.CEPS.Scaled.PositiveHalfFrequency

/-! # Coarse actual half-line and correction frequency bounds -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.trueHalfFrequencyConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) : ℝ :=
  (2 * cepsChartK D * dom.frequencyRootBound) *
    (Real.exp dom.normalRootSlack * (v * Real.exp (2 * dom.normalLogBound)))

def CepsCanonDomain.trueCorrectionFrequencyConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) : ℝ :=
  dom.trueFrequencyBridgeConstant + dom.trueHalfFrequencyConstant

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem trueHalfFrequencyConstant_pos : 0 < dom.trueHalfFrequencyConstant := by
  have := cepsChartK_pos hD
  have := frequencyRootBound_pos dom hD
  have := CepsCanonDomain.v_pos hW hθ hD
  unfold CepsCanonDomain.trueHalfFrequencyConstant
  positivity

include hW hθ hD in
theorem cepsScaledTrueGRoot_frequency_budget (M lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z))
    {ζ : ℂ} (hζ : ζ ∈ ball z dom.scaledFrequencyRadius) :
    ‖cepsScaledTrueG dom ρW lam ζ b (cepsScaledSignedRoot D θ ρW lam ζ 1 b)‖ ≤
      Real.exp dom.normalRootSlack * (v * Real.exp (2 * dom.normalLogBound)) := by
  let μ := b * lam
  let q := cepsComplexScaledDiscount lam ζ b
  let l := (1 + b * lam) / b
  obtain ⟨hμ, _, _, _, _, _, hl⟩ :=
    cepsScaledTrueFrequency_curve_bounds dom hW hθ hD M lam hz hb hbs
  obtain ⟨hq, hre⟩ := cepsScaledTrueFrequency_discount_disc dom hW hθ hD M lam hz hb hbs hζ
  have hμn : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by simpa only [μ, norm_real, Real.norm_eq_abs] using hμ
  have hl0 := (cepsNormal_width_properties dom hW hθ hD
    ((le_max_left _ _).trans ((le_max_right _ _).trans hl))).1
  have hp := dom.norm_rootPlus_le hW hθ hD hμn hq.le
  have hsign := (cepsRoots_re_signs_negative dom hW hθ hD hμ hq.le hl0 hre).1
  have hn := cepsNormal_weight_le_of_re_slack dom hW hθ hD hμ hq.le hp hsign
  have he := (cepsScaledTrue_physical_slopes_of_discount_disc dom hW hθ hD hb hμ hq.le).2.2.1
  have he' : cepsScaledTrueG dom ρW lam ζ b (cepsScaledSignedRoot D θ ρW lam ζ 1 b) =
      (cepsWHNormalData D θ ρW μ q).normalG (dom.canonL ρW) μ q l
        (cepsRootPlus D θ ρW μ q) := by
    simpa only [μ, q, l, cepsWHNormalData, ofReal_mul, ofReal_div, ofReal_add, ofReal_one] using! he
  rw [he']
  exact hn

include hW hθ hD in
theorem cepsScaledTrueHalfBridge_frequency_budget (M lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z))
    {ζ : ℂ} (hζ : ζ ∈ ball z dom.scaledFrequencyRadius) :
    ‖cepsScaledTrueHalfBridge dom ρW lam ζ b‖ ≤
      dom.trueHalfFrequencyConstant * (1 + |lam| + Real.sqrt ‖z‖) := by
  have hgap := cepsScaledRoots_frequency_gap_budget dom hW hθ hD M lam hz hb hbs hζ
  have hG := cepsScaledTrueGRoot_frequency_budget dom hW hθ hD M lam hz hb hbs hζ
  unfold cepsScaledTrueHalfBridge
  rw [norm_mul]
  exact (mul_le_mul hgap hG (norm_nonneg _) ((norm_nonneg _).trans hgap)).trans_eq
    (by unfold CepsCanonDomain.trueHalfFrequencyConstant; ring)

include hW hθ hD in
theorem cepsScaledTrueBridgeCorrection_frequency_budget (M lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z))
    {ζ : ℂ} (hζ : ζ ∈ ball z dom.scaledFrequencyRadius) :
    ‖cepsScaledTrueBridgeCorrection dom ρW lam ζ b‖ ≤
      dom.trueCorrectionFrequencyConstant * (1 + |lam| + Real.sqrt ‖z‖) := by
  exact (norm_sub_le _ _).trans ((add_le_add
    (cepsScaledTrueBridge_frequency_disc_budget dom hW hθ hD M lam hz hb hbs hζ)
    (cepsScaledTrueHalfBridge_frequency_budget dom hW hθ hD M lam hz hb hbs hζ)).trans_eq
      (by unfold CepsCanonDomain.trueCorrectionFrequencyConstant; ring))

include hW hθ hD in
theorem cepsScaledTrueHalfBridge_positive_frequency_derivative_budget (M lam : ℝ) (hlam : 1 ≤ lam)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z)) :
    ‖deriv (fun ζ => cepsScaledTrueHalfBridge dom ρW lam ζ b) z‖ ≤
      (2 * dom.trueHalfFrequencyConstant / dom.positiveFrequencyRadius) *
        (1 + |lam| + Real.sqrt ‖z‖) := by
  have hn := norm_iteratedDeriv_le_of_ball 1 (positiveFrequencyRadius_pos dom hW hθ hD)
    (cepsScaledTrueHalfBridge_positive_frequency_differentiableOn dom hW hθ hD M lam hlam hz hb hbs)
    (fun ζ hζ => cepsScaledTrueHalfBridge_frequency_budget dom hW hθ hD M lam hz hb hbs
      (ball_subset_ball (positiveFrequencyRadius_le dom) hζ))
  simp only [iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, one_mul, pow_one] at hn
  exact hn.trans_eq (by ring)

end PGM
