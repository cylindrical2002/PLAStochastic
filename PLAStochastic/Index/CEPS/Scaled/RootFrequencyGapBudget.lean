import PLAStochastic.Index.CEPS.Scaled.RootEvaluationDerivativeError

/-! # Root-gap inverse and derivative budgets with their drift weights -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.rootFrequencyGapInverseConstant {D θ v : ℝ}
    (_dom : CepsCanonDomain D θ v) : ℝ := 2 * Real.sqrt v * Real.sqrt (8 * v + 8)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledRootGap_frequency_sector (M lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    {b : ℝ} (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z)) :
    ‖cepsScaledRootCoordinate D θ ρW lam z b‖ / (2 * Real.sqrt v) ≤
      (cepsScaledSignedRoot D θ ρW lam z 1 b - cepsScaledSignedRoot D θ ρW lam z (-1) b).re := by
  have hbE := ball_subset_ball (trueDenominatorScaleRadius_le dom hW hθ hD M lam z)
    (ball_subset_ball (truePairScaleRadius_le dom M lam z)
      (ball_subset_ball (trueFrequencyScaleRadius_le dom M lam z) hbs))
  apply cepsScaledRootGap_complex_sector dom hW hθ hD lam hz
  apply ball_subset_ball ((min_le_right _ _).trans _) hbE
  exact div_le_div_of_nonneg_left (canonScaleRadius_pos dom hW hθ hD lam z).le (by norm_num) (by norm_num)

include hW hθ hD in
theorem cepsScaledRootGap_frequency_inverse_budget (M lam : ℝ) (hlam : lam ≠ 0)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z)) :
    cepsScaledSignedRoot D θ ρW lam z 1 b ≠ cepsScaledSignedRoot D θ ρW lam z (-1) b ∧
      ‖(cepsScaledSignedRoot D θ ρW lam z 1 b - cepsScaledSignedRoot D θ ρW lam z (-1) b)⁻¹‖ * |lam| ≤
        dom.rootFrequencyGapInverseConstant := by
  let r := cepsScaledRootCoordinate D θ ρW lam z (b : ℂ)
  let g := cepsScaledSignedRoot D θ ρW lam z 1 b - cepsScaledSignedRoot D θ ρW lam z (-1) b
  have hv := CepsCanonDomain.v_pos hW hθ hD
  have hs : 0 < Real.sqrt (8 * v + 8) := Real.sqrt_pos.mpr (by linarith)
  have hvS : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hbE := ball_subset_ball (trueDenominatorScaleRadius_le dom hW hθ hD M lam z)
    (ball_subset_ball (truePairScaleRadius_le dom M lam z)
      (ball_subset_ball (trueFrequencyScaleRadius_le dom M lam z) hbs))
  have hbSur := ball_subset_ball (min_le_left _ _) (ball_subset_ball (min_le_left _ _) hbE)
  have hl := (scaledCoordinateLower_drift_frequency_le dom hW hθ hD lam z).trans
    (cepsScaledRootCoordinate_lower dom hW hθ hD 0 M lam hz hbSur)
  have hL : |lam| ≤ ‖r‖ * Real.sqrt (8 * v + 8) := by
    have := (div_le_iff₀ hs).mp hl
    linarith [Real.sqrt_nonneg ‖z‖]
  have hg := (cepsScaledRootGap_frequency_sector dom hW hθ hD M lam hz hbs).trans (re_le_norm g)
  have hg' : ‖r‖ ≤ ‖g‖ * (2 * Real.sqrt v) := (div_le_iff₀ (by positivity)).mp hg
  have hbound : |lam| ≤ dom.rootFrequencyGapInverseConstant * ‖g‖ := by
    apply hL.trans
    apply (mul_le_mul_of_nonneg_right hg' hs.le).trans_eq
    unfold CepsCanonDomain.rootFrequencyGapInverseConstant
    ring
  have hgpos : 0 < ‖g‖ := by
    by_contra hn
    have he : ‖g‖ = 0 := le_antisymm (le_of_not_gt hn) (norm_nonneg _)
    rw [he, mul_zero] at hbound
    exact (abs_pos.mpr hlam).not_ge hbound
  refine ⟨sub_ne_zero.mp (norm_pos_iff.mp hgpos), ?_⟩
  change ‖g⁻¹‖ * |lam| ≤ _
  rw [norm_inv, inv_mul_eq_div, div_le_iff₀ hgpos]
  exact hbound

include hW hθ hD in
theorem cepsScaledRootWeights_frequency_order (M lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z)) :
    Real.exp (-(cepsScaledSignedRoot D θ ρW lam z 1 b * (1 + (b : ℂ) * lam)).re) ≤
      Real.exp (-(cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + (b : ℂ) * lam)).re) := by
  have hv := CepsCanonDomain.v_pos hW hθ hD
  have hS := Real.sqrt_pos.mpr hv
  have hg := cepsScaledRootGap_frequency_sector dom hW hθ hD M lam hz hbs
  have hg0 : 0 ≤ (cepsScaledSignedRoot D θ ρW lam z 1 b - cepsScaledSignedRoot D θ ρW lam z (-1) b).re :=
    (div_nonneg (norm_nonneg _) (by positivity)).trans hg
  have hw := (cepsScaledTrueFrequency_curve_bounds dom hW hθ hD M lam hz hb hbs).2.2.2.2.1
  apply Real.exp_le_exp.mpr
  rw [show (1 + (b : ℂ) * lam : ℂ) = ((1 + b * lam : ℝ) : ℂ) by simp [ofReal_mul]]
  simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, sub_re] at hg0 ⊢
  nlinarith

end PGM
