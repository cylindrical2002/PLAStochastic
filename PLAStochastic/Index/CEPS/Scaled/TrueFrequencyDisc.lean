import PLAStochastic.Index.CEPS.Scaled.TrueFrequencyRadius

/-! # A common complex frequency disc for the actual scaled bridge -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrueFrequency_curve_bounds (M lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : 0 < b) (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z)) :
    |b * lam| ≤ dom.μ₀ ∧ ‖cepsComplexScaledDiscount lam z b‖ ≤ dom.q₀ / 2 ∧
      0 ≤ (cepsComplexScaledDiscount lam z b).re ∧
      (b : ℂ) ∈ ball (0 : ℂ) (dom.minimumScaleRadius (lam : ℂ)) ∧
      1 / 2 ≤ 1 + b * lam ∧ 1 + b * lam ≤ 2 ∧
      max dom.normalNegativeWidth dom.normalCoarseWidth ≤ (1 + b * lam) / b := by
  have hbP := ball_subset_ball (trueFrequencyScaleRadius_le dom M lam z) hbs
  obtain ⟨hμ, _, hre, _, _⟩ := cepsScaledTruePair_curve_bounds dom hW hθ hD M lam hz hb hbP
  have hbE := ball_subset_ball (trueDenominatorScaleRadius_le dom hW hθ hD M lam z)
    (ball_subset_ball (truePairScaleRadius_le dom M lam z) hbP)
  have hbC := ball_subset_ball ((min_le_right _ _).trans
    (div_le_self (canonScaleRadius_pos dom hW hθ hD lam z).le (by norm_num))) hbE
  have hbR := ball_subset_ball (min_le_left _ _) (ball_subset_ball (min_le_left _ _) hbC)
  have hbMin := ball_subset_ball ((radicandScaleRadius_budget dom hW hθ hD lam).2.trans
    (half_le_self (dom.minimumScaleRadius_pos (lam : ℂ)).le)) hbR
  have hq := (canonScaleCurve_bounds dom hW hθ hD lam hz (sign := 1) (by norm_num) hbC).2.1
  have hsmall := cepsScaledTruePair_drift_le_half dom hW hθ hD M lam hz hbP
  exact ⟨hμ, hq.le, hre, hbMin, by linarith [neg_le_abs (b * lam)],
    by linarith [le_abs_self (b * lam)], cepsScaledTrueFrequency_width dom hW hθ hD M lam hz hb hbs⟩

include hW hθ hD in
theorem cepsScaledTrueFrequency_discount_disc (M lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : 0 < b) (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z))
    {ζ : ℂ} (hζ : ζ ∈ ball z dom.scaledFrequencyRadius) :
    ‖cepsComplexScaledDiscount lam ζ b‖ < dom.q₀ ∧
      -(dom.normalNegativeRadius / ((1 + b * lam) / b) ^ 2) ≤
        (cepsComplexScaledDiscount lam ζ b).re := by
  obtain ⟨_, hq, hre, _, hwlo, hwhi, hl⟩ :=
    cepsScaledTrueFrequency_curve_bounds dom hW hθ hD M lam hz hb hbs
  have hmap := cepsComplexScaledDiscount_maps_frequency_ball dom hD hb hwlo hwhi z hζ
  apply cepsNormal_discount_disc_subset dom hW hθ hD hl hq _ hmap
  exact (neg_nonpos.mpr (by have := cepsNormal_negativeRadius_pos dom hD; positivity)).trans hre

include hW hθ hD in
theorem cepsScaledTrueBridge_differentiableOn_frequency_disc (M lam : ℝ)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z)) :
    DifferentiableOn ℂ (fun ζ => cepsScaledTrueBridge dom ρW lam ζ b)
      (ball z dom.scaledFrequencyRadius) := by
  let μ := b * lam
  let l := (1 + b * lam) / b
  let q : ℂ → ℂ := fun ζ => cepsComplexScaledDiscount lam ζ b
  let F : ℂ → ℂ := fun q => (cepsWHNormalData D θ ρW μ q).regularBridge (dom.canonL ρW) μ q l
  obtain ⟨hμ, _, _, _, _, _, hl⟩ := cepsScaledTrueFrequency_curve_bounds dom hW hθ hD M lam hz hb hbs
  have hd : DifferentiableOn ℂ (fun ζ => F (q ζ) / (b : ℂ)) (ball z dom.scaledFrequencyRadius) := by
    intro ζ hζ
    obtain ⟨hq, hre⟩ := cepsScaledTrueFrequency_discount_disc dom hW hθ hD M lam hz hb hbs hζ
    have hF : DifferentiableAt ℂ F (q ζ) :=
      (cepsNormal_actual_holomorphicAt_negative dom hW hθ hD hμ hq
        (t := 0) (by simpa using half_pos dom.c₀_pos) ((le_max_left _ _).trans hl) hre).2
    have hq : DifferentiableAt ℂ q ζ := by unfold q cepsComplexScaledDiscount; fun_prop
    exact ((hF.comp ζ hq).div_const (b : ℂ)).differentiableWithinAt
  apply hd.congr
  intro ζ hζ
  have hq := (cepsScaledTrueFrequency_discount_disc dom hW hθ hD M lam hz hb hbs hζ).1.le
  have he := cepsScaledTrueBridge_eq_actual_on_discount_disc dom hW hθ hD hb hμ hq
  have he' : (b : ℂ) * cepsScaledTrueBridge dom ρW lam ζ b = F (q ζ) := by
    simpa only [F, q, μ, l, ofReal_mul, ofReal_div, ofReal_add, ofReal_one] using! he
  have heq : cepsScaledTrueBridge dom ρW lam ζ b = F (q ζ) / (b : ℂ) :=
    (eq_div_iff (ofReal_ne_zero.mpr hb.ne')).mpr (by simpa only [mul_comm] using he')
  exact heq

end PGM
