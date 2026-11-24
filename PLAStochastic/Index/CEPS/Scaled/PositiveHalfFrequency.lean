import PLAStochastic.Index.CEPS.Scaled.PositiveFrequencyHolomorphy

/-! # Actual positive-tail half-line bridge frequency holomorphy -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrueGRoot_positive_frequency_differentiableOn (M lam : ℝ) (hlam : 1 ≤ lam)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z)) :
    DifferentiableOn ℂ (fun ζ => cepsScaledTrueG dom ρW lam ζ b
      (cepsScaledSignedRoot D θ ρW lam ζ 1 b)) (ball z dom.positiveFrequencyRadius) := by
  let μ := b * lam
  let q : ℂ → ℂ := fun ζ => cepsComplexScaledDiscount lam ζ b
  let p : ℂ → ℂ := fun ζ => (b : ℂ) * cepsScaledSignedRoot D θ ρW lam ζ 1 b
  let U : Set ℂ := ball z dom.positiveFrequencyRadius
  have hμ := (cepsScaledTrueFrequency_curve_bounds dom hW hθ hD M lam hz hb hbs).1
  have hμn : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by simpa only [μ, norm_real, Real.norm_eq_abs] using hμ
  have hμc := dom.μ_lt_chart hμn
  have hqnorm : ∀ ζ ∈ U, ‖q ζ‖ < dom.q₀ := fun ζ hζ =>
    (cepsScaledTrueFrequency_discount_disc dom hW hθ hD M lam hz hb hbs
      (ball_subset_ball (positiveFrequencyRadius_le dom) hζ)).1
  have hpa : ∀ ζ, p ζ = cepsRootPlus D θ ρW μ (q ζ) := by
    intro ζ
    dsimp [p]
    rw [cepsScaledSignedRoot_plus_actual hW hθ hD hb hμc,
      mul_div_cancel₀ _ (ofReal_ne_zero.mpr hb.ne')]
    simp only [μ, q, cepsScaledDiscount, cepsComplexScaledDiscount, ofReal_mul]
  have hpbound : ∀ ζ ∈ U, ‖p ζ‖ ≤ dom.c₀ / 4 := fun ζ hζ =>
    hpa ζ ▸ dom.norm_rootPlus_le hW hθ hD hμn (hqnorm ζ hζ).le
  have hdq : DifferentiableOn ℂ q U := by unfold q cepsComplexScaledDiscount; fun_prop
  have hdp := (cepsScaledPositiveFrequency_roots_differentiableOn dom hW hθ hD
    M lam hlam hz hb hbs).1.const_mul (b : ℂ)
  have hQmap : MapsTo (fun ζ => (q ζ, p ζ)) U
      ({q | ‖q - cepsMorseMin D θ ρW μ‖ < dom.rmax ^ 2} ×ˢ ball 0 dom.ρA) := by
    intro ζ hζ
    constructor
    · change ‖q ζ - cepsMorseMin D θ ρW μ‖ < dom.rmax ^ 2
      have hn := norm_sub_le (q ζ) (cepsMorseMin D θ ρW μ)
      have hq := hqnorm ζ hζ
      have hm := cepsMorseMin_norm_le_class dom hW hθ hD hμn
      rw [dom.q₀_def] at hq
      nlinarith [sq_pos_of_pos dom.rmax_pos]
    · apply mem_ball_zero_iff.mpr
      have := hpbound ζ hζ
      have := dom.c₀_le
      have := dom.ρA_pos
      linarith
  have hdQ := (cepsQ_differentiableOn_joint_q_spatial dom hW hθ hD hμn).comp
    (hdq.prodMk hdp) hQmap
  have hdLc := dom.differentiableOn_cepsCanonL hW hθ hD (γ := 1) (by norm_num) le_rfl
    (c := dom.c₀) le_rfl (by linarith [dom.c₀_pos]) hμn (ofReal_im μ)
  have hLmap : MapsTo (fun ζ => (p ζ, q ζ)) U
      {x : ℂ × ℂ | x.1.re < dom.c₀ ∧ ‖x.2‖ < dom.q₀} := by
    intro ζ hζ
    exact ⟨by have := hpbound ζ hζ; linarith [re_le_norm (p ζ), dom.c₀_pos], hqnorm ζ hζ⟩
  have hdL := hdLc.comp (hdp.prodMk hdq) hLmap
  have hdE := ((cepsScaledPositiveFrequency_roots_differentiableOn dom hW hθ hD
    M lam hlam hz hb hbs).1.neg.mul_const (1 + (b : ℂ) * lam)).cexp
  simpa only [cepsScaledTrueG, cepsCanonTrueWeight, Function.comp_apply, μ, p, q,
    CepsCanonDomain.canonL] using! hdE.mul (hdQ.mul ((hdL.const_mul (-2)).cexp))

include hW hθ hD in
theorem cepsScaledTrueHalfBridge_positive_frequency_differentiableOn (M lam : ℝ) (hlam : 1 ≤ lam)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z)) :
    DifferentiableOn ℂ (fun ζ => cepsScaledTrueHalfBridge dom ρW lam ζ b)
      (ball z dom.positiveFrequencyRadius) :=
  ((cepsScaledPositiveFrequency_roots_differentiableOn dom hW hθ hD M lam hlam hz hb hbs).1.sub
    (cepsScaledPositiveFrequency_roots_differentiableOn dom hW hθ hD M lam hlam hz hb hbs).2).mul
      (cepsScaledTrueGRoot_positive_frequency_differentiableOn dom hW hθ hD M lam hlam hz hb hbs)

include hW hθ hD in
theorem cepsScaledTrueBridgeCorrection_positive_frequency_differentiableOn
    (M lam : ℝ) (hlam : 1 ≤ lam) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z)) :
    DifferentiableOn ℂ (fun ζ => cepsScaledTrueBridgeCorrection dom ρW lam ζ b)
      (ball z dom.positiveFrequencyRadius) :=
  ((cepsScaledTrueBridge_differentiableOn_frequency_disc dom hW hθ hD M lam hz hb hbs).mono
    (ball_subset_ball (positiveFrequencyRadius_le dom))).sub
      (cepsScaledTrueHalfBridge_positive_frequency_differentiableOn dom hW hθ hD M lam hlam hz hb hbs)

end PGM
