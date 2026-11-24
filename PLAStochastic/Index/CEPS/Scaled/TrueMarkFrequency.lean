import PLAStochastic.Index.CEPS.Scaled.TrueEntranceFrequency
import PLAStochastic.Index.CEPS.Scaled.TrueMarkPrefactor

/-! # Actual marked factor and quotient on a common zero-frequency disc -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrueMarkLog_zero_frequency_budget (M lam : ℝ) {b : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam 0)) :
    DifferentiableOn ℂ (fun ζ => dom.canonL ρW (b * lam)
      (cepsComplexScaledDiscount lam ζ b) ((b : ℂ) ^ 2 * ζ))
      (ball 0 dom.trueEntranceFrequencyRadius) ∧
    ∀ ζ ∈ ball (0 : ℂ) dom.trueEntranceFrequencyRadius,
      ‖dom.canonL ρW (b * lam) (cepsComplexScaledDiscount lam ζ b) ((b : ℂ) ^ 2 * ζ)‖ ≤
        dom.normalLogBound := by
  have hμ := (cepsScaledTrueFrequency_curve_bounds dom hW hθ hD M lam (by simp) hb hbs).1
  have hμn : ‖((b * lam : ℝ) : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hq : ∀ ζ ∈ ball (0 : ℂ) dom.trueEntranceFrequencyRadius,
      ‖cepsComplexScaledDiscount lam ζ b‖ < dom.q₀ := fun ζ hζ =>
    (cepsScaledTrueFrequency_discount_disc dom hW hθ hD M lam (by simp) hb hbs
      (ball_subset_ball (trueEntranceFrequencyRadius_le dom) hζ)).1
  have ht : ∀ ζ ∈ ball (0 : ℂ) dom.trueEntranceFrequencyRadius,
      ‖(b : ℂ) ^ 2 * ζ‖ < dom.c₀ / 4 := fun ζ hζ =>
    (cepsScaledTrueEntrance_frequency_marker_bounds dom hW hθ hD M lam hb hb1 hbs hζ).1
  have hd := dom.differentiableOn_cepsCanonL hW hθ hD (γ := 1) (by norm_num) le_rfl
    (c := dom.c₀) le_rfl (by linarith [dom.c₀_pos]) hμn (ofReal_im (b * lam))
  have hc : DifferentiableOn ℂ (fun ζ : ℂ =>
      ((b : ℂ) ^ 2 * ζ, cepsComplexScaledDiscount lam ζ b))
      (ball 0 dom.trueEntranceFrequencyRadius) := by unfold cepsComplexScaledDiscount; fun_prop
  refine ⟨?_, ?_⟩
  · simpa only [Function.comp_apply, CepsCanonDomain.canonL, ofReal_mul] using! hd.comp hc
      (fun ζ hζ => ⟨by linarith [re_le_norm ((b : ℂ) ^ 2 * ζ), ht ζ hζ, dom.c₀_pos], hq ζ hζ⟩)
  · intro ζ hζ
    simpa only [ofReal_mul, CepsCanonDomain.canonL, CepsCanonDomain.normalLogBound] using!
      dom.norm_cepsCanonL_le hW hθ hD (γ := 1) (by norm_num) le_rfl
      (c := dom.c₀) le_rfl (by linarith [dom.c₀_pos]) hμn (ofReal_im (b * lam))
      (hq ζ hζ).le (show ‖(b : ℂ) ^ 2 * ζ‖ ≤ dom.c₀ / 2 by linarith [ht ζ hζ, dom.c₀_pos])

include hW hθ hD in
theorem cepsScaledTrueMarkQuotient_zero_frequency_budget (M lam : ℝ) {b : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam 0)) :
    DifferentiableOn ℂ (fun ζ => cepsQ D θ ρW ((b : ℂ) * lam)
      (cepsComplexScaledDiscount lam ζ b) ((b : ℂ) ^ 2 * ζ))
      (ball 0 dom.trueEntranceFrequencyRadius) ∧
    ∀ ζ ∈ ball (0 : ℂ) dom.trueEntranceFrequencyRadius,
      cepsVarLo D / 4 ≤ ‖cepsQ D θ ρW ((b : ℂ) * lam)
        (cepsComplexScaledDiscount lam ζ b) ((b : ℂ) ^ 2 * ζ)‖ := by
  have hμ := (cepsScaledTrueFrequency_curve_bounds dom hW hθ hD M lam (by simp) hb hbs).1
  have hμn : ‖(b : ℂ) * lam‖ ≤ dom.μ₀ := by
    rw [← ofReal_mul, norm_real, Real.norm_eq_abs]
    exact hμ
  have hq : ∀ ζ ∈ ball (0 : ℂ) dom.trueEntranceFrequencyRadius,
      ‖cepsComplexScaledDiscount lam ζ b‖ < dom.q₀ := fun ζ hζ =>
    (cepsScaledTrueFrequency_discount_disc dom hW hθ hD M lam (by simp) hb hbs
      (ball_subset_ball (trueEntranceFrequencyRadius_le dom) hζ)).1
  have ht : ∀ ζ ∈ ball (0 : ℂ) dom.trueEntranceFrequencyRadius,
      ‖(b : ℂ) ^ 2 * ζ‖ < dom.ρA := by
    intro ζ hζ
    have := (cepsScaledTrueEntrance_frequency_marker_bounds dom hW hθ hD M lam hb hb1 hbs hζ).1
    have := dom.c₀_le
    have := dom.ρA_pos
    linarith
  have hc : DifferentiableOn ℂ (fun ζ : ℂ =>
      (cepsComplexScaledDiscount lam ζ b, (b : ℂ) ^ 2 * ζ))
      (ball 0 dom.trueEntranceFrequencyRadius) := by unfold cepsComplexScaledDiscount; fun_prop
  have hmap : MapsTo (fun ζ : ℂ => (cepsComplexScaledDiscount lam ζ b, (b : ℂ) ^ 2 * ζ))
      (ball 0 dom.trueEntranceFrequencyRadius)
      ({q | ‖q - cepsMorseMin D θ ρW ((b : ℂ) * lam)‖ < dom.rmax ^ 2} ×ˢ ball 0 dom.ρA) := by
    intro ζ hζ
    refine ⟨?_, mem_ball_zero_iff.mpr (ht ζ hζ)⟩
    change ‖cepsComplexScaledDiscount lam ζ b - cepsMorseMin D θ ρW ((b : ℂ) * lam)‖ < dom.rmax ^ 2
    have hn := norm_sub_le (cepsComplexScaledDiscount lam ζ b) (cepsMorseMin D θ ρW ((b : ℂ) * lam))
    have hm := cepsMorseMin_norm_le_class dom hW hθ hD hμn
    have hq' := hq ζ hζ
    rw [dom.q₀_def] at hq'
    nlinarith [sq_pos_of_pos dom.rmax_pos]
  refine ⟨?_, ?_⟩
  · simpa only [Function.comp_apply] using!
      (cepsQ_differentiableOn_joint_q_spatial dom hW hθ hD hμn).comp hc hmap
  · intro ζ hζ
    exact cepsQ_norm_ge_on_rootZone dom hW hθ hD hμn (hq ζ hζ).le (ht ζ hζ)

include hW hθ hD in
theorem cepsScaledTrueMarkPrefactor_zero_frequency_budget (M lam : ℝ) {b : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam 0)) :
    DifferentiableOn ℂ (fun ζ => cepsScaledTrueMarkPrefactor dom ρW lam ζ b)
      (ball 0 dom.trueEntranceFrequencyRadius) ∧
    ∀ ζ ∈ ball (0 : ℂ) dom.trueEntranceFrequencyRadius,
      ‖cepsScaledTrueMarkPrefactor dom ρW lam ζ b‖ ≤ Real.exp dom.normalLogBound * (4 / cepsVarLo D) := by
  obtain ⟨hL, hLb⟩ := cepsScaledTrueMarkLog_zero_frequency_budget dom hW hθ hD M lam hb hb1 hbs
  obtain ⟨hQ, hQb⟩ := cepsScaledTrueMarkQuotient_zero_frequency_budget dom hW hθ hD M lam hb hb1 hbs
  have ha : 0 < cepsVarLo D / 4 := by have := cepsVarLo_pos hD; positivity
  refine ⟨hL.cexp.div hQ (fun ζ hζ => norm_pos_iff.mp (ha.trans_le (hQb ζ hζ))), ?_⟩
  intro ζ hζ
  unfold cepsScaledTrueMarkPrefactor
  rw [norm_div]
  exact (div_le_div₀ (by positivity : 0 ≤ Real.exp dom.normalLogBound)
    (by rw [norm_exp]; exact Real.exp_le_exp.mpr ((re_le_norm _).trans (hLb ζ hζ))) ha
    (hQb ζ hζ)).trans_eq (by ring)

end PGM
