import PLAStochastic.Index.CEPS.Scaled.TrueFrequencyDisc
import PLAStochastic.Index.CEPS.Normal.EntranceMarkerSlack
import PLAStochastic.Index.CEPS.Normal.MarkerCurve

/-! # Actual moving entrance on a common frequency disc at zero -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.trueEntranceFrequencyRadius {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) : ℝ :=
  min dom.scaledFrequencyRadius (min (dom.c₀ / 4) (dom.normalRootSlack / 4))

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hD in
theorem trueEntranceFrequencyRadius_pos : 0 < dom.trueEntranceFrequencyRadius := by
  have hs : 0 < dom.normalRootSlack := by
    unfold CepsCanonDomain.normalRootSlack
    exact mul_pos (cepsChartK_pos hD)
      (Real.sqrt_pos.mpr (cepsNormal_negativeRadius_pos dom hD))
  have := scaledFrequencyRadius_pos dom hD
  have := dom.c₀_pos
  unfold CepsCanonDomain.trueEntranceFrequencyRadius
  positivity

theorem trueEntranceFrequencyRadius_le :
    dom.trueEntranceFrequencyRadius ≤ dom.scaledFrequencyRadius := min_le_left _ _

include hW hθ hD in
theorem cepsScaledTrueEntrance_frequency_marker_bounds (M lam : ℝ) {b : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam 0))
    {ζ : ℂ} (hζ : ζ ∈ ball 0 dom.trueEntranceFrequencyRadius) :
    ‖(b : ℂ) ^ 2 * ζ‖ < dom.c₀ / 4 ∧
      -dom.normalRootSlack ≤ ((b : ℂ) ^ 2 * ζ).re * ((1 + b * lam) / b) := by
  obtain ⟨_, _, _, _, hwlo, hwhi, _⟩ :=
    cepsScaledTrueFrequency_curve_bounds dom hW hθ hD M lam (by simp) hb hbs
  have hl0 : 0 < (1 + b * lam) / b := div_pos (by linarith) hb
  have hn : ‖ζ‖ < dom.trueEntranceFrequencyRadius := mem_ball_zero_iff.mp hζ
  have hrc : dom.trueEntranceFrequencyRadius ≤ dom.c₀ / 4 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hrs : dom.trueEntranceFrequencyRadius ≤ dom.normalRootSlack / 4 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have ht : ‖(b : ℂ) ^ 2 * ζ‖ = b ^ 2 * ‖ζ‖ := by
    rw [norm_mul, norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hb]
  have hb2 : b ^ 2 ≤ 1 := by nlinarith
  have htbound : ‖(b : ℂ) ^ 2 * ζ‖ < dom.c₀ / 4 := by
    rw [ht]
    exact (mul_le_mul_of_nonneg_right hb2 (norm_nonneg ζ)).trans_lt
      (by simpa only [one_mul] using hn.trans_le hrc)
  have hnorm : ‖(b : ℂ) ^ 2 * ζ‖ * ((1 + b * lam) / b) ≤ dom.normalRootSlack := by
    rw [ht]
    have he : b ^ 2 * ‖ζ‖ * ((1 + b * lam) / b) = b * (1 + b * lam) * ‖ζ‖ := by
      field_simp
    rw [he]
    have hw : b * (1 + b * lam) ≤ 2 :=
      (mul_le_mul_of_nonneg_left hwhi hb.le).trans (by linarith)
    have hsl : 0 ≤ dom.normalRootSlack := le_trans (by positivity : 0 ≤ 4 * ‖ζ‖)
      (by linarith [hn.trans_le hrs])
    exact (mul_le_mul_of_nonneg_right hw (norm_nonneg ζ)).trans (by linarith [hn.trans_le hrs])
  have hnegative : -‖(b : ℂ) ^ 2 * ζ‖ ≤ ((b : ℂ) ^ 2 * ζ).re := by
    linarith [(neg_le_abs ((b : ℂ) ^ 2 * ζ).re).trans (abs_re_le_norm _)]
  have hre := mul_le_mul_of_nonneg_right hnegative hl0.le
  exact ⟨htbound, by linarith⟩

include hW hθ hD in
theorem cepsScaledTrueEntrance_differentiableOn_zero_frequency_disc (M lam : ℝ) {b : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam 0)) :
    DifferentiableOn ℂ (fun ζ => cepsScaledTrueEntrance dom ρW lam ζ b)
      (ball 0 dom.trueEntranceFrequencyRadius) := by
  let μ := b * lam
  let l := (1 + b * lam) / b
  let w : ℂ := 1 + (b : ℂ) * lam
  let q : ℂ → ℂ := fun ζ => cepsComplexScaledDiscount lam ζ b
  let T : ℂ → ℂ := fun q => q / w
  let F : ℂ → ℂ := fun q => (cepsWHNormalData D θ ρW μ q).regularEntrance
    (dom.canonL ρW) μ q l (T q)
  obtain ⟨hμ, _, _, _, hwlo, _, hl⟩ :=
    cepsScaledTrueFrequency_curve_bounds dom hW hθ hD M lam (by simp) hb hbs
  have hw0 : w ≠ 0 := by
    have hwr : w.re = 1 + b * lam := by simp [w, mul_re]
    intro he
    rw [he, zero_re] at hwr
    linarith
  have htq : ∀ ζ, T (q ζ) = (b : ℂ) ^ 2 * ζ := by
    intro ζ
    unfold T q cepsComplexScaledDiscount
    change (b : ℂ) ^ 2 * ζ * w / w = _
    exact mul_div_cancel_right₀ _ hw0
  have hd : DifferentiableOn ℂ (fun ζ => (b : ℂ) * F (q ζ))
      (ball 0 dom.trueEntranceFrequencyRadius) := by
    intro ζ hζ
    obtain ⟨hq, hre⟩ := cepsScaledTrueFrequency_discount_disc dom hW hθ hD
      M lam (by simp) hb hbs (ball_subset_ball (trueEntranceFrequencyRadius_le dom) hζ)
    have ht := (cepsScaledTrueEntrance_frequency_marker_bounds dom hW hθ hD M lam hb hb1 hbs hζ).1
    have hF : DifferentiableAt ℂ F (q ζ) :=
      cepsNormal_actual_entrance_holomorphicAt_markerCurve_negative dom hW hθ hD
        hμ T (by unfold T; fun_prop) hq
        (by rw [htq]; linarith [dom.c₀_pos]) ((le_max_left _ _).trans hl) hre
    have hdq : DifferentiableAt ℂ q ζ := by unfold q cepsComplexScaledDiscount; fun_prop
    exact ((hF.comp ζ hdq).const_mul (b : ℂ)).differentiableWithinAt
  apply hd.congr
  intro ζ hζ
  have hq := (cepsScaledTrueFrequency_discount_disc dom hW hθ hD M lam (by simp) hb hbs
    (ball_subset_ball (trueEntranceFrequencyRadius_le dom) hζ)).1.le
  simpa only [F, q, μ, l, htq, ofReal_mul, ofReal_div, ofReal_add, ofReal_one] using!
    cepsScaledTrueEntrance_eq_actual_on_discount_disc dom hW hθ hD hb hμ hq

include hW hθ hD in
theorem cepsScaledTrueEntrance_zero_frequency_bound (M lam : ℝ) {b : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam 0))
    {ζ : ℂ} (hζ : ζ ∈ ball 0 dom.trueEntranceFrequencyRadius) :
    ‖cepsScaledTrueEntrance dom ρW lam ζ b‖ ≤ 9 * dom.normalNegativeEntranceBound / b := by
  obtain ⟨hμ, _, _, _, hwlo, hwhi, hl⟩ :=
    cepsScaledTrueFrequency_curve_bounds dom hW hθ hD M lam (by simp) hb hbs
  obtain ⟨hq, hre⟩ := cepsScaledTrueFrequency_discount_disc dom hW hθ hD M lam (by simp) hb hbs
    (ball_subset_ball (trueEntranceFrequencyRadius_le dom) hζ)
  obtain ⟨ht, htre⟩ := cepsScaledTrueEntrance_frequency_marker_bounds dom hW hθ hD M lam hb hb1 hbs hζ
  have hH := cepsNormal_actual_regularEntrance_bound_markerSlack dom hW hθ hD
    hμ hq.le ht.le htre hl hre
  rw [cepsScaledTrueEntrance_eq_actual_on_discount_disc dom hW hθ hD hb hμ hq.le,
    norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hb]
  have hH' : ‖(cepsWHNormalData D θ ρW (b * lam) (cepsComplexScaledDiscount lam ζ b)).regularEntrance
      (dom.canonL ρW) (b * lam) (cepsComplexScaledDiscount lam ζ b)
        ((1 + b * lam) / b) ((b : ℂ) ^ 2 * ζ)‖ ≤
      dom.normalNegativeEntranceBound * (1 + (1 + b * lam) / b) ^ 2 := by
    simpa only [ofReal_mul, ofReal_div, ofReal_add, ofReal_one] using! hH
  have hC : 0 ≤ dom.normalNegativeEntranceBound :=
    nonneg_of_mul_nonneg_left ((norm_nonneg _).trans hH)
      (sq_pos_of_pos (by
        have hw : 0 < 1 + b * lam := by linarith
        exact add_pos_of_pos_of_nonneg (by norm_num) (div_pos hw hb).le))
  have hl0 : 0 ≤ 1 + (1 + b * lam) / b := by positivity
  have hlb : 1 + (1 + b * lam) / b ≤ 3 / b := by
    apply (le_div_iff₀ hb).mpr
    rw [add_mul, div_mul_cancel₀ _ hb.ne']
    linarith
  calc
    _ ≤ b * (dom.normalNegativeEntranceBound * (1 + (1 + b * lam) / b) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hb.le
      simpa only [ofReal_mul, ofReal_div, ofReal_add, ofReal_one] using! hH'
    _ ≤ b * (dom.normalNegativeEntranceBound * (3 / b) ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hl0 hlb 2) hC) hb.le
    _ = _ := by field_simp; ring

end PGM
