import PLAStochastic.Index.CEPS.Scaled.FrequencyRootBudget

/-! # A fixed physical scale disc paying common complex frequency neighborhoods -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.trueFrequencyScaleBase {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (M : ℝ) : ℝ :=
  min (dom.truePairScaleBase M)
    (1 / (4 * (1 + max dom.normalNegativeWidth dom.normalCoarseWidth)))

def CepsCanonDomain.trueFrequencyScaleRadius {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (M lam : ℝ) (z : ℂ) : ℝ :=
  dom.trueFrequencyScaleBase M / (1 + |lam| + Real.sqrt ‖z‖)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem trueFrequencyScaleRadius_pos {M : ℝ} (hM : 0 ≤ M) (lam : ℝ) (z : ℂ) :
    0 < dom.trueFrequencyScaleRadius M lam z := by
  have := truePairScaleBase_pos dom hW hθ hD hM
  have hT := (cepsNormal_width_properties dom hW hθ hD (l := dom.normalWidthThreshold) le_rfl).1
  have hC : dom.normalWidthThreshold ≤ dom.normalCoarseWidth := le_max_left _ _
  have hL := le_max_right dom.normalNegativeWidth dom.normalCoarseWidth
  have hL0 : 0 < max dom.normalNegativeWidth dom.normalCoarseWidth := hT.trans_le (hC.trans hL)
  unfold CepsCanonDomain.trueFrequencyScaleRadius CepsCanonDomain.trueFrequencyScaleBase
  positivity

theorem trueFrequencyScaleRadius_le (M lam : ℝ) (z : ℂ) :
    dom.trueFrequencyScaleRadius M lam z ≤ dom.truePairScaleRadius M lam z :=
  div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)

include hW hθ hD in
theorem cepsScaledTrueFrequency_width (M lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : 0 < b) (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z)) :
    max dom.normalNegativeWidth dom.normalCoarseWidth ≤ (1 + b * lam) / b := by
  let L := max dom.normalNegativeWidth dom.normalCoarseWidth
  have hT := (cepsNormal_width_properties dom hW hθ hD (l := dom.normalWidthThreshold) le_rfl).1
  have hC : dom.normalWidthThreshold ≤ dom.normalCoarseWidth := le_max_left _ _
  have hCL : dom.normalCoarseWidth ≤ L := le_max_right _ _
  have hL : 0 < L := lt_of_lt_of_le (hT.trans_le hC) hCL
  have hsmall := cepsScaledTruePair_drift_le_half dom hW hθ hD M lam hz
    (ball_subset_ball (trueFrequencyScaleRadius_le dom M lam z) hbs)
  have hn := mem_ball_zero_iff.mp hbs
  rw [norm_real, Real.norm_eq_abs, abs_of_pos hb] at hn
  have ht := (lt_div_iff₀ (by positivity : 0 < 1 + |lam| + Real.sqrt ‖z‖)).mp hn
  have hbase : dom.trueFrequencyScaleBase M ≤ 1 / (4 * (1 + L)) := min_le_right _ _
  have hbL : b ≤ 1 / (4 * (1 + L)) := by
    nlinarith [abs_nonneg lam, Real.sqrt_nonneg ‖z‖]
  have hmul := (le_div_iff₀ (by positivity : 0 < 4 * (1 + L))).mp hbL
  exact (le_div_iff₀ hb).mpr (by nlinarith [neg_le_abs (b * lam)])

include hD in
theorem cepsComplexScaledDiscount_maps_frequency_ball {b lam : ℝ} (hb : 0 < b)
    (hwlo : 1 / 2 ≤ 1 + b * lam) (hwhi : 1 + b * lam ≤ 2) (z : ℂ) :
    MapsTo (fun ζ => cepsComplexScaledDiscount lam ζ b) (ball z dom.scaledFrequencyRadius)
      (ball (cepsComplexScaledDiscount lam z b)
        (dom.normalDiscountRadius / ((1 + b * lam) / b) ^ 2)) := by
  let w := 1 + b * lam
  have hw : 0 < w := by dsimp [w]; linarith
  have ha := cepsNormal_discountRadius_pos dom hD
  have hδ := scaledFrequencyRadius_pos dom hD
  have hpow : w ^ 3 ≤ 8 := by nlinarith [sq_nonneg (w - 2)]
  have hscale : b ^ 2 * w * dom.scaledFrequencyRadius ≤
      dom.normalDiscountRadius / (w / b) ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos (div_pos hw hb))).mpr
    have he : (b ^ 2 * w * dom.scaledFrequencyRadius) * (w / b) ^ 2 =
        w ^ 3 * dom.scaledFrequencyRadius := by field_simp
    rw [he]
    exact (mul_le_mul_of_nonneg_right hpow hδ.le).trans_eq (by
      unfold CepsCanonDomain.scaledFrequencyRadius
      ring)
  intro ζ hζ
  have he : cepsComplexScaledDiscount lam ζ b - cepsComplexScaledDiscount lam z b =
      ((b ^ 2 * w : ℝ) : ℂ) * (ζ - z) := by
    unfold cepsComplexScaledDiscount
    dsimp [w]
    push_cast
    ring
  rw [mem_ball, dist_eq_norm, he, norm_mul, norm_real, Real.norm_eq_abs,
    abs_of_pos (mul_pos (sq_pos_of_pos hb) hw)]
  exact (mul_lt_mul_of_pos_left (by simpa only [dist_eq_norm] using mem_ball.mp hζ)
    (mul_pos (sq_pos_of_pos hb) hw)).trans_le hscale

end PGM
