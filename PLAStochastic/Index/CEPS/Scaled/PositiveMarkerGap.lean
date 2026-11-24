import PLAStochastic.Index.CEPS.Scaled.PairRootDirections

/-! # A uniform half-line marker gap on the positive subtraction range -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.positiveMarkerGapLower {D θ v : ℝ} (_dom : CepsCanonDomain D θ v) : ℝ :=
  1 / (64 * Real.sqrt v * Real.sqrt (4 * v + 4))

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hD in
theorem cepsScaledWidth_norm_le_two (N : ℕ) (M lam : ℝ) {z b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    ‖(1 : ℂ) + b * lam‖ ≤ 2 := by
  have hC : 0 ≤ dom.actualScaledRootBound lam z := by
    unfold CepsCanonDomain.actualScaledRootBound
    have := cepsVarLo_pos hD
    have := cepsChartK_pos hD
    have := Real.sqrt_nonneg (2 * (‖z‖ + lam ^ 2 / (2 * cepsVarLo D)))
    positivity
  have ht := entranceScaleCurve_product_bound dom hD N M lam hb
  have hbase : dom.canonScaleBase ≤ 1 := min_le_left _ _
  have hu : ‖b * (lam : ℂ)‖ ≤ 1 := by
    rw [norm_mul, norm_real, Real.norm_eq_abs]
    nlinarith [abs_nonneg lam, norm_nonneg b, Real.sqrt_nonneg ‖z‖]
  exact (norm_add_le (1 : ℂ) (b * lam)).trans (by rw [norm_one]; linarith)

include hW hθ hD in
theorem positiveMarkerGapLower_pos : 0 < dom.positiveMarkerGapLower := by
  have := CepsCanonDomain.v_pos hW hθ hD
  unfold CepsCanonDomain.positiveMarkerGapLower
  positivity

include hW hθ hD in
theorem cepsScaledPositiveMarkerGap_norm_lower (N : ℕ) (M lam : ℝ) (hlam : 1 ≤ lam)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.pairPolynomialScaleBase N M / (1 + |lam| + Real.sqrt ‖z‖))) :
    dom.positiveMarkerGapLower ≤ ‖b * z - cepsScaledSignedRoot D θ ρW lam z (-1) b‖ := by
  let R := ‖cepsScaledRootCoordinate D θ ρW lam z b‖
  let δ := b * z - cepsScaledSignedRoot D θ ρW lam z (-1) b
  let w : ℂ := 1 + b * lam
  have hRadii := pairPolynomialScaleRadius_le dom hW hθ hD N M lam z
  have hbP := ball_subset_ball hRadii.1 hb
  have hbE := ball_subset_ball hRadii.2 hb
  have hbC := (complexDirectionScaleCurve_bounds dom N M lam (ball_subset_ball (min_le_left _ _) hbP)).1
  have hd := cepsScaledRootCoordinate_drift_le dom hW hθ hD lam hz hbC
  have hdirs := (cepsScaledPairRoot_positive_directions dom hW hθ hD N M lam (by linarith) hz hb).1
  have hr : R / (32 * Real.sqrt v) ≤ (δ * w).re := by
    simpa only [R, δ, w, sub_eq_add_neg, add_comm] using hdirs
  have hw := cepsScaledWidth_norm_le_two dom hD N M lam hbE
  have hn : R / (32 * Real.sqrt v) ≤ ‖δ‖ * 2 := hr.trans ((re_le_norm _).trans (by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hw (norm_nonneg _)))
  have hv := Real.sqrt_pos.mpr (CepsCanonDomain.v_pos hW hθ hD)
  have hs := Real.sqrt_pos.mpr (show 0 < 4 * v + 4 by linarith [CepsCanonDomain.v_pos hW hθ hD])
  have hone : 1 / Real.sqrt (4 * v + 4) ≤ R := (div_le_iff₀ hs).mpr (by
    dsimp [R]
    nlinarith [le_abs_self lam])
  calc
    _ = ((1 / Real.sqrt (4 * v + 4)) / (32 * Real.sqrt v)) / 2 := by
      unfold CepsCanonDomain.positiveMarkerGapLower
      ring
    _ ≤ (R / (32 * Real.sqrt v)) / 2 :=
      div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hone (by positivity)) (by norm_num)
    _ ≤ ‖δ‖ := by linarith

include hW hθ hD in
theorem cepsScaledPositiveMarkerGap_ne_zero (N : ℕ) (M lam : ℝ) (hlam : 1 ≤ lam)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.pairPolynomialScaleBase N M / (1 + |lam| + Real.sqrt ‖z‖))) :
    b * z ≠ cepsScaledSignedRoot D θ ρW lam z (-1) b :=
  sub_ne_zero.mp (norm_pos_iff.mp ((positiveMarkerGapLower_pos dom hW hθ hD).trans_le
    (cepsScaledPositiveMarkerGap_norm_lower dom hW hθ hD N M lam hlam hz hb)))

end PGM
