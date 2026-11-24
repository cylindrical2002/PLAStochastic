import PLAStochastic.Index.CEPS.Scaled.TruePositiveDerivative

/-! # Actual entrance half-line subtraction through marker collisions -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def cepsScaledTrueHalfEntrance {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (lam : ℝ) (z : ℂ) (b : ℝ) : ℂ :=
  cepsScaledTrueMarkPrefactor dom ρW lam z b /
    ((b : ℂ) * z - cepsScaledSignedRoot D θ ρW lam z (-1) b)

def cepsScaledTrueEntranceCorrection {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (lam : ℝ) (z : ℂ) (b : ℝ) : ℂ :=
  cepsScaledTrueEntrance dom ρW lam z b - cepsScaledTrueHalfEntrance dom ρW lam z b

def CepsCanonDomain.trueHalfEntranceConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) : ℝ :=
  (Real.exp dom.normalLogBound * (4 / cepsVarLo D)) / dom.positiveMarkerGapLower

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem trueHalfEntranceConstant_pos : 0 < dom.trueHalfEntranceConstant := by
  have := cepsVarLo_pos hD
  have := positiveMarkerGapLower_pos dom hW hθ hD
  unfold CepsCanonDomain.trueHalfEntranceConstant
  positivity

include hW hθ hD in
theorem cepsScaledTrueHalfEntrance_positive_budget (M lam : ℝ) (hlam : 1 ≤ lam)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDenominatorScaleRadius M lam z)) :
    ‖cepsScaledTrueHalfEntrance dom ρW lam z b‖ ≤ dom.trueHalfEntranceConstant := by
  have hbP : (b : ℂ) ∈ ball (0 : ℂ) (dom.pairPolynomialScaleBase 0 M /
      (1 + |lam| + Real.sqrt ‖z‖)) :=
    ball_subset_ball (div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)) hb
  have hbE := ball_subset_ball (trueDenominatorScaleRadius_le dom hW hθ hD M lam z) hb
  have hP := cepsScaledTrueMarkPrefactor_budget dom hW hθ hD 0 M lam hz hbE
  have hgap := cepsScaledPositiveMarkerGap_norm_lower dom hW hθ hD 0 M lam hlam hz hbP
  have hl := positiveMarkerGapLower_pos dom hW hθ hD
  have hi : ‖(((b : ℂ) * z - cepsScaledSignedRoot D θ ρW lam z (-1) b)⁻¹)‖ ≤
      dom.positiveMarkerGapLower⁻¹ := by
    rw [norm_inv]
    exact (inv_le_inv₀ (hl.trans_le hgap) hl).mpr hgap
  unfold cepsScaledTrueHalfEntrance
  rw [div_eq_mul_inv, norm_mul]
  exact (mul_le_mul hP hi (norm_nonneg _) ((norm_nonneg _).trans hP)).trans_eq
    (by unfold CepsCanonDomain.trueHalfEntranceConstant; ring)

include hW hθ hD in
theorem cepsScaledTrueEntranceCorrection_eq_firstSlope {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m) (lam : ℝ)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDenominatorScaleRadius M lam z))
    (ht : (b : ℂ) * z ≠ cepsScaledSignedRoot D θ ρW lam z (-1) b) :
    cepsScaledTrueEntranceCorrection dom ρW lam z b =
      -cepsScaledTrueHalfEntrance dom ρW lam z b *
        dslope (cepsScaledTrueG dom ρW lam z b)
          (cepsScaledSignedRoot D θ ρW lam z 1 b) ((b : ℂ) * z) /
            cepsScaledTrueDenominator dom ρW lam z b := by
  let G := cepsScaledTrueG dom ρW lam z b
  let p := cepsScaledSignedRoot D θ ρW lam z 1 (b : ℂ)
  let a := cepsScaledSignedRoot D θ ρW lam z (-1) (b : ℂ)
  let t := (b : ℂ) * z
  let R := dom.entranceSpatialScaleRadius lam z
  have hbE := ball_subset_ball (trueDenominatorScaleRadius_le dom hW hθ hD M lam z) hb
  have hG := cepsScaledTrueG_spatial_differentiableOn dom hW hθ hD 0 M lam hz hbE
  have hp := (hG p (entranceScaleCurve_roots_mem dom hW hθ hD 0 M lam hz
    (by norm_num : ‖(1 : ℂ)‖ ≤ 1) hbE)).differentiableAt
      (isOpen_ball.mem_nhds (entranceScaleCurve_roots_mem dom hW hθ hD 0 M lam hz
        (by norm_num : ‖(1 : ℂ)‖ ≤ 1) hbE))
  have ha := (hG a (entranceScaleCurve_roots_mem dom hW hθ hD 0 M lam hz
    (by norm_num : ‖(-1 : ℂ)‖ ≤ 1) hbE)).differentiableAt
      (isOpen_ball.mem_nhds (entranceScaleCurve_roots_mem dom hW hθ hD 0 M lam hz
        (by norm_num : ‖(-1 : ℂ)‖ ≤ 1) hbE))
  have hswap := cepsNormal_second_dslope_swap hp ha t
  have hid := sub_smul_dslope (dslope G p) a t
  rw [smul_eq_mul, ← hswap, cepsNormal_dslope_swap G p a] at hid
  change (t - a) * cepsScaledTrueEntranceNumerator dom ρW lam z b =
    dslope G p t - cepsScaledTrueDenominator dom ρW lam z b at hid
  have hS0 := cepsScaledTrueDenominator_ne_zero dom hW hθ hD hf hη hM hm lam hz hb
  have ht0 : t - a ≠ 0 := sub_ne_zero.mpr ht
  unfold cepsScaledTrueEntranceCorrection cepsScaledTrueEntrance cepsScaledTrueHalfEntrance
  change -_ * cepsScaledTrueEntranceNumerator dom ρW lam z b / _ - _ / (t - a) =
    -(_ / (t - a)) * dslope G p t / _
  field_simp
  linear_combination -cepsScaledTrueMarkPrefactor dom ρW lam z b * hid

end PGM
