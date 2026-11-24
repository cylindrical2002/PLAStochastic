import PLAStochastic.Index.CEPS.Scaled.BridgePolynomialRadius
import PLAStochastic.Index.CEPS.Scaled.EntranceScaleCurve
import PLAStochastic.Index.CEPS.Scaled.CombinedRootWidth

/-! # A reciprocal polynomial disc absorbing the scaled marker -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

private theorem marker_scale_identity {a c R : ℝ} (ha : a ≠ 0) (hc : c ≠ 0) :
    (1 / (256 * a * c)) * (c * R) * 2 = R / (128 * a) := by
  field_simp
  ring

def CepsCanonDomain.pairMarkerScaleBase {D θ v : ℝ} (_dom : CepsCanonDomain D θ v) : ℝ :=
  1 / (256 * Real.sqrt v * Real.sqrt (4 * v + 4))

def CepsCanonDomain.pairPolynomialScaleBase {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  min (dom.bridgePolynomialScaleBase N M)
    (min (dom.canonPolynomialScaleBase / 8) dom.pairMarkerScaleBase)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem pairPolynomialScaleBase_pos (N : ℕ) (M : ℝ) :
    0 < dom.pairPolynomialScaleBase N M := by
  have := CepsCanonDomain.v_pos hW hθ hD
  have := bridgePolynomialScaleBase_pos dom hW hθ hD N M
  have := (canonPolynomialScale_constants dom hW hθ hD).2.2.2
  unfold CepsCanonDomain.pairPolynomialScaleBase CepsCanonDomain.pairMarkerScaleBase
  positivity

include hW hθ hD in
theorem pairPolynomialScaleRadius_le (N : ℕ) (M lam : ℝ) (z : ℂ) :
    (dom.pairPolynomialScaleBase N M / (1 + |lam| + Real.sqrt ‖z‖) ≤
      dom.positiveCorrectionScaleRadius N M lam z) ∧
    (dom.pairPolynomialScaleBase N M / (1 + |lam| + Real.sqrt ‖z‖) ≤
      dom.entranceScaleRadius N M lam z) := by
  have hX : 0 ≤ 1 + |lam| + Real.sqrt ‖z‖ := by positivity
  have hb : dom.pairPolynomialScaleBase N M / (1 + |lam| + Real.sqrt ‖z‖) ≤
      dom.positiveCorrectionScaleRadius N M lam z :=
    (div_le_div_of_nonneg_right (min_le_left _ _) hX).trans
    (bridgePolynomialScaleRadius_le dom hW hθ hD N M lam z)
  refine ⟨hb, le_min ?_ ?_⟩
  · exact hb.trans ((min_le_left _ _).trans (min_le_left _ _))
  · calc
      _ ≤ (dom.canonPolynomialScaleBase / 8) / (1 + |lam| + Real.sqrt ‖z‖) :=
        div_le_div_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) hX
      _ = (dom.canonPolynomialScaleBase / (1 + |lam| + Real.sqrt ‖z‖)) / 8 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (canonPolynomialScaleRadius_le dom hW hθ hD lam z) (by norm_num)

include hW hθ hD in
theorem cepsScaledRootCoordinate_frequency_le (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z / 2)) :
    Real.sqrt ‖z‖ ≤ Real.sqrt (4 * v + 4) * ‖cepsScaledRootCoordinate D θ ρW lam z b‖ := by
  have hsub : dom.canonScaleRadius lam z / 2 ≤ dom.radicandScaleRadius lam / 2 :=
    div_le_div_of_nonneg_right ((min_le_left _ _).trans (min_le_left _ _)) (by norm_num)
  have hc := cepsScaledRootCoordinate_complex_coercive dom hW hθ hD lam hz (ball_subset_ball hsub hb)
  have hv : 0 ≤ 4 * v + 4 := by linarith [CepsCanonDomain.v_pos hW hθ hD]
  apply (pow_le_pow_iff_left₀ (Real.sqrt_nonneg _) (by positivity) (by norm_num : 2 ≠ 0)).mp
  rw [Real.sq_sqrt (norm_nonneg z), mul_pow, Real.sq_sqrt hv]
  linarith [sq_nonneg lam]

include hW hθ hD in
theorem cepsScaledMarker_width_small (N : ℕ) (M lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.pairPolynomialScaleBase N M / (1 + |lam| + Real.sqrt ‖z‖))) :
    ‖(b * z) * (1 + b * lam)‖ ≤
      ‖cepsScaledRootCoordinate D θ ρW lam z b‖ / (128 * Real.sqrt v) := by
  have hbP := ball_subset_ball (pairPolynomialScaleRadius_le dom hW hθ hD N M lam z).1 hb
  have hbE := ball_subset_ball (pairPolynomialScaleRadius_le dom hW hθ hD N M lam z).2 hb
  have hbD := ball_subset_ball (min_le_left _ _) hbP
  obtain ⟨hbC, _, _⟩ := complexDirectionScaleCurve_bounds dom N M lam hbD
  have hf := cepsScaledRootCoordinate_frequency_le dom hW hθ hD lam hz hbC
  have ht : ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) < dom.pairPolynomialScaleBase N M :=
    (lt_div_iff₀ (by positivity : 0 < 1 + |lam| + Real.sqrt ‖z‖)).mp (mem_ball_zero_iff.mp hb)
  have hB : dom.pairPolynomialScaleBase N M ≤ dom.pairMarkerScaleBase :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hbs : ‖b‖ * Real.sqrt ‖z‖ ≤ dom.pairMarkerScaleBase := by
    nlinarith [abs_nonneg lam, norm_nonneg b]
  have hC : 0 ≤ dom.actualScaledRootBound lam z := by
    unfold CepsCanonDomain.actualScaledRootBound
    have := cepsVarLo_pos hD
    have := cepsChartK_pos hD
    have := Real.sqrt_nonneg (2 * (‖z‖ + lam ^ 2 / (2 * cepsVarLo D)))
    positivity
  have hprod := entranceScaleCurve_product_bound dom hD N M lam hbE
  have hbase : dom.canonScaleBase ≤ 1 := min_le_left _ _
  have hu : ‖b * (lam : ℂ)‖ ≤ 1 := by
    rw [norm_mul, norm_real, Real.norm_eq_abs]
    nlinarith [abs_nonneg lam, norm_nonneg b, Real.sqrt_nonneg ‖z‖]
  have hw : ‖(1 : ℂ) + b * lam‖ ≤ 2 := by
    have hn := norm_add_le (1 : ℂ) (b * lam)
    rw [norm_one] at hn
    linarith
  have hv := Real.sqrt_pos.mpr (CepsCanonDomain.v_pos hW hθ hD)
  have hs : 0 < Real.sqrt (4 * v + 4) := Real.sqrt_pos.mpr (by linarith [CepsCanonDomain.v_pos hW hθ hD])
  have hB0 : 0 ≤ dom.pairMarkerScaleBase := by unfold CepsCanonDomain.pairMarkerScaleBase; positivity
  rw [norm_mul, norm_mul, ← Real.mul_self_sqrt (norm_nonneg z)]
  calc
    _ = (‖b‖ * Real.sqrt ‖z‖) * Real.sqrt ‖z‖ * ‖(1 : ℂ) + b * lam‖ := by ring
    _ ≤ dom.pairMarkerScaleBase * (Real.sqrt (4 * v + 4) * ‖cepsScaledRootCoordinate D θ ρW lam z b‖) * 2 :=
      mul_le_mul (mul_le_mul hbs hf (Real.sqrt_nonneg _) hB0) hw (norm_nonneg _) (by positivity)
    _ = _ := by
      unfold CepsCanonDomain.pairMarkerScaleBase
      exact marker_scale_identity hv.ne' hs.ne'

end PGM
