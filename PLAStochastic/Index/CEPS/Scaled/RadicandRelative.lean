import PLAStochastic.Index.CEPS.Scaled.Radicand
import PLAStochastic.ForMathlib.Analysis.Complex.RightHalfPlaneDisc

/-! # A common complex scale disc for the actual square-root radicand -/

noncomputable section
open Complex MeasureTheory Set Metric
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.scaledRadicandCoeffBound {D θ v : ℝ} (dom : CepsCanonDomain D θ v) : ℝ :=
  1 + dom.μ₀ / 2 + dom.morseMinUnitBound

def CepsCanonDomain.radicandScaleRadius {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (lam : ℝ) : ℝ := dom.minimumScaleRadius lam / (8 * dom.scaledRadicandCoeffBound * (2 * v + 2))

theorem CepsCanonDomain.scaledRadicandCoeffBound_ge_one {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) : 1 ≤ dom.scaledRadicandCoeffBound := by
  have hB : 0 ≤ dom.morseMinUnitBound := by unfold morseMinUnitBound; positivity
  unfold scaledRadicandCoeffBound
  linarith [dom.μ₀_pos]

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledMorseRadicand_zero_coercive (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) :
    0 ≤ (cepsScaledMorseRadicand D θ ρW lam z 0).re ∧
    lam ^ 2 + ‖z‖ ≤ (2 * v + 2) * ‖cepsScaledMorseRadicand D θ ρW lam z 0‖ := by
  let a : ℝ := lam ^ 2 / (2 * cepsStepVar ρW)
  have hV := cepsStepVar_pos hW hθ hD
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have he : (a : ℂ) + z = cepsScaledMorseRadicand D θ ρW lam z 0 := by
    rw [cepsScaledMorseRadicand_zero hW hθ hD]
    dsimp [a]
    push_cast
    ring
  obtain ⟨h1, h2⟩ := norm_nonneg_real_add_ge ha hz
  rw [he] at h1 h2
  have hla : lam ^ 2 = (2 * cepsStepVar ρW) * a := by dsimp [a]; field_simp
  have hlam : lam ^ 2 ≤ (2 * v) * ‖cepsScaledMorseRadicand D θ ρW lam z 0‖ := by
    rw [hla]
    exact mul_le_mul (by linarith [cepsStepVar_le hW]) h1 ha
      (by linarith [CepsCanonDomain.v_pos hW hθ hD])
  refine ⟨?_, by nlinarith⟩
  rw [← he, add_re, ofReal_re]
  linarith

include hW hθ hD in
theorem radicandScaleRadius_budget (lam : ℝ) : 0 < dom.radicandScaleRadius lam ∧
    dom.radicandScaleRadius lam ≤ dom.minimumScaleRadius lam / 2 := by
  have hR := dom.minimumScaleRadius_pos (lam : ℂ)
  have hC := dom.scaledRadicandCoeffBound_ge_one
  have hv := CepsCanonDomain.v_pos hW hθ hD
  have hden : 0 < 8 * dom.scaledRadicandCoeffBound * (2 * v + 2) := by positivity
  refine ⟨div_pos hR hden, ?_⟩
  rw [CepsCanonDomain.radicandScaleRadius, div_le_div_iff₀ hden (by norm_num)]
  have hden2 : 2 ≤ 8 * dom.scaledRadicandCoeffBound * (2 * v + 2) := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ dom.scaledRadicandCoeffBound) hv.le]
  nlinarith [mul_le_mul_of_nonneg_left hden2 hR.le]

include hW hθ hD in
theorem cepsScaledMorseRadicand_relative (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.radicandScaleRadius lam)) :
    ‖cepsScaledMorseRadicand D θ ρW lam z b - cepsScaledMorseRadicand D θ ρW lam z 0‖ ≤
      ‖cepsScaledMorseRadicand D θ ρW lam z 0‖ / 2 := by
  obtain ⟨hd, hm⟩ := cepsScaledMorseRadicand_budget dom hW hθ hD (lam : ℂ) z
  have hR := dom.minimumScaleRadius_pos (lam : ℂ)
  have hC := dom.scaledRadicandCoeffBound_ge_one
  have hv := CepsCanonDomain.v_pos hW hθ hD
  have hbR : b ∈ ball (0 : ℂ) (dom.minimumScaleRadius lam / 2) :=
    ball_subset_ball (radicandScaleRadius_budget dom hW hθ hD lam).2 hb
  have ht := norm_sub_le_of_ball_half hR hd hm hbR (mem_ball_self (half_pos hR))
  rw [sub_zero] at ht
  have hbound : dom.scaledRadicandBound lam z ≤
      dom.scaledRadicandCoeffBound * (lam ^ 2 + ‖z‖) := by
    have hB : 0 ≤ dom.morseMinUnitBound := by unfold CepsCanonDomain.morseMinUnitBound; positivity
    unfold CepsCanonDomain.scaledRadicandBound CepsCanonDomain.scaledRadicandCoeffBound
    rw [norm_real, Real.norm_eq_abs, sq_abs]
    nlinarith [norm_nonneg z, sq_nonneg lam, dom.μ₀_pos]
  have hnorm := (cepsScaledMorseRadicand_zero_coercive hW hθ hD lam hz).2
  have hM := hbound.trans (mul_le_mul_of_nonneg_left hnorm (by linarith :
    0 ≤ dom.scaledRadicandCoeffBound))
  have hden : 0 < 8 * dom.scaledRadicandCoeffBound * (2 * v + 2) := by positivity
  have hn := (le_div_iff₀ hden).mp (mem_ball_zero_iff.mp hb).le
  have hfactor : 4 * dom.scaledRadicandCoeffBound * (2 * v + 2) / dom.minimumScaleRadius lam *
      ‖b‖ ≤ 1 / 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hR]
    linarith
  calc
    _ ≤ 4 * dom.scaledRadicandBound lam z / dom.minimumScaleRadius lam * ‖b‖ := ht
    _ ≤ 4 * (dom.scaledRadicandCoeffBound * ((2 * v + 2) *
        ‖cepsScaledMorseRadicand D θ ρW lam z 0‖)) / dom.minimumScaleRadius lam * ‖b‖ := by gcongr
    _ = (4 * dom.scaledRadicandCoeffBound * (2 * v + 2) / dom.minimumScaleRadius lam * ‖b‖) *
        ‖cepsScaledMorseRadicand D θ ρW lam z 0‖ := by ring
    _ ≤ (1 / 2) * ‖cepsScaledMorseRadicand D θ ρW lam z 0‖ :=
      mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)
    _ = _ := by ring

include hW hθ hD in
theorem cepsScaledMorseRadicand_mem_slitPlane (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    (hne : lam ≠ 0 ∨ z ≠ 0) {b : ℂ} (hb : b ∈ ball (0 : ℂ) (dom.radicandScaleRadius lam)) :
    cepsScaledMorseRadicand D θ ρW lam z b ∈ slitPlane := by
  obtain ⟨hRe, hn⟩ := cepsScaledMorseRadicand_zero_coercive hW hθ hD lam hz
  have hp : 0 < lam ^ 2 + ‖z‖ := by
    rcases hne with hlam | hz'
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hlam) (norm_nonneg _)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (norm_pos_iff.mpr hz')
  have hbase : 0 < ‖cepsScaledMorseRadicand D θ ρW lam z 0‖ := by
    have hv := CepsCanonDomain.v_pos hW hθ hD
    by_contra h
    have hzero : ‖cepsScaledMorseRadicand D θ ρW lam z 0‖ = 0 := le_antisymm (not_lt.mp h) (norm_nonneg _)
    rw [hzero, mul_zero] at hn
    linarith
  exact mem_slitPlane_of_norm_sub_lt hRe
    ((cepsScaledMorseRadicand_relative dom hW hθ hD lam hz hb).trans_lt (half_lt_self hbase))

end PGM
