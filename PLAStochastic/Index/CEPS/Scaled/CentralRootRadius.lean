import PLAStochastic.Index.CEPS.Scaled.BoundedSpatialSlope
import PLAStochastic.Index.CEPS.Scaled.MorseChartJoint
import PLAStochastic.Index.CEPS.Scaled.MinimumBudget

/-! # Class-controlled small signed-root and scale discs -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.centralDriftRadius {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  min 1 (dom.boundedSpatialRootRadius N M / (8 * (1 + 2 / cepsVarLo D)))

def CepsCanonDomain.centralCoordinateRadius {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  min 1 (dom.boundedSpatialRootRadius N M / (8 * (1 + cepsChartK D)))

def CepsCanonDomain.centralScaleRadius {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  min (min dom.μ₀ dom.rmax /
    (8 * (1 + dom.centralDriftRadius N M + dom.centralCoordinateRadius N M)))
    (min (dom.c₀ / 4) (min (1 / 2) (min (1 / (4 * (1 + dom.canonSurrogatePiBound N M)))
      (dom.q₀ / (8 * (1 + dom.morseMinUnitBound + dom.centralCoordinateRadius N M ^ 2))))))

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem centralDriftRadius_pos (N : ℕ) (M : ℝ) : 0 < dom.centralDriftRadius N M := by
  unfold CepsCanonDomain.centralDriftRadius
  exact lt_min (by norm_num) (div_pos (boundedSpatialRootRadius_pos dom hW hθ hD N M)
    (by have := cepsVarLo_pos hD; positivity))

include hW hθ hD in
theorem centralCoordinateRadius_pos (N : ℕ) (M : ℝ) : 0 < dom.centralCoordinateRadius N M := by
  unfold CepsCanonDomain.centralCoordinateRadius
  exact lt_min (by norm_num) (div_pos (boundedSpatialRootRadius_pos dom hW hθ hD N M)
    (by have := cepsChartK_pos hD; positivity))

include hW hθ hD in
theorem centralScaleRadius_pos (N : ℕ) (M : ℝ) : 0 < dom.centralScaleRadius N M := by
  have := centralDriftRadius_pos dom hW hθ hD N M
  have := centralCoordinateRadius_pos dom hW hθ hD N M
  have := CepsCanonDomain.v_pos hW hθ hD
  have := cepsVarLo_pos hD
  have := dom.μ₀_pos
  have := dom.rmax_pos
  have := dom.c₀_pos
  have := dom.q₀_pos
  unfold CepsCanonDomain.centralScaleRadius CepsCanonDomain.morseMinUnitBound
    CepsCanonDomain.canonSurrogatePiBound
  positivity

include hW hθ hD in
theorem cepsScaledCentral_chart_bounds (N : ℕ) (M : ℝ) {lam r b : ℂ}
    (hlam : ‖lam‖ ≤ dom.centralDriftRadius N M)
    (hr : ‖r‖ ≤ dom.centralCoordinateRadius N M)
    (hb : b ∈ ball (0 : ℂ) (dom.centralScaleRadius N M)) :
    b ∈ ball (0 : ℂ) (dom.scaledMorseRadius lam r) ∧
      ‖b * lam‖ < dom.μ₀ / 8 ∧ ‖b * r‖ < dom.rmax ∧
      ‖cepsScaledMorseChart D θ ρW lam r b‖ ≤ dom.boundedSpatialRootRadius N M / 4 := by
  have hL := centralDriftRadius_pos dom hW hθ hD N M
  have hR := centralCoordinateRadius_pos dom hW hθ hD N M
  have hden : 0 < 1 + dom.centralDriftRadius N M + dom.centralCoordinateRadius N M := by positivity
  have hb0 := mem_ball_zero_iff.mp hb
  have hb1 := hb0.trans_le (min_le_left _ _)
  have hbmul := (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 8) hden)).mp hb1
  have hcoord : ‖b‖ * (1 + ‖lam‖ + ‖r‖) < min dom.μ₀ dom.rmax := by
    have ht := mul_le_mul_of_nonneg_left (by linarith : 1 + ‖lam‖ + ‖r‖ ≤
      1 + dom.centralDriftRadius N M + dom.centralCoordinateRadius N M) (norm_nonneg b)
    nlinarith [mul_nonneg (norm_nonneg b) hden.le]
  have hchart : b ∈ ball (0 : ℂ) (dom.scaledMorseRadius lam r) := by
    apply mem_ball_zero_iff.mpr
    exact (lt_div_iff₀ (by positivity : 0 < 1 + ‖lam‖ + ‖r‖)).mpr hcoord
  have hmu : ‖b * lam‖ < dom.μ₀ / 8 := by
    rw [norm_mul]
    have ht := mul_le_mul_of_nonneg_left (by linarith [norm_nonneg r] : ‖lam‖ ≤
      1 + dom.centralDriftRadius N M + dom.centralCoordinateRadius N M) (norm_nonneg b)
    have hm := min_le_left dom.μ₀ dom.rmax
    nlinarith
  have hbr : ‖b * r‖ < dom.rmax := by
    rw [norm_mul]
    have ht := mul_le_mul_of_nonneg_left (by linarith [norm_nonneg lam] : ‖r‖ ≤
      1 + ‖lam‖ + ‖r‖) (norm_nonneg b)
    exact ht.trans_lt (hcoord.trans_le (min_le_right _ _))
  have hA : 0 < 2 / cepsVarLo D := div_pos (by norm_num) (cepsVarLo_pos hD)
  have hK := cepsChartK_pos hD
  have hld := (le_div_iff₀ (by positivity : 0 < 8 * (1 + 2 / cepsVarLo D))).mp
    (show dom.centralDriftRadius N M ≤ dom.boundedSpatialRootRadius N M /
      (8 * (1 + 2 / cepsVarLo D)) from min_le_right _ _)
  have hrd := (le_div_iff₀ (by positivity : 0 < 8 * (1 + cepsChartK D))).mp
    (show dom.centralCoordinateRadius N M ≤ dom.boundedSpatialRootRadius N M /
      (8 * (1 + cepsChartK D)) from min_le_right _ _)
  have ha := mul_le_mul_of_nonneg_left hlam hA.le
  have hk := mul_le_mul_of_nonneg_left hr hK.le
  have hsize : dom.scaledMorseBound lam r ≤ dom.boundedSpatialRootRadius N M / 4 := by
    unfold CepsCanonDomain.scaledMorseBound
    nlinarith
  exact ⟨hchart, hmu, hbr, ((cepsScaledMorseChart_budget dom hW hθ hD lam r).2 b hchart).trans hsize⟩

end PGM
