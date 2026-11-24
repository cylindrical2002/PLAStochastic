import PLAStochastic.Index.CEPS.Scaled.CoordinateBudgets

/-! # A class-uniform reciprocal polynomial radius for canonical scale charts -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.scaledRootPolynomialConstant {D θ v : ℝ} (dom : CepsCanonDomain D θ v) : ℝ :=
  2 / cepsVarLo D + cepsChartK D * dom.scaledCoordinateRatioBound

def CepsCanonDomain.radicandPolynomialScaleBase {D θ v : ℝ} (dom : CepsCanonDomain D θ v) : ℝ :=
  dom.μ₀ / (16 * dom.scaledRadicandCoeffBound * (2 * v + 2))

def CepsCanonDomain.actualRootPolynomialScaleBase {D θ v : ℝ} (dom : CepsCanonDomain D θ v) : ℝ :=
  min dom.radicandPolynomialScaleBase (dom.rmax / (4 * (1 + dom.scaledCoordinateRatioBound)))

def CepsCanonDomain.canonPolynomialScaleBase {D θ v : ℝ} (dom : CepsCanonDomain D θ v) : ℝ :=
  min dom.actualRootPolynomialScaleBase (dom.canonScaleBase / (1 + dom.scaledRootPolynomialConstant))

private theorem ratio_lower_of_denominator_upper {c B K x y : ℝ}
    (hc : 0 ≤ c) (hx : 0 < x) (hy : 0 < y) (_hK : 0 < K)
    (hB : B ≤ c / K) (hden : y ≤ K * x) : B / x ≤ c / y := by
  calc
    _ ≤ (c / K) / x := div_le_div_of_nonneg_right hB hx.le
    _ = c / (K * x) := by rw [div_div]
    _ ≤ c / y := div_le_div_of_nonneg_left hc hy hden

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem canonPolynomialScale_constants :
    0 ≤ dom.scaledRootPolynomialConstant ∧ 0 < dom.radicandPolynomialScaleBase ∧
      0 < dom.actualRootPolynomialScaleBase ∧ 0 < dom.canonPolynomialScaleBase := by
  have hvl := cepsVarLo_pos hD
  have hv := CepsCanonDomain.v_pos hW hθ hD
  have hCK := cepsChartK_pos hD
  have hA : 0 ≤ dom.scaledCoordinateRatioBound := Real.sqrt_nonneg _
  have hC : 0 < dom.scaledRadicandCoeffBound := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) dom.scaledRadicandCoeffBound_ge_one
  have hroot : 0 ≤ dom.scaledRootPolynomialConstant := by unfold CepsCanonDomain.scaledRootPolynomialConstant; positivity
  have hrad : 0 < dom.radicandPolynomialScaleBase := by
    unfold CepsCanonDomain.radicandPolynomialScaleBase
    exact div_pos dom.μ₀_pos (by positivity)
  have har : 0 < dom.actualRootPolynomialScaleBase := lt_min hrad (div_pos dom.rmax_pos (by positivity))
  have hcan : 0 < dom.canonScaleBase := by
    unfold CepsCanonDomain.canonScaleBase
    have := dom.μ₀_pos
    have := dom.q₀_pos
    have := dom.c₀_pos
    positivity
  exact ⟨hroot, hrad, har, lt_min har (div_pos hcan (by positivity))⟩

include hW hθ hD in
theorem scaledRootCoordinateBound_le_polynomial (lam : ℝ) (z : ℂ) :
    dom.scaledRootCoordinateBound lam z ≤
      dom.scaledCoordinateRatioBound * (1 + |lam| + Real.sqrt ‖z‖) := by
  have hA : 0 ≤ dom.scaledCoordinateRatioBound := Real.sqrt_nonneg _
  exact (scaledRootCoordinateBound_le_lower dom hW hθ hD lam z).trans
    (mul_le_mul_of_nonneg_left
      (by linarith [scaledCoordinateLower_le_drift_frequency dom hW hθ hD lam z]) hA)

include hW hθ hD in
theorem actualScaledRootBound_le_polynomial (lam : ℝ) (z : ℂ) :
    dom.actualScaledRootBound lam z ≤
      dom.scaledRootPolynomialConstant * (1 + |lam| + Real.sqrt ‖z‖) := by
  have hvl := cepsVarLo_pos hD
  have hCK := (cepsChartK_pos hD).le
  have hS := mul_le_mul_of_nonneg_left (scaledRootCoordinateBound_le_polynomial dom hW hθ hD lam z) hCK
  have hl : |lam| ≤ 1 + |lam| + Real.sqrt ‖z‖ := by linarith [Real.sqrt_nonneg ‖z‖]
  have hL := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 2 / cepsVarLo D)
  change 2 / cepsVarLo D * |lam| + cepsChartK D * dom.scaledRootCoordinateBound lam z ≤
    (2 / cepsVarLo D + cepsChartK D * dom.scaledCoordinateRatioBound) * (1 + |lam| + Real.sqrt ‖z‖)
  nlinarith

include hW hθ hD in
theorem radicandPolynomialScaleRadius_le (lam : ℝ) (z : ℂ) :
    dom.radicandPolynomialScaleBase / (1 + |lam| + Real.sqrt ‖z‖) ≤ dom.radicandScaleRadius lam := by
  have hR := (canonPolynomialScale_constants dom hW hθ hD).2.1.le
  have he : dom.radicandScaleRadius lam = dom.radicandPolynomialScaleBase / (1 + |lam|) := by
    unfold CepsCanonDomain.radicandScaleRadius CepsCanonDomain.minimumScaleRadius
      CepsCanonDomain.radicandPolynomialScaleBase
    rw [norm_real, Real.norm_eq_abs]
    simp only [div_div]
    congr 1
    ring
  rw [he]
  exact div_le_div_of_nonneg_left hR (by positivity) (by linarith [Real.sqrt_nonneg ‖z‖])

include hW hθ hD in
theorem actualRootPolynomialScaleRadius_le (lam : ℝ) (z : ℂ) :
    dom.actualRootPolynomialScaleBase / (1 + |lam| + Real.sqrt ‖z‖) ≤ dom.actualRootScaleRadius lam z := by
  let X := 1 + |lam| + Real.sqrt ‖z‖
  have hX : 1 ≤ X := by dsimp [X]; linarith [abs_nonneg lam, Real.sqrt_nonneg ‖z‖]
  have hA : 0 ≤ dom.scaledCoordinateRatioBound := Real.sqrt_nonneg _
  have hS : 0 ≤ dom.scaledRootCoordinateBound lam z := Real.sqrt_nonneg _
  apply le_min
  · exact (div_le_div_of_nonneg_right (min_le_left _ _) (by positivity : 0 ≤ X)).trans
      (radicandPolynomialScaleRadius_le dom hW hθ hD lam z)
  · apply ratio_lower_of_denominator_upper dom.rmax_pos.le (by linarith : 0 < X)
      (by positivity : 0 < 4 * (1 + dom.scaledRootCoordinateBound lam z))
      (by positivity : 0 < 4 * (1 + dom.scaledCoordinateRatioBound)) (min_le_right _ _)
    have hs := scaledRootCoordinateBound_le_polynomial dom hW hθ hD lam z
    change _ ≤ 4 * (1 + dom.scaledCoordinateRatioBound) * X
    nlinarith

include hW hθ hD in
theorem canonPolynomialScaleRadius_le (lam : ℝ) (z : ℂ) :
    dom.canonPolynomialScaleBase / (1 + |lam| + Real.sqrt ‖z‖) ≤ dom.canonScaleRadius lam z := by
  let X := 1 + |lam| + Real.sqrt ‖z‖
  have hX : 0 < X := by dsimp [X]; positivity
  have hC := (canonPolynomialScale_constants dom hW hθ hD).1
  have hraw : 0 ≤ dom.actualScaledRootBound lam z := by
    unfold CepsCanonDomain.actualScaledRootBound
    have := cepsVarLo_pos hD
    have := cepsChartK_pos hD
    have : 0 ≤ dom.scaledRootCoordinateBound lam z := Real.sqrt_nonneg _
    positivity
  have hcan : 0 ≤ dom.canonScaleBase := by
    unfold CepsCanonDomain.canonScaleBase
    have := dom.μ₀_pos
    have := dom.q₀_pos
    have := dom.c₀_pos
    positivity
  apply le_min
  · exact (div_le_div_of_nonneg_right (min_le_left _ _) hX.le).trans
      (actualRootPolynomialScaleRadius_le dom hW hθ hD lam z)
  · apply ratio_lower_of_denominator_upper hcan hX (by positivity : 0 < X + dom.actualScaledRootBound lam z)
      (by positivity : 0 < 1 + dom.scaledRootPolynomialConstant) (min_le_right _ _)
    have hs := actualScaledRootBound_le_polynomial dom hW hθ hD lam z
    change X + dom.actualScaledRootBound lam z ≤ (1 + dom.scaledRootPolynomialConstant) * X
    nlinarith

end PGM
