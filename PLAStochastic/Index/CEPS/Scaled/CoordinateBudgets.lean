import PLAStochastic.Index.CEPS.Scaled.SurrogateDeltaInverse

/-! # Polynomial comparison budgets for the scaled root coordinate -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.scaledCoordinateRatioBound {D θ v : ℝ} (_dom : CepsCanonDomain D θ v) : ℝ :=
  Real.sqrt ((2 + 1 / cepsVarLo D) * (4 * v + 4))

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem scaledRootCoordinateBound_le_lower (lam : ℝ) (z : ℂ) :
    dom.scaledRootCoordinateBound lam z ≤
      dom.scaledCoordinateRatioBound * dom.scaledCoordinateLower lam z := by
  have hv : 0 < 4 * v + 4 := by linarith [CepsCanonDomain.v_pos hW hθ hD]
  have hvl := cepsVarLo_pos hD
  have hs : 0 ≤ 2 * (‖z‖ + lam ^ 2 / (2 * cepsVarLo D)) := by positivity
  have ha : 0 ≤ (2 + 1 / cepsVarLo D) * (4 * v + 4) := by positivity
  have ht : 0 ≤ (lam ^ 2 + ‖z‖) / (4 * v + 4) := by positivity
  change Real.sqrt (2 * (‖z‖ + lam ^ 2 / (2 * cepsVarLo D))) ≤
    Real.sqrt ((2 + 1 / cepsVarLo D) * (4 * v + 4)) *
      Real.sqrt ((lam ^ 2 + ‖z‖) / (4 * v + 4))
  apply (pow_le_pow_iff_left₀ (Real.sqrt_nonneg _) (by positivity) (by norm_num : 2 ≠ 0)).mp
  rw [mul_pow, Real.sq_sqrt hs, Real.sq_sqrt ha, Real.sq_sqrt ht]
  have he : (2 + 1 / cepsVarLo D) * (4 * v + 4) *
      ((lam ^ 2 + ‖z‖) / (4 * v + 4)) = (2 + 1 / cepsVarLo D) * (lam ^ 2 + ‖z‖) := by
    rw [mul_assoc, mul_div_cancel₀ _ hv.ne']
  rw [he]
  have he' : 2 * (‖z‖ + lam ^ 2 / (2 * cepsVarLo D)) =
      2 * ‖z‖ + lam ^ 2 / cepsVarLo D := by ring
  rw [he']
  have he'' : (2 + 1 / cepsVarLo D) * (lam ^ 2 + ‖z‖) =
      2 * ‖z‖ + lam ^ 2 / cepsVarLo D + 2 * lam ^ 2 + ‖z‖ / cepsVarLo D := by ring
  rw [he'']
  linarith [sq_nonneg lam, div_nonneg (norm_nonneg z) hvl.le]

include hW hθ hD in
theorem scaledCoordinateLower_le_drift_frequency (lam : ℝ) (z : ℂ) :
    dom.scaledCoordinateLower lam z ≤ |lam| + Real.sqrt ‖z‖ := by
  have hv : 1 ≤ 4 * v + 4 := by linarith [CepsCanonDomain.v_pos hW hθ hD]
  have ha : (lam ^ 2 + ‖z‖) / (4 * v + 4) ≤ lam ^ 2 + ‖z‖ :=
    div_le_self (by positivity) hv
  have hs : lam ^ 2 + ‖z‖ ≤ (|lam| + Real.sqrt ‖z‖) ^ 2 := by
    nlinarith [Real.sq_sqrt (norm_nonneg z), sq_abs lam,
      mul_nonneg (abs_nonneg lam) (Real.sqrt_nonneg ‖z‖)]
  simpa only [CepsCanonDomain.scaledCoordinateLower,
    Real.sqrt_sq (by positivity : 0 ≤ |lam| + Real.sqrt ‖z‖)] using Real.sqrt_le_sqrt (ha.trans hs)

include hW hθ hD in
theorem scaledCoordinateLower_drift_frequency_le (lam : ℝ) (z : ℂ) :
    (|lam| + Real.sqrt ‖z‖) / Real.sqrt (8 * v + 8) ≤
      dom.scaledCoordinateLower lam z := by
  have hv : 0 < 4 * v + 4 := by linarith [CepsCanonDomain.v_pos hW hθ hD]
  have h8 : 0 < 8 * v + 8 := by linarith
  have ht : 0 ≤ (lam ^ 2 + ‖z‖) / (4 * v + 4) := by positivity
  have hs : (|lam| + Real.sqrt ‖z‖) ^ 2 ≤ 2 * (lam ^ 2 + ‖z‖) := by
    nlinarith [Real.sq_sqrt (norm_nonneg z), sq_abs lam,
      sq_nonneg (|lam| - Real.sqrt ‖z‖)]
  apply (pow_le_pow_iff_left₀ (by positivity) (Real.sqrt_nonneg _) (by norm_num : 2 ≠ 0)).mp
  change ((|lam| + Real.sqrt ‖z‖) / Real.sqrt (8 * v + 8)) ^ 2 ≤
    (Real.sqrt ((lam ^ 2 + ‖z‖) / (4 * v + 4))) ^ 2
  rw [div_pow, Real.sq_sqrt h8.le, Real.sq_sqrt ht]
  apply (div_le_div_iff₀ h8 hv).mpr
  nlinarith

private theorem div_min_one_le {t : ℝ} (ht : 0 < t) : t / min 1 t ≤ 1 + t := by
  by_cases h : t ≤ 1
  · rw [min_eq_right h, div_self ht.ne']
    linarith
  · rw [min_eq_left (le_of_not_ge h), div_one]
    linarith

include hW hθ hD in
theorem scaledCoordinateBound_mul_deltaInverse_le (lam : ℝ) {z : ℂ}
    (hne : 0 < lam ^ 2 + ‖z‖) :
    dom.scaledRootCoordinateBound lam z * dom.surrogateDeltaInverseBound lam z ≤
      (4 * dom.scaledCoordinateRatioBound / dom.scaledComplexSector) *
        (1 + |lam| + Real.sqrt ‖z‖) := by
  have ht := scaledCoordinateLower_pos dom hW hθ hD lam hne
  have hc := (cepsScaledSurrogate_constants dom hW hθ hD 0 0).2.1
  have hA : 0 ≤ dom.scaledCoordinateRatioBound := Real.sqrt_nonneg _
  have hi : 0 ≤ dom.surrogateDeltaInverseBound lam z := by
    unfold CepsCanonDomain.surrogateDeltaInverseBound
    exact div_nonneg (div_nonneg (by norm_num) hc.le) (le_min (by norm_num) ht.le)
  calc
    _ ≤ (dom.scaledCoordinateRatioBound * dom.scaledCoordinateLower lam z) *
        dom.surrogateDeltaInverseBound lam z :=
      mul_le_mul_of_nonneg_right (scaledRootCoordinateBound_le_lower dom hW hθ hD lam z) hi
    _ = (4 * dom.scaledCoordinateRatioBound / dom.scaledComplexSector) *
        (dom.scaledCoordinateLower lam z / min 1 (dom.scaledCoordinateLower lam z)) := by
      unfold CepsCanonDomain.surrogateDeltaInverseBound
      ring
    _ ≤ (4 * dom.scaledCoordinateRatioBound / dom.scaledComplexSector) *
        (1 + dom.scaledCoordinateLower lam z) :=
      mul_le_mul_of_nonneg_left (div_min_one_le ht) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (by linarith [scaledCoordinateLower_le_drift_frequency dom hW hθ hD lam z]) (by positivity)

end PGM
