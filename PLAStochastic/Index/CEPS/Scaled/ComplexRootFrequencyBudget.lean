import PLAStochastic.Index.CEPS.Scaled.ComplexFrequencyCurve
import PLAStochastic.Index.CEPS.Scaled.PairPolynomialRadius

/-! # Coordinate-weighted root derivative bounds at every complex scale -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSignedRoot_complex_frequency_coordinate_budget
    (N : ℕ) (M lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    (hne : lam ≠ 0 ∨ z ≠ 0) {b sign : ℂ} (hsign : ‖sign‖ ≤ 1)
    (hb : b ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    ‖deriv (fun ζ => cepsScaledSignedRoot D θ ρW lam ζ sign b) z‖ *
      ‖cepsScaledRootCoordinate D θ ρW lam z b‖ ≤ 4 * cepsChartK D := by
  let r := cepsScaledRootCoordinate D θ ρW lam z b
  let w : ℂ := 1 + b * lam
  have hbC := ball_subset_ball (half_le_self (canonScaleRadius_pos dom hW hθ hD lam z).le)
    (complexFrequencyCurve_canon_mem dom hW hθ hD N M lam hb)
  have hbA := ball_subset_ball (min_le_left _ _) hbC
  have hbR := ball_subset_ball (min_le_left _ _) hbA
  obtain ⟨hμ, _, _, _, hw⟩ := complexFrequencyCurve_small dom hW hθ hD N M lam hz hsign hb
  have hrB := (cepsScaledRootCoordinate_budget dom hW hθ hD lam hz).2 b hbR
  have hB0 : 0 ≤ dom.scaledRootCoordinateBound lam z := Real.sqrt_nonneg _
  have hprod := (lt_div_iff₀ (by positivity : 0 < 4 * (1 + dom.scaledRootCoordinateBound lam z))).mp
    ((mem_ball_zero_iff.mp hbA).trans_le (min_le_right _ _))
  have hrphys : ‖b * sign * r‖ < dom.rmax := by
    rw [norm_mul, norm_mul]
    have hh : ‖b‖ * ‖sign‖ * ‖r‖ ≤ ‖b‖ * dom.scaledRootCoordinateBound lam z := by
      calc
        _ ≤ ‖b‖ * 1 * dom.scaledRootCoordinateBound lam z := by gcongr
        _ = _ := by ring
    exact hh.trans_lt (by nlinarith [norm_nonneg b, mul_nonneg (norm_nonneg b) hB0])
  have hΘ := cepsMorseRoot_coordinate_deriv_budget dom hW hθ hD
    (hμ.trans (by linarith [dom.μ₀_pos])) hrphys
  have hK := cepsChartK_pos hD
  have hslit := cepsScaledMorseRadicand_mem_slitPlane dom hW hθ hD lam hz hne hbR
  have hr0 : r ≠ 0 := by
    intro he
    have hs := sqrt_sq_eq (cepsScaledMorseRadicand D θ ρW lam z b)
    change r ^ 2 = _ at hs
    rw [he, zero_pow (by norm_num : 2 ≠ 0)] at hs
    rw [← hs] at hslit
    simp [mem_slitPlane_iff] at hslit
  have hrpos : 0 < ‖r‖ := norm_pos_iff.mpr hr0
  have hd := cepsScaledSignedRoot_complex_frequency_hasDerivAt dom hW hθ hD lam hz hne hsign hbC
  rw [hd.deriv, norm_div, norm_mul, norm_mul, norm_mul, norm_ofNat]
  change (‖deriv (cepsMorseRoot D θ ρW (b * lam)) (b * sign * r)‖ * ‖sign‖ * ‖w‖ /
    (2 * ‖r‖)) * ‖r‖ ≤ _
  rw [show (‖deriv (cepsMorseRoot D θ ρW (b * lam)) (b * sign * r)‖ * ‖sign‖ * ‖w‖ /
    (2 * ‖r‖)) * ‖r‖ =
      ‖deriv (cepsMorseRoot D θ ρW (b * lam)) (b * sign * r)‖ * ‖sign‖ * ‖w‖ / 2 by
        field_simp [hrpos.ne']]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  calc
    _ ≤ (4 * cepsChartK D) * 1 * 2 := by gcongr
    _ = _ := by ring

include hW hθ hD in
theorem cepsScaledSignedRoot_complex_frequency_envelope_budget
    (N : ℕ) (M lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    (hne : lam ≠ 0 ∨ z ≠ 0) {b sign : ℂ} (hsign : ‖sign‖ ≤ 1)
    (hb : b ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    ‖deriv (fun ζ => cepsScaledSignedRoot D θ ρW lam ζ sign b) z‖ *
      (|lam| + Real.sqrt ‖z‖) ≤ 8 * cepsChartK D * Real.sqrt (4 * v + 4) := by
  have hbC := complexFrequencyCurve_canon_mem dom hW hθ hD N M lam hb
  have hl := cepsScaledRootCoordinate_drift_le dom hW hθ hD lam hz hbC
  have hzB := cepsScaledRootCoordinate_frequency_le dom hW hθ hD lam hz hbC
  have hd := cepsScaledSignedRoot_complex_frequency_coordinate_budget dom hW hθ hD N M lam hz hne hsign hb
  calc
    _ ≤ ‖deriv (fun ζ => cepsScaledSignedRoot D θ ρW lam ζ sign b) z‖ *
        (2 * Real.sqrt (4 * v + 4) * ‖cepsScaledRootCoordinate D θ ρW lam z b‖) :=
      mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
    _ = (‖deriv (fun ζ => cepsScaledSignedRoot D θ ρW lam ζ sign b) z‖ *
        ‖cepsScaledRootCoordinate D θ ρW lam z b‖) * (2 * Real.sqrt (4 * v + 4)) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_right hd (by positivity)).trans_eq (by ring)

end PGM
