import PLAStochastic.Index.CEPS.Scaled.ComplexRootDirections

/-! # Individual complex-scale roots are controlled by the root coordinate -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.complexIndividualRootBound {D θ v : ℝ} (_dom : CepsCanonDomain D θ v) : ℝ :=
  3 / (2 * cepsVarLo D) * Real.sqrt (4 * v + 4) + 2 / Real.sqrt (cepsVarLo D / 2)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem complexIndividualRootBound_pos : 0 < dom.complexIndividualRootBound := by
  have hvl := cepsVarLo_pos hD
  have hv := CepsCanonDomain.v_pos hW hθ hD
  unfold CepsCanonDomain.complexIndividualRootBound
  positivity

include hW hθ hD in
theorem cepsScaledRootCoordinate_drift_le (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z / 2)) :
    |lam| ≤ Real.sqrt (4 * v + 4) * ‖cepsScaledRootCoordinate D θ ρW lam z b‖ := by
  have hsub : dom.canonScaleRadius lam z / 2 ≤ dom.radicandScaleRadius lam / 2 := by
    have h1 : dom.canonScaleRadius lam z ≤ dom.actualRootScaleRadius lam z := min_le_left _ _
    have h2 : dom.actualRootScaleRadius lam z ≤ dom.radicandScaleRadius lam := min_le_left _ _
    exact div_le_div_of_nonneg_right (h1.trans h2) (by norm_num)
  have hc := cepsScaledRootCoordinate_complex_coercive dom hW hθ hD lam hz (ball_subset_ball hsub hb)
  have hv : 0 ≤ 4 * v + 4 := by linarith [CepsCanonDomain.v_pos hW hθ hD]
  have hs := Real.sq_sqrt hv
  have he : (Real.sqrt (4 * v + 4) * ‖cepsScaledRootCoordinate D θ ρW lam z b‖) ^ 2 =
      (4 * v + 4) * ‖cepsScaledRootCoordinate D θ ρW lam z b‖ ^ 2 := by rw [mul_pow, hs]
  apply (pow_le_pow_iff_left₀ (abs_nonneg _) (by positivity) (by norm_num : 2 ≠ 0)).mp
  rw [sq_abs, he]
  linarith [norm_nonneg z]

include hW hθ hD in
theorem cepsScaledRoot_individual_norm_le (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    {sign : ℂ} (hsign : ‖sign‖ ≤ 1) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z / 2))
    (hμ : b * (lam : ℂ) ∈ ball (0 : ℂ) dom.centerUnitSectorRadius) :
    ‖cepsScaledSignedRoot D θ ρW lam z sign b‖ ≤
      dom.complexIndividualRootBound * ‖cepsScaledRootCoordinate D θ ρW lam z b‖ := by
  let r := cepsScaledRootCoordinate D θ ρW lam z b
  let c := cepsScaledMorseCenter D θ ρW lam b
  let s := Real.sqrt (cepsStepVar ρW / 2)
  let s₀ := Real.sqrt (cepsVarLo D / 2)
  let p := cepsScaledSignedRoot D θ ρW lam z sign b
  let u := sign * r / (s : ℂ)
  have hs : 0 < s := Real.sqrt_pos.mpr (by linarith [cepsStepVar_pos hW hθ hD])
  have hs₀ : 0 < s₀ := Real.sqrt_pos.mpr (by linarith [cepsVarLo_pos hD])
  have hss : s₀ ≤ s := Real.sqrt_le_sqrt (by linarith [cepsVarLo_le hW hθ hD])
  have hbfull := ball_subset_ball (half_le_self (canonScaleRadius_pos dom hW hθ hD lam z).le) hb
  have herr : ‖p - c - u‖ ≤ ‖r‖ / (8 * s) := cepsScaledRoot_individual_linear_error dom hW hθ hD lam hz hsign hbfull
  have hmodel : ‖u‖ ≤ ‖r‖ / s := by
    dsimp only [u]
    rw [norm_div, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hs]
    exact div_le_div_of_nonneg_right (by nlinarith [norm_nonneg r]) hs.le
  have hcenter : ‖c‖ ≤ (3 / (2 * cepsVarLo D) * Real.sqrt (4 * v + 4)) * ‖r‖ := by
    have hc := (cepsScaledMorseCenter_complex_signs dom hW hθ hD lam hμ).2.2
    have hvl := cepsVarLo_pos hD
    have hV := cepsVarLo_le hW hθ hD
    calc
      _ ≤ 3 * |lam| / (2 * cepsVarLo D) := hc.trans
        (div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith))
      _ = 3 / (2 * cepsVarLo D) * |lam| := by ring
      _ ≤ 3 / (2 * cepsVarLo D) * (Real.sqrt (4 * v + 4) * ‖r‖) :=
        mul_le_mul_of_nonneg_left (cepsScaledRootCoordinate_drift_le dom hW hθ hD lam hz hb) (by positivity)
      _ = _ := by ring
  have htri := norm_add_le (p - c - u) (c + u)
  rw [show p - c - u + (c + u) = p by ring] at htri
  have hrest : ‖r‖ / (8 * s) + ‖r‖ / s ≤ (2 / s₀) * ‖r‖ := by
    have hn := mul_nonneg (norm_nonneg r) (inv_nonneg.mpr hs.le)
    have h1 : ‖r‖ / (8 * s) + ‖r‖ / s ≤ (2 / s) * ‖r‖ := by ring_nf; linarith
    exact h1.trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left (by norm_num) hs₀ hss) (norm_nonneg r))
  have hall := htri.trans (add_le_add herr ((norm_add_le c u).trans (add_le_add hcenter hmodel)))
  change ‖p‖ ≤ (3 / (2 * cepsVarLo D) * Real.sqrt (4 * v + 4) + 2 / s₀) * ‖r‖
  nlinarith

end PGM
