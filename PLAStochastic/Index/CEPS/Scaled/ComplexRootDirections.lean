import PLAStochastic.Index.CEPS.Scaled.IndividualRootModel
import PLAStochastic.Index.CEPS.Scaled.ComplexRootSector

/-! # Individual actual root directions throughout complex-scale discs -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledRoot_complex_directions (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z / 2))
    (hμ : b * (lam : ℂ) ∈ ball (0 : ℂ) dom.centerUnitSectorRadius) :
    (lam ≤ 0 → ‖cepsScaledRootCoordinate D θ ρW lam z b‖ / (4 * Real.sqrt v) ≤
      (cepsScaledSignedRoot D θ ρW lam z 1 b).re) ∧
    (0 ≤ lam → ‖cepsScaledRootCoordinate D θ ρW lam z b‖ / (4 * Real.sqrt v) ≤
      (-cepsScaledSignedRoot D θ ρW lam z (-1) b).re) := by
  have hbfull := ball_subset_ball (half_le_self (canonScaleRadius_pos dom hW hθ hD lam z).le) hb
  have hsub : dom.canonScaleRadius lam z / 2 ≤ dom.radicandScaleRadius lam / 2 := by
    have h1 : dom.canonScaleRadius lam z ≤ dom.actualRootScaleRadius lam z := min_le_left _ _
    have h2 : dom.actualRootScaleRadius lam z ≤ dom.radicandScaleRadius lam := min_le_left _ _
    exact div_le_div_of_nonneg_right (h1.trans h2) (by norm_num)
  let r := cepsScaledRootCoordinate D θ ρW lam z b
  let s := Real.sqrt (cepsStepVar ρW / 2)
  let c := cepsScaledMorseCenter D θ ρW lam b
  have hs : 0 < s := Real.sqrt_pos.mpr (by linarith [cepsStepVar_pos hW hθ hD])
  have hv : 0 < Real.sqrt v := Real.sqrt_pos.mpr (CepsCanonDomain.v_pos hW hθ hD)
  have hsv : s ≤ Real.sqrt v := Real.sqrt_le_sqrt (by linarith [cepsStepVar_le hW, cepsStepVar_pos hW hθ hD])
  have hsector : ‖r‖ / 2 ≤ r.re := cepsScaledRootCoordinate_complex_sector dom hW hθ hD lam hz (ball_subset_ball hsub hb)
  have hdiv := div_le_div_of_nonneg_right hsector hs.le
  have hsigns := cepsScaledMorseCenter_complex_signs dom hW hθ hD lam hμ
  have hcompare : ‖r‖ / (4 * Real.sqrt v) ≤ ‖r‖ / (4 * s) :=
    div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) (by linarith)
  constructor
  · intro hlam
    have hc : 0 ≤ c.re := hsigns.1 hlam
    let p := cepsScaledSignedRoot D θ ρW lam z 1 b
    have herr : ‖p - c - r / (s : ℂ)‖ ≤ ‖r‖ / (8 * s) := by
      simpa only [one_mul] using cepsScaledRoot_individual_linear_error dom hW hθ hD lam hz
        (by norm_num : ‖(1 : ℂ)‖ ≤ 1) hbfull
    have hneg := (neg_le_abs (p - c - r / (s : ℂ)).re).trans ((abs_re_le_norm _).trans herr)
    have he : (p - c - r / (s : ℂ)).re = p.re - c.re - r.re / s := by
      simp [div_ofReal_re]
    rw [he] at hneg
    have hlo : ‖r‖ / (4 * s) ≤ p.re := by
      have hnon := mul_nonneg (norm_nonneg r) (inv_nonneg.mpr hs.le)
      ring_nf at hneg hdiv ⊢
      linarith
    exact hcompare.trans hlo
  · intro hlam
    have hc : c.re ≤ 0 := hsigns.2.1 hlam
    let m := cepsScaledSignedRoot D θ ρW lam z (-1) b
    have herr : ‖m - c + r / (s : ℂ)‖ ≤ ‖r‖ / (8 * s) := by
      simpa only [neg_one_mul, neg_div, sub_neg_eq_add] using
        cepsScaledRoot_individual_linear_error dom hW hθ hD lam hz (by norm_num : ‖(-1 : ℂ)‖ ≤ 1) hbfull
    have hpos := (le_abs_self (m - c + r / (s : ℂ)).re).trans ((abs_re_le_norm _).trans herr)
    have he : (m - c + r / (s : ℂ)).re = m.re - c.re + r.re / s := by
      simp [div_ofReal_re]
    rw [he] at hpos
    have hlo : ‖r‖ / (4 * s) ≤ -m.re := by
      have hnon := mul_nonneg (norm_nonneg r) (inv_nonneg.mpr hs.le)
      ring_nf at hpos hdiv ⊢
      linarith
    exact hcompare.trans hlo

end PGM
