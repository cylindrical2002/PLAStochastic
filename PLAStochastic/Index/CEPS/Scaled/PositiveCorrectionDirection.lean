import PLAStochastic.Index.CEPS.Scaled.CoordinateRealDrift
import PLAStochastic.Index.CEPS.Scaled.ComplexRootNorm

/-! # The root combination controlling positive-drift half-line subtraction -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledPositiveCorrectionRoot_norm_le (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z / 2))
    (hμ : b * (lam : ℂ) ∈ ball (0 : ℂ) dom.centerUnitSectorRadius) :
    ‖2 * cepsScaledSignedRoot D θ ρW lam z 1 b - cepsScaledSignedRoot D θ ρW lam z (-1) b‖ ≤
      (3 * dom.complexIndividualRootBound) * ‖cepsScaledRootCoordinate D θ ρW lam z b‖ := by
  have hp := cepsScaledRoot_individual_norm_le dom hW hθ hD lam hz (by norm_num : ‖(1 : ℂ)‖ ≤ 1) hb hμ
  have hm := cepsScaledRoot_individual_norm_le dom hW hθ hD lam hz (by norm_num : ‖(-1 : ℂ)‖ ≤ 1) hb hμ
  have ht := norm_sub_le (2 * cepsScaledSignedRoot D θ ρW lam z 1 b)
    (cepsScaledSignedRoot D θ ρW lam z (-1) b)
  rw [norm_mul] at ht
  norm_num at ht
  nlinarith

include hW hθ hD in
theorem cepsScaledPositiveCorrectionRoot_real_lower (lam : ℝ) (hlam : 0 ≤ lam)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z / 2))
    (hμ : b * (lam : ℂ) ∈ ball (0 : ℂ) dom.centerUnitSectorRadius) :
    ‖cepsScaledRootCoordinate D θ ρW lam z b‖ / (8 * Real.sqrt v) ≤
      (2 * cepsScaledSignedRoot D θ ρW lam z 1 b - cepsScaledSignedRoot D θ ρW lam z (-1) b).re := by
  have hbfull := ball_subset_ball (half_le_self (canonScaleRadius_pos dom hW hθ hD lam z).le) hb
  have hsub : dom.canonScaleRadius lam z / 2 ≤ dom.radicandScaleRadius lam / 2 := by
    have h1 : dom.canonScaleRadius lam z ≤ dom.actualRootScaleRadius lam z := min_le_left _ _
    have h2 : dom.actualRootScaleRadius lam z ≤ dom.radicandScaleRadius lam := min_le_left _ _
    exact div_le_div_of_nonneg_right (h1.trans h2) (by norm_num)
  let r := cepsScaledRootCoordinate D θ ρW lam z b
  let s := Real.sqrt (cepsStepVar ρW / 2)
  let c := cepsScaledMorseCenter D θ ρW lam b
  let p := cepsScaledSignedRoot D θ ρW lam z 1 b
  let m := cepsScaledSignedRoot D θ ρW lam z (-1) b
  let a := 2 * p - m
  have hs : 0 < s := Real.sqrt_pos.mpr (by linarith [cepsStepVar_pos hW hθ hD])
  have hv : 0 < Real.sqrt v := Real.sqrt_pos.mpr (CepsCanonDomain.v_pos hW hθ hD)
  have hsv : s ≤ Real.sqrt v := Real.sqrt_le_sqrt (by linarith [cepsStepVar_le hW, cepsStepVar_pos hW hθ hD])
  have hsector : ‖r‖ / 2 ≤ r.re := cepsScaledRootCoordinate_complex_sector dom hW hθ hD lam hz (ball_subset_ball hsub hb)
  have hdrift : 3 * lam / (4 * cepsStepVar ρW) ≤ r.re / s := by
    simpa only [abs_of_nonneg hlam] using cepsScaledRootCoordinate_real_drift_lower dom hW hθ hD lam hz (ball_subset_ball hsub hb)
  have hcN : ‖c‖ ≤ 3 * lam / (2 * cepsStepVar ρW) := by
    simpa only [abs_of_nonneg hlam] using (cepsScaledMorseCenter_complex_signs dom hW hθ hD lam hμ).2.2
  have hcR := (neg_le_abs c.re).trans ((abs_re_le_norm c).trans hcN)
  have hc : -2 * (r.re / s) ≤ c.re := by
    ring_nf at hdrift hcR ⊢
    linarith
  have hpE : ‖p - c - r / (s : ℂ)‖ ≤ ‖r‖ / (8 * s) := by
    simpa only [one_mul] using cepsScaledRoot_individual_linear_error dom hW hθ hD lam hz
      (by norm_num : ‖(1 : ℂ)‖ ≤ 1) hbfull
  have hmE : ‖m - c + r / (s : ℂ)‖ ≤ ‖r‖ / (8 * s) := by
    simpa only [neg_one_mul, neg_div, sub_neg_eq_add] using cepsScaledRoot_individual_linear_error dom hW hθ hD lam hz
      (by norm_num : ‖(-1 : ℂ)‖ ≤ 1) hbfull
  have he : a - c - 3 * r / (s : ℂ) =
      2 * (p - c - r / (s : ℂ)) - (m - c + r / (s : ℂ)) := by dsimp [a]; ring
  have herr : ‖a - c - 3 * r / (s : ℂ)‖ ≤ 3 * ‖r‖ / (8 * s) := by
    rw [he]
    have ht := norm_sub_le (2 * (p - c - r / (s : ℂ))) (m - c + r / (s : ℂ))
    rw [norm_mul] at ht
    norm_num at ht
    apply ht.trans
    calc
      _ ≤ 2 * (‖r‖ / (8 * s)) + ‖r‖ / (8 * s) := by linarith
      _ = _ := by ring
  have hneg := (neg_le_abs (a - c - 3 * r / (s : ℂ)).re).trans ((abs_re_le_norm _).trans herr)
  have hre : (a - c - 3 * r / (s : ℂ)).re = a.re - c.re - 3 * r.re / s := by
    simp [div_ofReal_re, mul_re]
  rw [hre] at hneg
  have hlo : ‖r‖ / (8 * s) ≤ a.re := by
    have hdiv := div_le_div_of_nonneg_right hsector hs.le
    have hnon := mul_nonneg (norm_nonneg r) (inv_nonneg.mpr hs.le)
    ring_nf at hneg hdiv hc ⊢
    linarith
  exact (div_le_div_of_nonneg_left (norm_nonneg r) (by positivity : 0 < 8 * s) (by linarith : 8 * s ≤ 8 * Real.sqrt v)).trans hlo

end PGM
