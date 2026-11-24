import PLAStochastic.Index.CEPS.Scaled.PairRootDirections

/-! # A positive-root decay direction with an explicit bounded drift loss -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledRootPlus_width_drift_loss (N : ℕ) (M lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.complexDirectionScaleRadius N M lam z)) :
    ‖cepsScaledRootCoordinate D θ ρW lam z b‖ / (8 * Real.sqrt v) - 2 / cepsVarLo D * |lam| ≤
      (cepsScaledSignedRoot D θ ρW lam z 1 b * (1 + b * lam)).re := by
  obtain ⟨hbhalf, hμ, hsmall⟩ := complexDirectionScaleCurve_bounds dom N M lam hb
  have hbfull := ball_subset_ball (half_le_self (canonScaleRadius_pos dom hW hθ hD lam z).le) hbhalf
  have hsub : dom.canonScaleRadius lam z / 2 ≤ dom.radicandScaleRadius lam / 2 :=
    div_le_div_of_nonneg_right ((min_le_left _ _).trans (min_le_left _ _)) (by norm_num)
  let r := cepsScaledRootCoordinate D θ ρW lam z b
  let s := Real.sqrt (cepsStepVar ρW / 2)
  let c := cepsScaledMorseCenter D θ ρW lam b
  let p := cepsScaledSignedRoot D θ ρW lam z 1 b
  have hs : 0 < s := Real.sqrt_pos.mpr (by linarith [cepsStepVar_pos hW hθ hD])
  have hv := Real.sqrt_pos.mpr (CepsCanonDomain.v_pos hW hθ hD)
  have hsv : s ≤ Real.sqrt v := Real.sqrt_le_sqrt (by linarith [cepsStepVar_le hW, cepsStepVar_pos hW hθ hD])
  have hsector : ‖r‖ / 2 ≤ r.re := cepsScaledRootCoordinate_complex_sector dom hW hθ hD lam hz (ball_subset_ball hsub hbhalf)
  have hdiv := div_le_div_of_nonneg_right hsector hs.le
  have hcenter := (cepsScaledMorseCenter_budget dom hW hθ hD lam hz).2 b hbfull
  have hc : -(2 / cepsVarLo D * |lam|) ≤ c.re := by
    have hh := (neg_le_abs c.re).trans ((abs_re_le_norm c).trans hcenter)
    linarith
  have herr : ‖p - c - r / (s : ℂ)‖ ≤ ‖r‖ / (8 * s) := by
    simpa only [one_mul] using cepsScaledRoot_individual_linear_error dom hW hθ hD lam hz
      (by norm_num : ‖(1 : ℂ)‖ ≤ 1) hbfull
  have hneg := (neg_le_abs (p - c - r / (s : ℂ)).re).trans ((abs_re_le_norm _).trans herr)
  have he : (p - c - r / (s : ℂ)).re = p.re - c.re - r.re / s := by simp [div_ofReal_re]
  rw [he] at hneg
  have hpre : ‖r‖ / (4 * Real.sqrt v) - 2 / cepsVarLo D * |lam| ≤ p.re := by
    have hcompare : ‖r‖ / (4 * Real.sqrt v) ≤ ‖r‖ / (4 * s) :=
      div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) (by linarith)
    have hnon := mul_nonneg (norm_nonneg r) (inv_nonneg.mpr hs.le)
    ring_nf at hneg hdiv hcompare hc hnon ⊢
    linarith
  have hp := cepsScaledRoot_individual_norm_le dom hW hθ hD lam hz (by norm_num : ‖(1 : ℂ)‖ ≤ 1) hbhalf hμ
  have hH := complexIndividualRootBound_pos dom hW hθ hD
  have hprod : ‖p * (b * (lam : ℂ))‖ ≤ ‖r‖ / (8 * Real.sqrt v) := by
    rw [norm_mul]
    calc
      _ ≤ (dom.complexIndividualRootBound * ‖r‖) * ((1 / (8 * Real.sqrt v)) / dom.complexIndividualRootBound) :=
        mul_le_mul hp hsmall (norm_nonneg _) (by positivity)
      _ = _ := by field_simp
  have hloss := (neg_le_abs (p * (b * (lam : ℂ))).re).trans ((abs_re_le_norm _).trans hprod)
  rw [mul_add, mul_one, add_re]
  dsimp only [p, r] at hpre hloss
  ring_nf at hpre hloss ⊢
  linarith

end PGM
