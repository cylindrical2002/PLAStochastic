import PLAStochastic.Index.CEPS.Scaled.RootFrequencyDerivative

/-! # Drift-weighted actual root frequency derivative budgets -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSignedRoot_frequency_deriv_coordinate_budget (M lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    (hne : lam ≠ 0 ∨ z ≠ 0) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z))
    {sign : ℂ} (hsign : ‖sign‖ ≤ 1) :
    ‖deriv (fun ζ => cepsScaledSignedRoot D θ ρW lam ζ sign b) z‖ *
      ‖cepsScaledRootCoordinate D θ ρW lam z b‖ ≤ 4 * cepsChartK D := by
  let r := cepsScaledRootCoordinate D θ ρW lam z (b : ℂ)
  let w : ℂ := 1 + (b : ℂ) * lam
  obtain ⟨hμ, hq, _, _, hwlo, hwhi, _⟩ :=
    cepsScaledTrueFrequency_curve_bounds dom hW hθ hD M lam hz hb hbs
  have hμn : ‖((b * lam : ℝ) : ℂ)‖ ≤ dom.μ₀ := by simpa only [norm_real, Real.norm_eq_abs] using hμ
  have hactual : cepsRootR D θ ρW (b * lam : ℝ) (cepsComplexScaledDiscount lam z b) = (b : ℂ) * r := by
    simpa only [r, cepsScaledDiscount, cepsComplexScaledDiscount, ofReal_mul] using
      cepsScaledRootCoordinate_actual hW hθ hD hb (z := z) (dom.μ_lt_chart hμn)
  have hrphys : ‖(b : ℂ) * sign * r‖ < dom.rmax := by
    calc
      _ = ‖sign‖ * ‖(b : ℂ) * r‖ := by rw [norm_mul, norm_mul, norm_mul]; ring
      _ ≤ ‖(b : ℂ) * r‖ := mul_le_of_le_one_left (norm_nonneg _) hsign
      _ < dom.rmax := by
        rw [← hactual]
        exact actual_rootR_lt_rmax dom hW hθ hD hμn (hq.trans (half_le_self dom.q₀_pos.le))
  have hσ := cepsMorseRoot_coordinate_deriv_budget dom hW hθ hD
    (show ‖(b : ℂ) * (lam : ℂ)‖ ≤ dom.μ₀ by simpa only [ofReal_mul] using hμn) hrphys
  have hK := cepsChartK_pos hD
  have hw : ‖w‖ ≤ 2 := by
    have he : w = ((1 + b * lam : ℝ) : ℂ) := by simp [w, ofReal_mul]
    rw [he, norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 1 + b * lam)]
    exact hwhi
  have hbE := ball_subset_ball (trueDenominatorScaleRadius_le dom hW hθ hD M lam z)
    (ball_subset_ball (truePairScaleRadius_le dom M lam z)
      (ball_subset_ball (trueFrequencyScaleRadius_le dom M lam z) hbs))
  have hbSur := ball_subset_ball (min_le_left _ _) (ball_subset_ball (min_le_left _ _) hbE)
  have hlow := cepsScaledRootCoordinate_lower dom hW hθ hD 0 M lam hz hbSur
  have hpos : 0 < lam ^ 2 + ‖z‖ := by
    rcases hne with hl | hz0
    · nlinarith [sq_pos_of_ne_zero hl, norm_nonneg z]
    · exact add_pos_of_nonneg_of_pos (sq_nonneg lam) (norm_pos_iff.mpr hz0)
  have hrpos : 0 < ‖r‖ := (scaledCoordinateLower_pos dom hW hθ hD lam hpos).trans_le hlow
  have hd := cepsScaledSignedRoot_frequency_hasDerivAt dom hW hθ hD M lam hz hne hb hbs hsign
  rw [hd.deriv, norm_div, norm_mul, norm_mul, norm_mul, norm_ofNat]
  change (‖deriv (cepsMorseRoot D θ ρW ((b : ℂ) * lam)) ((b : ℂ) * sign * r)‖ * ‖sign‖ * ‖w‖ /
    (2 * ‖r‖)) * ‖r‖ ≤ _
  rw [show (‖deriv (cepsMorseRoot D θ ρW ((b : ℂ) * lam)) ((b : ℂ) * sign * r)‖ * ‖sign‖ * ‖w‖ /
    (2 * ‖r‖)) * ‖r‖ =
      ‖deriv (cepsMorseRoot D θ ρW ((b : ℂ) * lam)) ((b : ℂ) * sign * r)‖ * ‖sign‖ * ‖w‖ / 2 by
        field_simp [hrpos.ne']]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  calc
    _ ≤ (4 * cepsChartK D) * 1 * 2 := by gcongr
    _ = _ := by ring

include hW hθ hD in
theorem cepsScaledSignedRoot_frequency_deriv_drift_budget (M lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    (hne : lam ≠ 0 ∨ z ≠ 0) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z))
    {sign : ℂ} (hsign : ‖sign‖ ≤ 1) :
    ‖deriv (fun ζ => cepsScaledSignedRoot D θ ρW lam ζ sign b) z‖ * |lam| ≤
      4 * cepsChartK D * Real.sqrt (8 * v + 8) := by
  have hv : 0 < 8 * v + 8 := by linarith [CepsCanonDomain.v_pos hW hθ hD]
  have hs : 0 < Real.sqrt (8 * v + 8) := Real.sqrt_pos.mpr hv
  have hbE := ball_subset_ball (trueDenominatorScaleRadius_le dom hW hθ hD M lam z)
    (ball_subset_ball (truePairScaleRadius_le dom M lam z)
      (ball_subset_ball (trueFrequencyScaleRadius_le dom M lam z) hbs))
  have hbSur := ball_subset_ball (min_le_left _ _) (ball_subset_ball (min_le_left _ _) hbE)
  have hlow := (scaledCoordinateLower_drift_frequency_le dom hW hθ hD lam z).trans
    (cepsScaledRootCoordinate_lower dom hW hθ hD 0 M lam hz hbSur)
  have hl : |lam| ≤ ‖cepsScaledRootCoordinate D θ ρW lam z b‖ * Real.sqrt (8 * v + 8) := by
    have hh := (div_le_iff₀ hs).mp hlow
    linarith [Real.sqrt_nonneg ‖z‖]
  calc
    _ ≤ ‖deriv (fun ζ => cepsScaledSignedRoot D θ ρW lam ζ sign b) z‖ *
        (‖cepsScaledRootCoordinate D θ ρW lam z b‖ * Real.sqrt (8 * v + 8)) :=
      mul_le_mul_of_nonneg_left hl (norm_nonneg _)
    _ = (‖deriv (fun ζ => cepsScaledSignedRoot D θ ρW lam ζ sign b) z‖ *
        ‖cepsScaledRootCoordinate D θ ρW lam z b‖) * Real.sqrt (8 * v + 8) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (cepsScaledSignedRoot_frequency_deriv_coordinate_budget dom hW hθ hD M lam hz hne hb hbs hsign) hs.le

end PGM
