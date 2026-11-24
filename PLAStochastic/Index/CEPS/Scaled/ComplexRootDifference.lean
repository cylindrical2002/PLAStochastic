import PLAStochastic.Index.CEPS.Scaled.ComplexRootSector
import PLAStochastic.Index.CEPS.Scaled.RootCurvePair

/-! # Uniform root-gap sectors throughout a complex scale disc -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledRootGap_linear_error (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z)) :
    ‖cepsScaledSignedRoot D θ ρW lam z 1 b - cepsScaledSignedRoot D θ ρW lam z (-1) b -
      2 * cepsScaledRootCoordinate D θ ρW lam z b / (Real.sqrt (cepsStepVar ρW / 2) : ℂ)‖ ≤
      ‖cepsScaledRootCoordinate D θ ρW lam z b‖ / (4 * Real.sqrt (cepsStepVar ρW / 2)) := by
  let s := Real.sqrt (cepsStepVar ρW / 2)
  have hs : 0 < s := Real.sqrt_pos.mpr (by linarith [cepsStepVar_pos hW hθ hD])
  let E : ℂ → ℂ := fun b => cepsScaledSignedRoot D θ ρW lam z 1 b -
    cepsScaledSignedRoot D θ ρW lam z (-1) b - 2 * cepsScaledRootCoordinate D θ ρW lam z b / (s : ℂ)
  have hnonzero : ∀ b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z), b ≠ 0 →
      ‖E b‖ ≤ ‖cepsScaledRootCoordinate D θ ρW lam z b‖ / (4 * s) := by
    intro b hb hb0
    let r := b * cepsScaledRootCoordinate D θ ρW lam z b
    have hsub : b ∈ ball (0 : ℂ) (dom.actualRootScaleRadius lam z) :=
      ball_subset_ball (min_le_left _ _) hb
    have hbr : b ∈ ball (0 : ℂ) (dom.radicandScaleRadius lam) :=
      ball_subset_ball (min_le_left _ _) hsub
    have hn : ‖b‖ < dom.rmax / (4 * (1 + dom.scaledRootCoordinateBound lam z)) :=
      (mem_ball_zero_iff.mp hsub).trans_le (min_le_right _ _)
    have hS : 0 ≤ dom.scaledRootCoordinateBound lam z := Real.sqrt_nonneg _
    have hmul := (lt_div_iff₀ (by positivity : 0 < 4 * (1 + dom.scaledRootCoordinateBound lam z))).mp hn
    have hr : ‖r‖ < cepsChartRho D θ := by
      have hnS := (cepsScaledRootCoordinate_budget dom hW hθ hD lam hz).2 b hbr
      have hnorm : ‖r‖ ≤ ‖b‖ * dom.scaledRootCoordinateBound lam z := by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left hnS (norm_nonneg b)
      have hsmall : ‖r‖ < dom.rmax := by nlinarith [norm_nonneg b]
      have := dom.rmax_r1; have := dom.rmax_pos
      linarith
    have hμ : ‖b * (lam : ℂ)‖ < cepsChartMu D θ := dom.μ_lt_chart
      ((canonScaleCurve_bounds dom hW hθ hD lam hz (sign := 1) (by norm_num) hb).1.le.trans
        (by linarith [dom.μ₀_pos]))
    have hp := cepsMorseRoot_linear_error hW hθ hD hμ hr
    have hm := cepsMorseRoot_linear_error hW hθ hD hμ (r := -r) (by simpa using hr)
    rw [norm_neg] at hm
    have he : b * E b =
        (cepsMorseRoot D θ ρW (b * lam) r - cepsMorseCenter D θ ρW (b * lam) - r / (s : ℂ)) -
        (cepsMorseRoot D θ ρW (b * lam) (-r) - cepsMorseCenter D θ ρW (b * lam) - (-r) / (s : ℂ)) := by
      have hpr := cepsScaledRootCurve_eq_morse hW hθ hD lam z 1 b
      have hmr := cepsScaledRootCurve_eq_morse hW hθ hD lam z (-1) b
      simp only [mul_one] at hpr
      simp only [mul_neg_one, neg_mul] at hmr
      dsimp only [E, r] at *
      linear_combination hpr - hmr
    have hbound : ‖b‖ * ‖E b‖ ≤ ‖b‖ * (‖cepsScaledRootCoordinate D θ ρW lam z b‖ / (4 * s)) := by
      calc
        _ = ‖b * E b‖ := (norm_mul _ _).symm
        _ ≤ ‖r‖ / (8 * s) + ‖r‖ / (8 * s) := by rw [he]; exact (norm_sub_le _ _).trans (add_le_add hp hm)
        _ = _ := by dsimp only [r]; rw [norm_mul]; ring
    exact le_of_mul_le_mul_left hbound (norm_pos_iff.mpr hb0)
  by_cases hb0 : b = 0
  · subst b
    have hR := canonScaleRadius_pos dom hW hθ hD lam z
    have hdp : ContinuousAt (cepsScaledSignedRoot D θ ρW lam z 1) 0 :=
      (((cepsScaledSignedRoot_budget dom hW hθ hD lam hz (by norm_num : ‖(1 : ℂ)‖ ≤ 1)).1 0
        (mem_ball_self (actualRootScaleRadius_pos dom hW hθ hD lam z))).differentiableAt
        (ball_mem_nhds 0 (actualRootScaleRadius_pos dom hW hθ hD lam z))).continuousAt
    have hdm : ContinuousAt (cepsScaledSignedRoot D θ ρW lam z (-1)) 0 :=
      (((cepsScaledSignedRoot_budget dom hW hθ hD lam hz (by norm_num : ‖(-1 : ℂ)‖ ≤ 1)).1 0
        (mem_ball_self (actualRootScaleRadius_pos dom hW hθ hD lam z))).differentiableAt
        (ball_mem_nhds 0 (actualRootScaleRadius_pos dom hW hθ hD lam z))).continuousAt
    have hdc : ContinuousAt (cepsScaledRootCoordinate D θ ρW lam z) 0 :=
      (((cepsScaledRootCoordinate_budget dom hW hθ hD lam hz).1 0
        (mem_ball_self (radicandScaleRadius_budget dom hW hθ hD lam).1)).differentiableAt
        (ball_mem_nhds 0 (radicandScaleRadius_budget dom hW hθ hD lam).1)).continuousAt
    have hE : ContinuousAt (fun b => ‖E b‖) 0 := by dsimp only [E]; fun_prop
    have hC : ContinuousAt (fun b => ‖cepsScaledRootCoordinate D θ ρW lam z b‖ / (4 * s)) 0 := by fun_prop
    apply le_of_tendsto_of_tendsto
      (hE.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℂ) ≤ 𝓝 0))
      (hC.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℂ) ≤ 𝓝 0))
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (ball_mem_nhds 0 hR)] with b hne hb
    exact hnonzero b hb (by simpa using hne)
  · exact hnonzero b hb hb0

include hW hθ hD in
theorem cepsScaledRootGap_complex_sector (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z / 2)) :
    ‖cepsScaledRootCoordinate D θ ρW lam z b‖ / (2 * Real.sqrt v) ≤
      (cepsScaledSignedRoot D θ ρW lam z 1 b - cepsScaledSignedRoot D θ ρW lam z (-1) b).re := by
  have hR := canonScaleRadius_pos dom hW hθ hD lam z
  have hbR := ball_subset_ball (half_le_self hR.le) hb
  have hbr : b ∈ ball (0 : ℂ) (dom.radicandScaleRadius lam / 2) :=
    ball_subset_ball (by
      have h : dom.canonScaleRadius lam z ≤ dom.actualRootScaleRadius lam z := min_le_left _ _
      have h' : dom.actualRootScaleRadius lam z ≤ dom.radicandScaleRadius lam := min_le_left _ _
      exact div_le_div_of_nonneg_right (h.trans h') (by norm_num)) hb
  let r := cepsScaledRootCoordinate D θ ρW lam z b
  let s := Real.sqrt (cepsStepVar ρW / 2)
  let a := cepsScaledSignedRoot D θ ρW lam z 1 b - cepsScaledSignedRoot D θ ρW lam z (-1) b
  have hs : 0 < s := Real.sqrt_pos.mpr (by linarith [cepsStepVar_pos hW hθ hD])
  have hv : 0 < Real.sqrt v := Real.sqrt_pos.mpr (CepsCanonDomain.v_pos hW hθ hD)
  have hsv : s ≤ Real.sqrt v := Real.sqrt_le_sqrt (by linarith [cepsStepVar_le hW, cepsStepVar_pos hW hθ hD])
  have hsector : ‖r‖ / 2 ≤ r.re := cepsScaledRootCoordinate_complex_sector dom hW hθ hD lam hz hbr
  have herr : ‖a - 2 * r / (s : ℂ)‖ ≤ ‖r‖ / (4 * s) := cepsScaledRootGap_linear_error dom hW hθ hD lam hz hbR
  have hreal : (a - 2 * r / (s : ℂ)).re = a.re - 2 * r.re / s := by simp [Complex.div_ofReal_re, mul_re]
  have hneg := (neg_le_abs (a - 2 * r / (s : ℂ)).re).trans ((abs_re_le_norm _).trans herr)
  rw [hreal] at hneg
  have hlow : ‖r‖ / (2 * s) ≤ a.re := by
    have hr := div_le_div_of_nonneg_right hsector hs.le
    ring_nf at hneg hr ⊢
    have hnon := mul_nonneg (inv_nonneg.mpr hs.le) (norm_nonneg r)
    linarith
  exact (div_le_div_of_nonneg_left (norm_nonneg r) (by positivity) (by linarith)).trans hlow

include hW hθ hD in
theorem cepsScaledRootGap_norm_le (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z)) :
    ‖cepsScaledSignedRoot D θ ρW lam z 1 b - cepsScaledSignedRoot D θ ρW lam z (-1) b‖ ≤
      (3 / Real.sqrt (cepsVarLo D / 2)) * ‖cepsScaledRootCoordinate D θ ρW lam z b‖ := by
  let r := cepsScaledRootCoordinate D θ ρW lam z b
  let s := Real.sqrt (cepsStepVar ρW / 2)
  let s₀ := Real.sqrt (cepsVarLo D / 2)
  let a := cepsScaledSignedRoot D θ ρW lam z 1 b - cepsScaledSignedRoot D θ ρW lam z (-1) b
  have hs : 0 < s := Real.sqrt_pos.mpr (by linarith [cepsStepVar_pos hW hθ hD])
  have hs₀ : 0 < s₀ := Real.sqrt_pos.mpr (by linarith [cepsVarLo_pos hD])
  have hss : s₀ ≤ s := Real.sqrt_le_sqrt (by linarith [cepsVarLo_le hW hθ hD])
  have he : ‖a - 2 * r / (s : ℂ)‖ ≤ ‖r‖ / (4 * s) :=
    cepsScaledRootGap_linear_error dom hW hθ hD lam hz hb
  have ht := norm_add_le (a - 2 * r / (s : ℂ)) (2 * r / (s : ℂ))
  rw [sub_add_cancel, norm_div, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hs] at ht
  norm_num at ht
  have hbound : ‖a‖ ≤ (3 / s) * ‖r‖ := by
    have hnon := mul_nonneg (norm_nonneg r) (inv_nonneg.mpr hs.le)
    ring_nf at he ht ⊢
    linarith
  apply hbound.trans
  exact mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_left (by norm_num) hs₀ hss) (norm_nonneg r)

end PGM
