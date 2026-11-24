import PLAStochastic.Index.CEPS.Scaled.CenterScale
import PLAStochastic.Index.CEPS.Scaled.RootCurvePair
import PLAStochastic.Index.CEPS.Scaled.ComplexRootDifference

/-! # Actual signed scaled roots relative to the removable center -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledRoot_individual_linear_error (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    {sign : ℂ} (hsign : ‖sign‖ ≤ 1) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z)) :
    ‖cepsScaledSignedRoot D θ ρW lam z sign b - cepsScaledMorseCenter D θ ρW lam b -
      sign * cepsScaledRootCoordinate D θ ρW lam z b / (Real.sqrt (cepsStepVar ρW / 2) : ℂ)‖ ≤
      ‖cepsScaledRootCoordinate D θ ρW lam z b‖ / (8 * Real.sqrt (cepsStepVar ρW / 2)) := by
  let s := Real.sqrt (cepsStepVar ρW / 2)
  have hs : 0 < s := Real.sqrt_pos.mpr (by linarith [cepsStepVar_pos hW hθ hD])
  let E : ℂ → ℂ := fun b => cepsScaledSignedRoot D θ ρW lam z sign b -
    cepsScaledMorseCenter D θ ρW lam b - sign * cepsScaledRootCoordinate D θ ρW lam z b / (s : ℂ)
  have hnonzero : ∀ b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z), b ≠ 0 →
      ‖E b‖ ≤ ‖cepsScaledRootCoordinate D θ ρW lam z b‖ / (8 * s) := by
    intro b hb hb0
    let r := b * sign * cepsScaledRootCoordinate D θ ρW lam z b
    have hsub : b ∈ ball (0 : ℂ) (dom.actualRootScaleRadius lam z) := ball_subset_ball (min_le_left _ _) hb
    have hbr : b ∈ ball (0 : ℂ) (dom.radicandScaleRadius lam) := ball_subset_ball (min_le_left _ _) hsub
    have hn : ‖b‖ < dom.rmax / (4 * (1 + dom.scaledRootCoordinateBound lam z)) :=
      (mem_ball_zero_iff.mp hsub).trans_le (min_le_right _ _)
    have hS : 0 ≤ dom.scaledRootCoordinateBound lam z := Real.sqrt_nonneg _
    have hmul := (lt_div_iff₀ (by positivity : 0 < 4 * (1 + dom.scaledRootCoordinateBound lam z))).mp hn
    have hnorm : ‖r‖ ≤ ‖b‖ * ‖cepsScaledRootCoordinate D θ ρW lam z b‖ := by
      rw [norm_mul, norm_mul]
      calc
        _ ≤ ‖b‖ * 1 * ‖cepsScaledRootCoordinate D θ ρW lam z b‖ := by gcongr
        _ = _ := by ring
    have hr : ‖r‖ < cepsChartRho D θ := by
      have hcoord := (cepsScaledRootCoordinate_budget dom hW hθ hD lam hz).2 b hbr
      have ht : ‖r‖ ≤ ‖b‖ * dom.scaledRootCoordinateBound lam z :=
        hnorm.trans (mul_le_mul_of_nonneg_left hcoord (norm_nonneg b))
      have := dom.rmax_r1; have := dom.rmax_pos
      nlinarith [norm_nonneg b]
    have hμ : ‖b * (lam : ℂ)‖ < cepsChartMu D θ := dom.μ_lt_chart
      ((canonScaleCurve_bounds dom hW hθ hD lam hz hsign hb).1.le.trans (by linarith [dom.μ₀_pos]))
    have herr := cepsMorseRoot_linear_error hW hθ hD hμ hr
    have he : b * E b = cepsMorseRoot D θ ρW (b * lam) r -
        cepsMorseCenter D θ ρW (b * lam) - r / (s : ℂ) := by
      have hroot := cepsScaledRootCurve_eq_morse hW hθ hD lam z sign b
      have hcenter := cepsScaledMorseCenter_actual hW hθ hD lam b
      dsimp only [E, r]
      linear_combination hroot - hcenter
    have hbnd : ‖b‖ * ‖E b‖ ≤ ‖b‖ * (‖cepsScaledRootCoordinate D θ ρW lam z b‖ / (8 * s)) := by
      calc
        _ = ‖b * E b‖ := (norm_mul _ _).symm
        _ ≤ ‖r‖ / (8 * s) := by rw [he]; exact herr
        _ ≤ (‖b‖ * ‖cepsScaledRootCoordinate D θ ρW lam z b‖) / (8 * s) :=
          div_le_div_of_nonneg_right hnorm (by positivity)
        _ = _ := by ring
    exact le_of_mul_le_mul_left hbnd (norm_pos_iff.mpr hb0)
  by_cases hb0 : b = 0
  · subst b
    have hR := canonScaleRadius_pos dom hW hθ hD lam z
    have hdp : ContinuousAt (cepsScaledSignedRoot D θ ρW lam z sign) 0 :=
      (((cepsScaledSignedRoot_budget dom hW hθ hD lam hz hsign).1 0
        (mem_ball_self (actualRootScaleRadius_pos dom hW hθ hD lam z))).differentiableAt
        (ball_mem_nhds 0 (actualRootScaleRadius_pos dom hW hθ hD lam z))).continuousAt
    have hdm : ContinuousAt (cepsScaledMorseCenter D θ ρW lam) 0 :=
      (((cepsScaledMorseCenter_budget dom hW hθ hD lam hz).1 0
        (mem_ball_self hR)).differentiableAt (ball_mem_nhds 0 hR)).continuousAt
    have hdc : ContinuousAt (cepsScaledRootCoordinate D θ ρW lam z) 0 :=
      (((cepsScaledRootCoordinate_budget dom hW hθ hD lam hz).1 0
        (mem_ball_self (radicandScaleRadius_budget dom hW hθ hD lam).1)).differentiableAt
        (ball_mem_nhds 0 (radicandScaleRadius_budget dom hW hθ hD lam).1)).continuousAt
    have hE : ContinuousAt (fun b => ‖E b‖) 0 := by dsimp only [E]; fun_prop
    have hC : ContinuousAt (fun b => ‖cepsScaledRootCoordinate D θ ρW lam z b‖ / (8 * s)) 0 := by fun_prop
    apply le_of_tendsto_of_tendsto
      (hE.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℂ) ≤ 𝓝 0))
      (hC.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℂ) ≤ 𝓝 0))
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (ball_mem_nhds 0 hR)] with b hne hb
    exact hnonzero b hb (by simpa using hne)
  · exact hnonzero b hb hb0

end PGM
