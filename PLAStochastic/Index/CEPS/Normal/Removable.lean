import PLAStochastic.Index.CEPS.Normal.Symmetry

/-! # One-variable removal of a common simple zero in the Morse coordinate -/

noncomputable section
open Complex Set Metric Filter Topology
namespace PGM

/-- Remove the common zero using the two complex divided differences. -/
def cepsNormalRemovedRatio (N Δ : ℂ → ℂ) (r : ℂ) : ℂ :=
  dslope N 0 r / dslope Δ 0 r

theorem cepsNormalRemovedRatio_zero (N Δ : ℂ → ℂ) :
    cepsNormalRemovedRatio N Δ 0 = deriv N 0 / deriv Δ 0 := by
  simp [cepsNormalRemovedRatio, dslope_same]

theorem cepsNormalRemovedRatio_eq {N Δ : ℂ → ℂ} (hN : N 0 = 0) (hΔ : Δ 0 = 0)
    {r : ℂ} (hr : r ≠ 0) : cepsNormalRemovedRatio N Δ r = N r / Δ r := by
  rw [cepsNormalRemovedRatio, dslope_of_ne _ hr, dslope_of_ne _ hr,
    slope_def_field, slope_def_field, hN, hΔ]
  simp only [sub_zero]
  field_simp

theorem cepsNormalRemovedRatio_even {N Δ : ℂ → ℂ} (hN : N 0 = 0) (hΔ : Δ 0 = 0)
    (heven : ∀ r, N (-r) / Δ (-r) = N r / Δ r) :
    ∀ r, cepsNormalRemovedRatio N Δ (-r) = cepsNormalRemovedRatio N Δ r := by
  intro r
  by_cases hr : r = 0
  · simp [hr]
  · rw [cepsNormalRemovedRatio_eq hN hΔ (neg_ne_zero.mpr hr),
      cepsNormalRemovedRatio_eq hN hΔ hr, heven]

/-- A common simple zero is locally removable; evenness then gives a function
holomorphic in `r²`, including the origin. The regularity and simple-zero
hypotheses concern the pre-division numerator and denominator.
-/
theorem cepsNormalRemovedRatio_holomorphic_sq {N Δ : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hN : DifferentiableOn ℂ N (ball 0 R))
    (hΔ : DifferentiableOn ℂ Δ (ball 0 R)) (hN0 : N 0 = 0) (hΔ0 : Δ 0 = 0)
    (hΔ' : deriv Δ 0 ≠ 0) (heven : ∀ r, N (-r) / Δ (-r) = N r / Δ r) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ R ∧
      DifferentiableOn ℂ (cepsNormalRemovedRatio N Δ) (ball 0 ε) ∧
      DifferentiableOn ℂ (fun z => cepsNormalRemovedRatio N Δ (Complex.sqrt z))
        (ball 0 (ε ^ 2)) := by
  have hzero : (0 : ℂ) ∈ ball (0 : ℂ) R := mem_ball_self hR
  have hNs := (differentiableOn_dslope (isOpen_ball.mem_nhds hzero)).mpr hN
  have hΔs := (differentiableOn_dslope (isOpen_ball.mem_nhds hzero)).mpr hΔ
  have hc := (hΔs 0 hzero).continuousWithinAt.continuousAt (isOpen_ball.mem_nhds hzero)
  have hne : dslope Δ 0 0 ≠ 0 := by simpa only [dslope_same] using hΔ'
  have he : ∀ᶠ r in 𝓝 (0 : ℂ), dslope Δ 0 r ≠ 0 := hc.eventually_ne hne
  obtain ⟨ε₀, hε₀, hεball⟩ := Metric.eventually_nhds_iff.mp he
  let ε := min ε₀ R
  have hε : 0 < ε := lt_min hε₀ hR
  have hsub : ball (0 : ℂ) ε ⊆ ball 0 R := ball_subset_ball (min_le_right _ _)
  have hratio : DifferentiableOn ℂ (cepsNormalRemovedRatio N Δ) (ball 0 ε) := by
    apply (hNs.mono hsub).div (hΔs.mono hsub)
    intro r hr
    apply hεball
    have hrε : ‖r‖ < ε := by simpa [mem_ball, dist_zero_right] using hr
    simpa only [dist_zero_right] using lt_of_lt_of_le hrε (show ε ≤ ε₀ from min_le_left _ _)
  exact ⟨ε, hε, min_le_right _ _, hratio,
    differentiableOn_comp_sqrt_of_even hε hratio (cepsNormalRemovedRatio_even hN0 hΔ0 heven)⟩

end PGM
