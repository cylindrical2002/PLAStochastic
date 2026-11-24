import PLAStochastic.Index.CEPS.Normal.SlopeDerivative
import Mathlib.Analysis.Complex.RemovableSingularity

/-! # Moving second divided differences, including all diagonals -/

noncomputable section
open Complex Set Metric
namespace PGM

theorem cepsNormal_moving_dslope_of_analytic {U : Set ℂ} (hU : IsOpen U) {R : ℝ}
    {G : ℂ → ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ (fun x : ℂ × ℂ => G x.1 x.2) (U ×ˢ ball 0 R))
    {a b : ℂ → ℂ} (ha : DifferentiableOn ℂ a U) (hb : DifferentiableOn ℂ b U)
    (hamap : MapsTo a U (ball 0 R)) (hbmap : MapsTo b U (ball 0 R)) :
    DifferentiableOn ℂ (fun r => dslope (G r) (a r) (b r)) U := by
  have hs : ∀ r ∈ U, DifferentiableOn ℂ (G r) (ball 0 R) := fun r hr z hz =>
    (hG (r, z) ⟨hr, hz⟩).curry_right.differentiableAt.differentiableWithinAt
  exact cepsNormal_differentiableOn_moving_dslope hU hs
    (cepsNormal_analyticOnNhd_spatial_deriv hU hG).differentiableOn ha hb hamap hbmap

theorem cepsNormal_moving_second_dslope {U : Set ℂ} (hU : IsOpen U) {R : ℝ}
    {G : ℂ → ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ (fun x : ℂ × ℂ => G x.1 x.2) (U ×ˢ ball 0 R))
    {b a t : ℂ → ℂ} (hb : DifferentiableOn ℂ b U)
    (ha : DifferentiableOn ℂ a U) (ht : DifferentiableOn ℂ t U)
    (hbmap : MapsTo b U (ball 0 R)) (hamap : MapsTo a U (ball 0 R))
    (htmap : MapsTo t U (ball 0 R)) :
    DifferentiableOn ℂ (fun r => dslope (dslope (G r) (b r)) (a r) (t r)) U := by
  have hs : ∀ r ∈ U, DifferentiableOn ℂ (G r) (ball 0 R) := fun r hr z hz =>
    (hG (r, z) ⟨hr, hz⟩).curry_right.differentiableAt.differentiableWithinAt
  have hGζ := cepsNormal_analyticOnNhd_spatial_deriv hU hG
  have hGζζ := cepsNormal_analyticOnNhd_spatial_deriv (G := fun r => deriv (G r)) hU hGζ
  have hI : DifferentiableOn ℂ
      (fun x : ℂ × ℂ => ∫ s in (0 : ℝ)..1,
        (s : ℂ) * deriv (deriv (G x.1)) (b x.1 + (s : ℂ) * (x.2 - b x.1)))
      (U ×ˢ ball 0 R) := by
    intro x hx
    exact (cepsNormal_hasFDerivAt_weighted_segmentIntegral (D := fun x : ℂ × ℂ =>
      deriv (deriv (G x.1)) x.2) hU hGζζ (hb.analyticOnNhd hU) hbmap
      (by fun_prop : ContinuousOn (fun s : ℝ => (s : ℂ)) (Icc 0 1)) hx).differentiableAt.differentiableWithinAt
  have hHζ : DifferentiableOn ℂ
      (fun x : ℂ × ℂ => deriv (dslope (G x.1) (b x.1)) x.2) (U ×ˢ ball 0 R) := by
    apply hI.congr
    intro x hx
    exact cepsNormal_deriv_dslope_eq_integral (hs x.1 hx.1) (hbmap hx.1) hx.2
  have hH : ∀ r ∈ U, DifferentiableOn ℂ (dslope (G r) (b r)) (ball 0 R) := by
    intro r hr
    exact (differentiableOn_dslope (isOpen_ball.mem_nhds (hbmap hr))).mpr (hs r hr)
  exact cepsNormal_differentiableOn_moving_dslope (G := fun r => dslope (G r) (b r))
    hU hH hHζ ha ht hamap htmap

end PGM
