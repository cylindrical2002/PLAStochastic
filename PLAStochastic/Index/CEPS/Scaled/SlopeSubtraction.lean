import PLAStochastic.Index.CEPS.Scaled.WeightedFirstSlope
import PLAStochastic.Index.CEPS.Scaled.WeightedSlopeBudget

/-! # Linearity and weighted error bounds of spatial divided differences -/

noncomputable section
open Complex Set Metric
namespace PGM

theorem cepsNormal_dslope_sub {f g : ℂ → ℂ} {a : ℂ}
    (hf : DifferentiableAt ℂ f a) (hg : DifferentiableAt ℂ g a) (t : ℂ) :
    dslope (fun ζ => f ζ - g ζ) a t = dslope f a t - dslope g a t := by
  by_cases ht : t = a
  · subst t
    rw [dslope_same, dslope_same, dslope_same]
    simpa only [Pi.sub_apply] using! deriv_sub hf hg
  · rw [dslope_of_ne _ ht, dslope_of_ne _ ht, dslope_of_ne _ ht]
    simp only [slope_def_field]
    ring

theorem cepsNormal_second_dslope_sub {f g : ℂ → ℂ} {R : ℝ}
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hg : DifferentiableOn ℂ g (ball 0 R))
    {a b : ℂ} (ha : a ∈ ball (0 : ℂ) R) (hb : b ∈ ball (0 : ℂ) R) (t : ℂ) :
    dslope (dslope (fun ζ => f ζ - g ζ) a) b t =
      dslope (dslope f a) b t - dslope (dslope g a) b t := by
  have hfa := (hf a ha).differentiableAt (isOpen_ball.mem_nhds ha)
  have hga := (hg a ha).differentiableAt (isOpen_ball.mem_nhds ha)
  have hdF := (differentiableOn_dslope (isOpen_ball.mem_nhds ha)).mpr hf
  have hdG := (differentiableOn_dslope (isOpen_ball.mem_nhds ha)).mpr hg
  have he : dslope (fun ζ => f ζ - g ζ) a = fun ζ => dslope f a ζ - dslope g a ζ :=
    funext (cepsNormal_dslope_sub hfa hga)
  rw [he, cepsNormal_dslope_sub
    ((hdF b hb).differentiableAt (isOpen_ball.mem_nhds hb))
    ((hdG b hb).differentiableAt (isOpen_ball.mem_nhds hb))]

theorem cepsNormal_norm_dslope_sub_le_weighted {f g : ℂ → ℂ} {R C : ℝ} {w : ℂ}
    (hR : 0 < R) (hC : 0 ≤ C) (hf : DifferentiableOn ℂ f (ball 0 R))
    (hg : DifferentiableOn ℂ g (ball 0 R))
    (hderiv : ∀ ξ : ℂ, ‖ξ‖ ≤ R / 2 → ‖deriv f ξ - deriv g ξ‖ ≤ C * Real.exp (-(ξ * w).re))
    {a t : ℂ} (ha : ‖a‖ ≤ R / 2) (ht : ‖t‖ ≤ R / 2) :
    ‖dslope f a t - dslope g a t‖ ≤
      C * (Real.exp (-(a * w).re) + Real.exp (-(t * w).re)) := by
  have hmem : ∀ ξ : ℂ, ‖ξ‖ ≤ R / 2 → ξ ∈ ball (0 : ℂ) R :=
    fun ξ hξ => mem_ball_zero_iff.mpr (hξ.trans_lt (half_lt_self hR))
  have hfa := (hf a (hmem a ha)).differentiableAt (isOpen_ball.mem_nhds (hmem a ha))
  have hga := (hg a (hmem a ha)).differentiableAt (isOpen_ball.mem_nhds (hmem a ha))
  rw [← cepsNormal_dslope_sub hfa hga t]
  apply cepsNormal_norm_dslope_le_weighted hR hC (hf.sub hg) _ ha ht
  intro ξ hξ
  rw [deriv_sub ((hf ξ (hmem ξ hξ)).differentiableAt (isOpen_ball.mem_nhds (hmem ξ hξ)))
    ((hg ξ (hmem ξ hξ)).differentiableAt (isOpen_ball.mem_nhds (hmem ξ hξ)))]
  exact hderiv ξ hξ

theorem cepsNormal_norm_second_dslope_sub_le_weighted {f g : ℂ → ℂ} {R C : ℝ} {w : ℂ}
    (hR : 0 < R) (hC : 0 ≤ C) (hf : DifferentiableOn ℂ f (ball 0 R))
    (hg : DifferentiableOn ℂ g (ball 0 R))
    (hderiv : ∀ ξ : ℂ, ‖ξ‖ ≤ R / 2 →
      ‖iteratedDeriv 2 f ξ - iteratedDeriv 2 g ξ‖ ≤ C * Real.exp (-(ξ * w).re))
    {a b t : ℂ} (ha : ‖a‖ ≤ R / 2) (hb : ‖b‖ ≤ R / 2) (ht : ‖t‖ ≤ R / 2) :
    ‖dslope (dslope f a) b t - dslope (dslope g a) b t‖ ≤
      C * (Real.exp (-(a * w).re) + Real.exp (-(b * w).re) + Real.exp (-(t * w).re)) := by
  have hmem : ∀ ξ : ℂ, ‖ξ‖ ≤ R / 2 → ξ ∈ ball (0 : ℂ) R :=
    fun ξ hξ => mem_ball_zero_iff.mpr (hξ.trans_lt (half_lt_self hR))
  rw [← cepsNormal_second_dslope_sub hf hg (hmem a ha) (hmem b hb) t]
  apply cepsNormal_norm_second_dslope_le_weighted hR hC (hf.sub hg) _ ha hb ht
  intro ξ hξ
  have hCA : ContDiffAt ℂ 2 f ξ := ((hf.analyticOnNhd isOpen_ball) ξ (hmem ξ hξ)).contDiffAt
  have hCB : ContDiffAt ℂ 2 g ξ := ((hg.analyticOnNhd isOpen_ball) ξ (hmem ξ hξ)).contDiffAt
  have he := iteratedDeriv_sub hCA hCB
  have h := hderiv ξ hξ
  rw [← he] at h
  simpa only [iteratedDeriv_succ, iteratedDeriv_one] using! h

end PGM
