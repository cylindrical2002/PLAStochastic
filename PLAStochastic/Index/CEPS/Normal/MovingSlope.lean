import PLAStochastic.Index.CEPS.Normal.ParameterIntegral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Holomorphy of a divided difference with both endpoints moving -/

noncomputable section
open Complex Set Metric Filter Topology MeasureTheory
namespace PGM

theorem cepsNormal_segment_mem_ball {R : ℝ} {a b : ℂ} {s : ℝ}
    (ha : a ∈ ball 0 R) (hb : b ∈ ball 0 R) (hs : s ∈ Icc (0 : ℝ) 1) :
    a + (s : ℂ) * (b - a) ∈ ball 0 R := by
  have h := (convex_ball (0 : ℂ) R).lineMap_mem ha hb hs
  simpa [AffineMap.lineMap_apply, Complex.real_smul, add_comm] using h

/-- The complex divided difference is the integral of the derivative along
the segment, including coinciding endpoints.
-/
theorem cepsNormal_dslope_eq_integral {g : ℂ → ℂ} {R : ℝ}
    (hg : DifferentiableOn ℂ g (ball 0 R)) {a b : ℂ}
    (ha : a ∈ ball 0 R) (hb : b ∈ ball 0 R) :
    dslope g a b = ∫ s in (0 : ℝ)..1, deriv g (a + (s : ℂ) * (b - a)) := by
  have hpath : ∀ s ∈ Icc (0 : ℝ) 1, a + (s : ℂ) * (b - a) ∈ ball 0 R :=
    fun s hs => cepsNormal_segment_mem_ball ha hb hs
  have hc : ContinuousOn (fun s : ℝ => deriv g (a + s • (b - a))) (Icc 0 1) :=
    (hg.deriv isOpen_ball).continuousOn.comp (by fun_prop)
      (fun s hs => by simpa only [Complex.real_smul] using hpath s hs)
  by_cases he : b = a
  · rw [he, dslope_same]
    simp
  · have hFTC := intervalIntegral.integral_unitInterval_deriv_eq_sub
      (z₀ := a) (z₁ := b - a) hc (fun s hs =>
        ((hg _ (by simpa only [Complex.real_smul] using hpath s hs)).differentiableAt
          (isOpen_ball.mem_nhds (by simpa only [Complex.real_smul] using hpath s hs))).hasDerivAt)
    rw [smul_eq_mul, add_sub_cancel] at hFTC
    simp only [Complex.real_smul] at hFTC
    rw [dslope_of_ne _ he, slope_def_field]
    exact (div_eq_iff (sub_ne_zero.mpr he)).2 (by simpa [mul_comm] using hFTC.symm)

/-- A genuine moving-center result. `G` is holomorphic in space, and its
spatial derivative is jointly holomorphic in parameter/space on the product
domain. Neither endpoint is required to stay distinct from the other.
-/
theorem cepsNormal_differentiableOn_moving_dslope
    {U : Set ℂ} (hU : IsOpen U) {G : ℂ → ℂ → ℂ} {R : ℝ}
    (hG : ∀ r ∈ U, DifferentiableOn ℂ (G r) (ball 0 R))
    (hGζ : DifferentiableOn ℂ (fun x : ℂ × ℂ => deriv (G x.1) x.2) (U ×ˢ ball 0 R))
    {a b : ℂ → ℂ} (ha : DifferentiableOn ℂ a U) (hb : DifferentiableOn ℂ b U)
    (hamap : MapsTo a U (ball 0 R)) (hbmap : MapsTo b U (ball 0 R)) :
    DifferentiableOn ℂ (fun r => dslope (G r) (a r) (b r)) U := by
  let F : ℂ → ℝ → ℂ := fun r s => deriv (G r) (a r + (s : ℂ) * (b r - a r))
  have hmap : ∀ x : ℂ × ℝ, x ∈ U ×ˢ Icc (0 : ℝ) 1 →
      (x.1, a x.1 + (x.2 : ℂ) * (b x.1 - a x.1)) ∈ U ×ˢ ball (0 : ℂ) R := by
    intro x hx
    exact ⟨hx.1, cepsNormal_segment_mem_ball (hamap hx.1) (hbmap hx.1) hx.2⟩
  have hca : ContinuousOn (fun x : ℂ × ℝ => a x.1) (U ×ˢ Icc (0 : ℝ) 1) :=
    ha.continuousOn.comp continuousOn_fst (fun _ hx => hx.1)
  have hcb : ContinuousOn (fun x : ℂ × ℝ => b x.1) (U ×ˢ Icc (0 : ℝ) 1) :=
    hb.continuousOn.comp continuousOn_fst (fun _ hx => hx.1)
  have hcS : ContinuousOn (fun x : ℂ × ℝ => (x.2 : ℂ)) (U ×ˢ Icc (0 : ℝ) 1) := by
    fun_prop
  have hpath : ContinuousOn (fun x : ℂ × ℝ =>
      (x.1, a x.1 + (x.2 : ℂ) * (b x.1 - a x.1))) (U ×ˢ Icc (0 : ℝ) 1) :=
    continuousOn_fst.prodMk (hca.add (hcS.mul (hcb.sub hca)))
  have hcF : ContinuousOn (fun x : ℂ × ℝ => F x.1 x.2) (U ×ˢ Icc (0 : ℝ) 1) :=
    hGζ.continuousOn.comp hpath hmap
  have hdF : ∀ s ∈ Icc (0 : ℝ) 1, DifferentiableOn ℂ (fun r => F r s) U := by
    intro s hs
    have hp := differentiableOn_id.prodMk (ha.add ((hb.sub ha).const_mul (s : ℂ)))
    exact hGζ.comp hp (fun r hr =>
      ⟨hr, cepsNormal_segment_mem_ball (hamap hr) (hbmap hr) hs⟩)
  have hmain := cepsNormal_differentiableOn_parameterIntegral hU hcF hdF
  apply hmain.congr
  intro r hr
  exact cepsNormal_dslope_eq_integral (hG r hr) (hamap hr) (hbmap hr)

end PGM
