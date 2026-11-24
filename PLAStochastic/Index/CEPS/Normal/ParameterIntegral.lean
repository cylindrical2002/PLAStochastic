import PLAStochastic.ForMathlib.Analysis.Complex.Osgood

/-! # Holomorphic compact-interval parameter integrals

Joint continuity and holomorphy in the complex parameter suffice; continuity
of the parameter derivative is not assumed. Cauchy bounds supply domination,
and measurable difference quotients supply measurable derivatives.
-/

noncomputable section
open Complex Set Metric Filter Topology MeasureTheory
namespace PGM

set_option maxHeartbeats 800000 in
theorem cepsNormal_differentiableOn_parameterIntegral {U : Set ℂ}
    (hU : IsOpen U) {F : ℂ → ℝ → ℂ}
    (hc : ContinuousOn (fun x : ℂ × ℝ => F x.1 x.2) (U ×ˢ Icc 0 1))
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, DifferentiableOn ℂ (fun r => F r s) U) :
    DifferentiableOn ℂ (fun r => ∫ s in (0 : ℝ)..1, F r s) U := by
  intro r₀ hr₀
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU r₀ hr₀
  let R := ε / 3
  have hR : 0 < R := by dsimp [R]; positivity
  have hsub : closedBall r₀ (2 * R) ⊆ U :=
    (closedBall_subset_ball (by dsimp [R]; linarith)).trans hεU
  have hsub' : ball r₀ R ⊆ U := (ball_subset_closedBall.trans
    (closedBall_subset_closedBall (by linarith))).trans hsub
  have hcompact := (isCompact_closedBall r₀ (2 * R)).prod (isCompact_Icc (a := (0 : ℝ)) (b := 1))
  obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuousOn
    (hc.mono (fun x hx => ⟨hsub hx.1, hx.2⟩))
  have hpoint : ∀ r ∈ ball r₀ R, ∀ z ∈ ball r R, z ∈ closedBall r₀ (2 * R) := by
    intro r hr z hz
    rw [mem_ball] at hr hz
    rw [mem_closedBall]
    exact (dist_triangle z r r₀).trans (by linarith)
  have hbound : ∀ r ∈ ball r₀ R, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖deriv (fun r => F r s) r‖ ≤ 2 * M / R := by
    intro r hr s hs
    have hdiff : DifferentiableOn ℂ (fun r => F r s) (ball r R) :=
      (hd s hs).mono (fun z hz => hsub (hpoint r hr z hz))
    have hb : ∀ z ∈ ball r R, ‖F z s‖ ≤ M := fun z hz => hM (z, s) ⟨hpoint r hr z hz, hs⟩
    have h := norm_iteratedDeriv_le_of_ball 1 hR hdiff hb
    rw [iteratedDeriv_one] at h
    convert h using 1
    simp
    ring
  have hslice : ∀ r ∈ ball r₀ R, ContinuousOn (F r) (Icc (0 : ℝ) 1) := by
    intro r hr
    exact hc.comp ((continuous_const.prodMk continuous_id).continuousOn)
      (fun s hs => ⟨hsub' hr, hs⟩)
  have hmeas : ∀ r ∈ ball r₀ R, AEStronglyMeasurable (F r) (volume.restrict (Ioc (0 : ℝ) 1)) := by
    intro r hr
    exact ((hslice r hr).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hrball : r₀ ∈ ball r₀ R := mem_ball_self hR
  let H : ℕ → ℂ := fun n => ((R / 2 / (n + 1) : ℝ) : ℂ)
  obtain ⟨hH0, hHlim⟩ := tendsto_ofReal_div_succ (by positivity : 0 < R / 2)
  have hHmem : ∀ n, r₀ + H n ∈ ball r₀ R := by
    intro n
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    dsimp [H]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hle : R / 2 / ((n : ℝ) + 1) ≤ R / 2 :=
      div_le_self (by positivity) (by have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)
    linarith
  have hdmeas : AEStronglyMeasurable (fun s => deriv (fun r => F r s) r₀)
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n s => (H n)⁻¹ • (F (r₀ + H n) s - F r₀ s))
      (fun n => by
        exact aestronglyMeasurable_const.mul ((hmeas _ (hHmem n)).sub (hmeas _ hrball))) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hsd := ((hd s (Ioc_subset_Icc_self hs)) r₀ hr₀).differentiableAt (hU.mem_nhds hr₀)
    have hlim : Tendsto H atTop (𝓝[≠] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨hHlim, Eventually.of_forall hH0⟩
    exact hsd.hasDerivAt.tendsto_slope_zero.comp hlim
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := 0) (b := 1) (s := ball r₀ R) (F := F)
    (F' := fun r s => deriv (fun r => F r s) r) (bound := fun _ => 2 * M / R)
    (ball_mem_nhds r₀ hR) ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
  · exact hmain.2.differentiableAt.differentiableWithinAt
  · filter_upwards [ball_mem_nhds r₀ hR] with r hr
    rw [uIoc_of_le zero_le_one]
    exact hmeas r hr
  · exact (hslice r₀ hrball).intervalIntegrable_of_Icc zero_le_one
  · rwa [uIoc_of_le zero_le_one]
  · exact Eventually.of_forall fun s hs r hr => hbound r hr s
      (by simpa [uIoc_of_le zero_le_one] using Ioc_subset_Icc_self hs)
  · refine Eventually.of_forall fun s hs r hr => ?_
    have hs' : s ∈ Icc (0 : ℝ) 1 := by
      apply Ioc_subset_Icc_self
      simpa [uIoc_of_le zero_le_one] using hs
    exact (((hd s hs') r (hsub' hr)).differentiableAt (hU.mem_nhds (hsub' hr))).hasDerivAt

end PGM
