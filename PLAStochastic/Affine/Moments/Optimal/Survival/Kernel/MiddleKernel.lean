import PLAStochastic.Affine.Moments.Optimal.Survival.Image.CrossBound
import PLAStochastic.Brownian.Killed.Width.UniformQuotient

/-! # A bounded continuous middle kernel for the actual survival convolution -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

def heatCrossZeroExtension (t : ℝ) : ℝ := if 0 < t then heatCrossBoundary 1 t else 0

theorem heatCrossZeroExtension_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    heatCrossZeroExtension t = 0 := by simp [heatCrossZeroExtension, not_lt.mpr ht]

theorem continuous_heatCrossZeroExtension : Continuous heatCrossZeroExtension := by
  apply continuous_iff_continuousAt.mpr
  intro t
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have he : heatCrossZeroExtension =ᶠ[𝓝 t] (fun _ => 0) := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      exact heatCrossZeroExtension_of_nonpos hs.le
    exact continuousAt_const.congr_of_eventuallyEq he
  · rw [continuousAt_iff_continuous_left'_right']
    constructor
    · change Tendsto heatCrossZeroExtension (𝓝[<] (0 : ℝ)) (𝓝 (heatCrossZeroExtension 0))
      rw [heatCrossZeroExtension_of_nonpos le_rfl]
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (heatCrossZeroExtension_of_nonpos hs.le).symm
    · change Tendsto heatCrossZeroExtension (𝓝[>] (0 : ℝ)) (𝓝 (heatCrossZeroExtension 0))
      rw [heatCrossZeroExtension_of_nonpos le_rfl]
      apply tendsto_heatCrossBoundary_zero.congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      simp [heatCrossZeroExtension, show 0 < s from hs]
  · have he : heatCrossZeroExtension =ᶠ[𝓝 t] (heatCrossBoundary 1) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      simp [heatCrossZeroExtension, show 0 < s from hs]
    have hh := (continuousOn_heatCrossBoundary_time (by norm_num : (0 : ℝ)<1)
      (K := Ioi 0) (fun _ hs => hs)) t ht
    exact (hh.continuousAt (Ioi_mem_nhds ht)).congr_of_eventuallyEq he

theorem norm_heatCrossBoundary_large_time {t : ℝ} (ht : 1 ≤ t) :
    ‖heatCrossBoundary 1 t‖ ≤ ∑' n, heatSpatialBound 1 1 1 1 n := by
  unfold heatCrossBoundary heatSpatialSeries
  rw [norm_neg]
  exact tsum_of_norm_bounded
    (summable_heatSpatialBound (by norm_num : (0 : ℝ)<1) (by norm_num : (0 : ℝ)<1) 1 1).hasSum
    (fun n => heatSpatialMode_bound (by norm_num) (by norm_num) ht 1 1 n 1 0)

theorem bddAbove_norm_heatCrossZeroExtension :
    BddAbove (range (fun t => ‖heatCrossZeroExtension t‖)) := by
  obtain ⟨M,hM⟩ := isCompact_Icc.bddAbove_image
    (continuous_heatCrossZeroExtension.norm.continuousOn (s := Icc (0 : ℝ) 1))
  have hM0 : 0 ≤ M := by
    have hh := hM (mem_image_of_mem (fun t => ‖heatCrossZeroExtension t‖)
      (show (0 : ℝ) ∈ Icc 0 1 by norm_num))
    simpa only [heatCrossZeroExtension_of_nonpos le_rfl, norm_zero] using hh
  refine ⟨max M (∑' n, heatSpatialBound 1 1 1 1 n), ?_⟩
  rintro _ ⟨t,rfl⟩
  dsimp only
  by_cases ht0 : t ≤ 0
  · rw [heatCrossZeroExtension_of_nonpos ht0, norm_zero]
    exact hM0.trans (le_max_left _ _)
  by_cases ht1 : t ≤ 1
  · exact (hM (mem_image_of_mem (fun t => ‖heatCrossZeroExtension t‖)
      ⟨le_of_not_ge ht0,ht1⟩)).trans (le_max_left _ _)
  · rw [heatCrossZeroExtension, if_pos (lt_of_not_ge ht0)]
    exact (norm_heatCrossBoundary_large_time (le_of_not_ge ht1)).trans (le_max_right _ _)

/-- The exponential rate one half matches the already proved edge Laplace laws at k=1. -/
def optimalSurvivalMiddleKernel (t : ℝ) : ℝ :=
  Real.exp (-t/2) * t * heatCrossZeroExtension t

theorem continuous_optimalSurvivalMiddleKernel : Continuous optimalSurvivalMiddleKernel := by
  unfold optimalSurvivalMiddleKernel
  exact ((by fun_prop : Continuous (fun t : ℝ => Real.exp (-t/2))).mul continuous_id).mul
    continuous_heatCrossZeroExtension

theorem optimalSurvivalMiddleKernel_nonneg (t : ℝ) : 0 ≤ optimalSurvivalMiddleKernel t := by
  by_cases ht : 0 < t
  · unfold optimalSurvivalMiddleKernel heatCrossZeroExtension
    rw [if_pos ht]
    exact mul_nonneg (by positivity) (heatCrossBoundary_strictlyPositive (by norm_num) ht).le
  · simp [optimalSurvivalMiddleKernel, heatCrossZeroExtension_of_nonpos (le_of_not_gt ht)]

theorem bddAbove_norm_optimalSurvivalMiddleKernel :
    BddAbove (range (fun t => ‖optimalSurvivalMiddleKernel t‖)) := by
  obtain ⟨M,hM⟩ := bddAbove_norm_heatCrossZeroExtension
  have hM0 : 0 ≤ M := (norm_nonneg (heatCrossZeroExtension 0)).trans (hM (mem_range_self 0))
  refine ⟨2*M, ?_⟩
  rintro _ ⟨t,rfl⟩
  dsimp only
  by_cases ht : 0 < t
  swap
  · simp only [optimalSurvivalMiddleKernel, heatCrossZeroExtension_of_nonpos (le_of_not_gt ht),
      mul_zero, norm_zero]
    positivity
  have he : Real.exp (-t/2)*t ≤ 2 := by
    have hh := mul_le_mul_of_nonneg_right (show t/2 ≤ Real.exp (t/2) by
      linarith [Real.add_one_le_exp (t/2)]) (Real.exp_nonneg (-t/2))
    rw [← Real.exp_add, show t/2 + -t/2 = 0 by ring, Real.exp_zero] at hh
    nlinarith
  unfold optimalSurvivalMiddleKernel
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (mul_pos (Real.exp_pos _) ht)]
  exact mul_le_mul he (hM (mem_range_self t)) (norm_nonneg _) (by norm_num)

end BrownianAffine
