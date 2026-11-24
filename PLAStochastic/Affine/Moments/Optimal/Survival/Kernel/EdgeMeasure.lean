import PLAStochastic.Affine.Moments.Optimal.Laplace.Convolution
import Mathlib.MeasureTheory.Measure.WithDensity

/-! # Finite edge measures for the actual boundary convolution -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- Exponential weighting at k=1 gives total mass at most two, uniformly in the starting point. -/
def optimalSurvivalEdgeMeasure (a : ℝ) : Measure ℝ :=
  ((volume : Measure ℝ).restrict (Ioi 0)).withDensity
    (fun t => ENNReal.ofReal (Real.exp (-t/2)*heatBoundaryLeft 1 t a))

theorem integrable_optimalSurvivalEdgeWeight {a : ℝ} (ha : a ∈ Ioo 0 1) :
    IntegrableOn (fun t => Real.exp (-t/2)*heatBoundaryLeft 1 t a) (Ioi 0) := by
  have he (t : ℝ) : Real.exp (-t/2)*heatBoundaryLeft 1 t a =
      Real.exp (-(1^2/2)*t)*heatBoundaryLeft 1 t a := by
    apply congrArg (fun u : ℝ => Real.exp u * heatBoundaryLeft 1 t a)
    ring
  simp_rw [he]
  exact integrableOn_laplace_heatBoundaryLeft (by norm_num) (by norm_num) ha

theorem optimalSurvivalEdgeWeight_nonneg_ae {a : ℝ} (ha : a ∈ Ioo 0 1) :
    0 ≤ᵐ[(volume : Measure ℝ).restrict (Ioi 0)]
      (fun t => Real.exp (-t/2)*heatBoundaryLeft 1 t a) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact mul_nonneg (Real.exp_nonneg _) (heatBoundaryLeft_strictlyPositive (by norm_num) ht ha).le

theorem isFiniteMeasure_optimalSurvivalEdgeMeasure {a : ℝ} (ha : a ∈ Ioo 0 1) :
    IsFiniteMeasure (optimalSurvivalEdgeMeasure a) := by
  apply isFiniteMeasure_withDensity
  exact (hasFiniteIntegral_iff_ofReal (optimalSurvivalEdgeWeight_nonneg_ae ha)).mp
    (integrable_optimalSurvivalEdgeWeight ha).hasFiniteIntegral |>.ne

theorem optimalSurvivalEdgeMeasure_univ {a : ℝ} (ha : a ∈ Ioo 0 1) :
    optimalSurvivalEdgeMeasure a univ = ENNReal.ofReal (2*Real.sinh (1-a)/Real.sinh 1) := by
  rw [optimalSurvivalEdgeMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_optimalSurvivalEdgeWeight ha)
      (optimalSurvivalEdgeWeight_nonneg_ae ha)]
  congr 1
  have hh := integral_laplace_heatBoundaryLeft_eq_sinh (by norm_num : (0 : ℝ)<1)
    (by norm_num : (0 : ℝ)<1) ha
  calc
    _ = ∫ t in Ioi (0 : ℝ), Real.exp (-(1^2/2)*t)*heatBoundaryLeft 1 t a := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      apply congrArg (fun u : ℝ => Real.exp u * heatBoundaryLeft 1 t a)
      ring
    _ = _ := by simpa only [one_mul, mul_one] using hh

theorem optimalSurvivalEdgeMeasure_univ_le_two {a : ℝ} (ha : a ∈ Ioo 0 1) :
    optimalSurvivalEdgeMeasure a univ ≤ 2 := by
  rw [optimalSurvivalEdgeMeasure_univ ha]
  have hs : 0 < Real.sinh (1 : ℝ) := Real.sinh_pos_iff.mpr zero_lt_one
  have he : 2*Real.sinh (1-a)/Real.sinh 1 ≤ 2 := by
    apply (div_le_iff₀ hs).mpr
    have hh := Real.sinh_le_sinh.mpr (show 1-a ≤ 1 by linarith [ha.1])
    linarith
  exact (ENNReal.ofReal_le_ofReal he).trans_eq (by norm_num)

theorem optimalSurvivalEdgeMeasure_apply {a : ℝ} {s : Set ℝ} (hs : MeasurableSet s) :
    optimalSurvivalEdgeMeasure a s = ∫⁻ t in s ∩ Ioi (0 : ℝ),
      ENNReal.ofReal (Real.exp (-t/2)*heatBoundaryLeft 1 t a) := by
  rw [optimalSurvivalEdgeMeasure, withDensity_apply _ hs, Measure.restrict_restrict hs]

end BrownianAffine
