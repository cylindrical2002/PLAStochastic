import PLAStochastic.Affine.Moments.Optimal.Survival.Image.CrossKernel
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Gaussian small-time decay of the actual cross-boundary kernel -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

theorem oddHeatImageTerm_split_bound (n : ℕ) {T t : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    oddHeatImageTerm n t ≤ Real.exp (-1/(4*t)) * oddHeatImageTerm n (2*T) := by
  have hT : 0 < T := ht.trans_le htT
  rw [oddHeatImageTerm_of_pos n ht, oddHeatImageTerm_of_pos n (by positivity), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hc : (1/2 : ℝ) ≤ oddHeatImageRate n := by
    have hh := (oddHeatImageRate_bounds n).1
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have h₁ := div_le_div_of_nonneg_right hc (show 0 ≤ 2*t by positivity)
  have h₂ : oddHeatImageRate n/(2*T) ≤ oddHeatImageRate n/(2*t) :=
    div_le_div_of_nonneg_left (oddHeatImageRate_pos n).le (by positivity) (by linarith)
  have he : (1/2 : ℝ)/(2*t) = 1/(4*t) := by ring
  rw [he] at h₁
  have hd : oddHeatImageRate n/t = 2*(oddHeatImageRate n/(2*t)) := by ring
  rw [neg_div, neg_div, neg_div, hd]
  linarith

theorem tsum_oddHeatImageRateTerm_bound {T t : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    (∑' n, oddHeatImageRate n*oddHeatImageTerm n t) ≤
      Real.exp (-1/(4*t)) * ∑' n, oddHeatImageRate n*oddHeatImageTerm n (2*T) := by
  have hT : 0 < T := ht.trans_le htT
  rw [← tsum_mul_left]
  apply (summable_oddHeatImageRateTerm ht).tsum_le_tsum _
    ((summable_oddHeatImageRateTerm (by positivity : 0 < 2*T)).mul_left _)
  intro n
  have hh := mul_le_mul_of_nonneg_left (oddHeatImageTerm_split_bound n ht htT)
    (oddHeatImageRate_pos n).le
  convert! hh using 1
  ring

def heatCrossImageBound (T : ℝ) : ℝ :=
  4*heatImageNormalization*((∑' n, oddHeatImageRate n*oddHeatImageTerm n (2*T))+1)

theorem heatCrossImageBound_pos (T : ℝ) : 0 < heatCrossImageBound T := by
  have hs : 0 ≤ ∑' n, oddHeatImageRate n*oddHeatImageTerm n (2*T) :=
    tsum_nonneg (fun n => mul_nonneg (oddHeatImageRate_pos n).le (expNegInvGlue.nonneg _))
  unfold heatCrossImageBound
  exact mul_pos (mul_pos (by norm_num) heatImageNormalization_pos) (by linarith)

/-- The cross-boundary factor has the Gaussian decay required for dominated
convergence on every bounded positive time interval. -/
theorem heatCrossBoundary_small_time_bound {T t : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    ‖heatCrossBoundary 1 t‖ ≤ heatCrossImageBound T * t^(-5/2 : ℝ) * Real.exp (-1/(4*t)) := by
  have hc := heatImageNormalization_pos
  have hS : 0 ≤ ∑' n, oddHeatImageTerm n t := tsum_nonneg (fun n => expNegInvGlue.nonneg _)
  have hD := tsum_oddHeatImageRateTerm_bound ht htT
  rw [Real.norm_eq_abs, abs_of_pos (heatCrossBoundary_strictlyPositive (by norm_num) ht),
    heatCrossBoundary_eq_image_derivative ht, tsum_oddHeatImageDerivative ht]
  have hr : t^(-1/2 : ℝ)*(1/t^2) = t^(-5/2 : ℝ) := by
    rw [one_div, ← Real.rpow_two, ← Real.rpow_neg ht.le, ← Real.rpow_add ht]
    norm_num
  have hp : 0 ≤ 4*heatImageNormalization*t^(-5/2 : ℝ) := by positivity
  calc
    _ ≤ 4*heatImageNormalization*t^(-1/2 : ℝ)*
        ((1/t^2)*(∑' n, oddHeatImageRate n*oddHeatImageTerm n t)) := by
      have hn : 0 ≤ 2*heatImageNormalization*t^(-3/2 : ℝ)*(∑' n, oddHeatImageTerm n t) := by positivity
      linarith
    _ = 4*heatImageNormalization*t^(-5/2 : ℝ)*
        (∑' n, oddHeatImageRate n*oddHeatImageTerm n t) := by
      calc
        _ = 4*heatImageNormalization*(t^(-1/2 : ℝ)*(1/t^2))*(∑' n, oddHeatImageRate n*oddHeatImageTerm n t) := by ring
        _ = _ := by rw [hr]
    _ ≤ 4*heatImageNormalization*t^(-5/2 : ℝ)*
        (Real.exp (-1/(4*t))*(∑' n, oddHeatImageRate n*oddHeatImageTerm n (2*T))) :=
      mul_le_mul_of_nonneg_left hD hp
    _ ≤ heatCrossImageBound T*t^(-5/2 : ℝ)*Real.exp (-1/(4*t)) := by
      unfold heatCrossImageBound
      have hh : 0 ≤ 4*heatImageNormalization*t^(-5/2 : ℝ)*Real.exp (-1/(4*t)) := by positivity
      nlinarith

theorem tendsto_rpow_inverse_gaussian_zero (p : ℝ) :
    Tendsto (fun t : ℝ => t^(-p)*Real.exp (-1/(4*t))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p (1/4) (by norm_num)).comp
    tendsto_inv_nhdsGT_zero
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  dsimp only [Function.comp_apply]
  rw [Real.inv_rpow ht.le, ← Real.rpow_neg ht.le]
  congr 1
  congr 1
  ring

theorem tendsto_heatCrossBoundary_zero :
    Tendsto (heatCrossBoundary 1) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply squeeze_zero_norm'
    (a := fun t : ℝ => heatCrossImageBound 1*t^(-5/2 : ℝ)*Real.exp (-1/(4*t)))
  · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ)<1 by norm_num))] with t ht ht1
    exact heatCrossBoundary_small_time_bound ht ht1.le
  · have hh := (tendsto_rpow_inverse_gaussian_zero (5/2)).const_mul (heatCrossImageBound 1)
    simpa only [mul_zero, mul_assoc, show -(5/2 : ℝ) = -5/2 by ring] using hh

end BrownianAffine
