import PLAStochastic.Affine.Moments.Optimal.Survival.Image.OddGaussian

/-! # The genuine cross-boundary kernel in Gaussian image form -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

def heatImageNormalization : ℝ := (Real.pi/2)^(-1/2 : ℝ)

theorem heatImageNormalization_pos : 0 < heatImageNormalization := by
  unfold heatImageNormalization
  positivity

theorem alternatingHeatTheta_image_rpow {t : ℝ} (ht : 0 < t) :
    alternatingHeatTheta t = 2 * heatImageNormalization * t^(-1/2 : ℝ) *
      ∑' n, oddHeatImageTerm n t := by
  rw [alternatingHeatTheta_image_nat ht]
  unfold heatImageNormalization
  have he : Real.pi*t/2 = (Real.pi/2)*t := by ring
  rw [he, Real.mul_rpow (by positivity : 0 ≤ Real.pi/2) ht.le,
    show (-1/2 : ℝ) = -(1/2) by ring, Real.rpow_neg (by positivity : 0 ≤ Real.pi/2), Real.rpow_neg ht.le]
  ring

/-- Differentiation of Poisson summation identifies the actual cross-boundary
kernel, with absolute convergence justified before differentiating. -/
theorem heatCrossBoundary_eq_image_derivative {t : ℝ} (ht : 0 < t) :
    heatCrossBoundary 1 t =
      -2 * heatImageNormalization * t^(-3/2 : ℝ) * (∑' n, oddHeatImageTerm n t) +
      4 * heatImageNormalization * t^(-1/2 : ℝ) *
        (∑' n, oddHeatImageRate n/t^2 * Real.exp (-oddHeatImageRate n/t)) := by
  have hp := (Real.hasDerivAt_rpow_const (x := t) (p := (-1/2 : ℝ)) (Or.inl ht.ne')).const_mul
    (2 * heatImageNormalization)
  have hd := hp.mul (hasDerivAt_tsum_oddHeatImageTerm ht)
  have he : alternatingHeatTheta =ᶠ[𝓝 t] (fun s => 2*heatImageNormalization*s^(-1/2 : ℝ)*
      ∑' n, oddHeatImageTerm n s) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact alternatingHeatTheta_image_rpow hs
  have heq := (hasDerivAt_alternatingHeatTheta ht).unique (hd.congr_of_eventuallyEq he)
  norm_num at heq
  linarith

theorem summable_oddHeatImageRateTerm {t : ℝ} (ht : 0 < t) :
    Summable (fun n => oddHeatImageRate n * oddHeatImageTerm n t) := by
  have hh := (summable_oddHeatImageBound ht 2).mul_left 2
  apply hh.of_norm_bounded
  intro n
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (oddHeatImageRate_pos n)]
  have h := mul_le_mul (oddHeatImageRate_bounds n).2 (oddHeatImageTerm_bound n ht le_rfl)
    (norm_nonneg _) (by positivity)
  convert! h using 1
  ring

theorem tsum_oddHeatImageDerivative {t : ℝ} (ht : 0 < t) :
    (∑' n, oddHeatImageRate n/t^2 * Real.exp (-oddHeatImageRate n/t)) =
      (1/t^2) * ∑' n, oddHeatImageRate n * oddHeatImageTerm n t := by
  simp_rw [← oddHeatImageTerm_of_pos _ ht]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  ring

/-- A real image series for the already identified heat cross derivative. -/
theorem heatCrossBoundary_image_series {t : ℝ} (ht : 0 < t) :
    heatCrossBoundary 1 t = 2 * heatImageNormalization * t^(-5/2 : ℝ) *
      ∑' n : ℕ, ((2*(n : ℝ)+1)^2-t) * Real.exp (-oddHeatImageRate n/t) := by
  have hs := summable_oddHeatImageTerm t
  have hc := summable_oddHeatImageRateTerm ht
  have he : (∑' n : ℕ, ((2*(n : ℝ)+1)^2-t) * Real.exp (-oddHeatImageRate n/t)) =
      2*(∑' n, oddHeatImageRate n*oddHeatImageTerm n t) - t*(∑' n, oddHeatImageTerm n t) := by
    simp_rw [← oddHeatImageTerm_of_pos _ ht,
      show ∀ n : ℕ, ((2*(n : ℝ)+1)^2-t) * oddHeatImageTerm n t =
        2*(oddHeatImageRate n*oddHeatImageTerm n t)-t*oddHeatImageTerm n t by
        intro n; unfold oddHeatImageRate; ring]
    rw [(hc.mul_left 2).tsum_sub (hs.mul_left t), tsum_mul_left, tsum_mul_left]
  rw [heatCrossBoundary_eq_image_derivative ht, tsum_oddHeatImageDerivative ht, he]
  have h₁ : t^(-5/2 : ℝ)*t = t^(-3/2 : ℝ) := by
    calc
      _ = t^(-5/2 : ℝ)*t^(1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add ht]; norm_num
  have h₂ : t^(-1/2 : ℝ)*(1/t^2) = t^(-5/2 : ℝ) := by
    rw [one_div, ← Real.rpow_two, ← Real.rpow_neg ht.le, ← Real.rpow_add ht]
    norm_num
  calc
    _ = 2*heatImageNormalization *
      (2*(t^(-1/2 : ℝ)*(1/t^2))*(∑' n, oddHeatImageRate n*oddHeatImageTerm n t) -
        t^(-3/2 : ℝ)*(∑' n, oddHeatImageTerm n t)) := by ring
    _ = _ := by rw [h₂, ← h₁]; ring

end BrownianAffine
