import PLAStochastic.Affine.Moments.Optimal.Survival.Image.Bounds

/-! # Absolute and uniform convergence of the optimal image series

The analytic series is continuous through zero and converges absolutely and
uniformly on every bounded positive time interval. Its probabilistic
identification is kept separate.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

def optimalImageGaussianBound (T : ℝ) (n : ℕ) : ℝ :=
  (40 * ((n : ℝ) + 1) ^ 2 + 4 * T) * Real.exp (-8 * ((n : ℝ) + 1) ^ 2 / T)

theorem summable_optimalImageGaussianBound {T : ℝ} (hT : 0 < T) :
    Summable (optimalImageGaussianBound T) := by
  have hr : 0 < 8 / T := by positivity
  have h₂ := (Real.summable_pow_mul_exp_neg_nat_mul 2 hr).mul_left 40
  have h₁ := (Real.summable_pow_mul_exp_neg_nat_mul 1 hr).mul_left 80
  have h₀ := (Real.summable_pow_mul_exp_neg_nat_mul 0 hr).mul_left (40 + 4 * T)
  have hs : Summable (fun n : ℕ => (40 * ((n : ℝ) + 1) ^ 2 + 4 * T) *
      Real.exp (-(8 / T) * (n : ℝ))) := by
    convert! (h₂.add h₁).add h₀ using 1
    funext n
    simp only [pow_zero, pow_one, one_mul]
    ring
  apply hs.of_nonneg_of_le
  · intro n
    dsimp [optimalImageGaussianBound]
    positivity
  · intro n
    unfold optimalImageGaussianBound
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have hn : (n : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) n, sq_nonneg (n : ℝ)]
    have hh := mul_le_mul_of_nonneg_left hn hr.le
    convert! neg_le_neg hh using 1 <;> ring

theorem summable_norm_optimalImageMode (t : ℝ) :
    Summable (fun n => ‖optimalImageMode n t‖) := by
  let T := max t 1
  have hT : 0 < T := zero_lt_one.trans_le (le_max_right _ _)
  exact (summable_optimalImageGaussianBound hT).of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => optimalImageMode_gaussian_bound n hT (le_max_left _ _))

theorem summable_optimalImageMode (t : ℝ) : Summable (fun n => optimalImageMode n t) :=
  (summable_norm_optimalImageMode t).of_norm

/-- The interval contains zero and all positive times through `T`. -/
theorem tendstoUniformlyOn_optimalImageMode {T : ℝ} (hT : 0 < T) :
    TendstoUniformlyOn (fun N t => ∑ n ∈ Finset.range N, optimalImageMode n t)
      (fun t => ∑' n, optimalImageMode n t) atTop (Iic T) :=
  tendstoUniformlyOn_tsum_nat (summable_optimalImageGaussianBound hT)
    (fun n _ ht => optimalImageMode_gaussian_bound n hT ht)

theorem continuous_optimalImageSeries : Continuous optimalImageSeries := by
  apply continuous_iff_continuousAt.mpr
  intro t
  let T := max t 1 + 1
  have hT : 0 < T := by dsimp only [T]; linarith [le_max_right t 1]
  have htT : t < T := by dsimp only [T]; linarith [le_max_left t 1]
  have hc : ContinuousOn optimalImageSeries (Iic T) := by
    apply continuousOn_const.add
    exact continuousOn_tsum (fun n => (continuous_optimalImageMode n).continuousOn)
      (summable_optimalImageGaussianBound hT) (fun n _ hx => optimalImageMode_gaussian_bound n hT hx)
  exact hc.continuousAt (Iic_mem_nhds htT)

theorem optimalImageSeries_of_nonpos {t : ℝ} (ht : t ≤ 0) : optimalImageSeries t = 1 := by
  simp [optimalImageSeries, optimalImageMode_of_nonpos _ ht]

theorem tendsto_optimalImageSeries_zero : Tendsto optimalImageSeries (𝓝 (0 : ℝ)) (𝓝 1) := by
  simpa [optimalImageSeries_of_nonpos le_rfl] using
    (continuous_optimalImageSeries.continuousAt (x := (0 : ℝ))).tendsto

end BrownianAffine
