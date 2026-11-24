import PLAStochastic.Affine.Moments.Optimal.Survival.QImage.Laplace
import PLAStochastic.Affine.Moments.Optimal.Survival.Image.Convergence

noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

def optimalQImageGaussianBound (δ U : ℝ) (n : ℕ) : ℝ :=
  (64*(5/δ+1)/Real.sqrt (2*Real.pi*δ))*((n : ℝ)+1)^4*
    Real.exp (-((n : ℝ)+1)^2/(2*U))

theorem optimalQImageCoefficientB_le (n : ℕ) :
    optimalQImageCoefficientB n ≤ ((n : ℝ)+1)^2 := by
  unfold optimalQImageCoefficientB
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem optimalQImageCoefficientC_le (n : ℕ) :
    optimalQImageCoefficientC n ≤ ((n : ℝ)+1)^3 := by
  unfold optimalQImageCoefficientC
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith [sq_nonneg (n : ℝ),mul_nonneg hn (sq_nonneg (n : ℝ))]

theorem optimalQImageLength_bounds (n : ℕ) {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    (n : ℝ)+1 ≤ optimalQImageLength n x y ∧ optimalQImageLength n x y ≤ 5*((n : ℝ)+1) := by
  unfold optimalQImageLength
  constructor <;> linarith [(abs_le.mp hx).1,(abs_le.mp hx).2,
    (abs_le.mp hy).1,(abs_le.mp hy).2,Nat.cast_nonneg (α := ℝ) n]

theorem norm_optimalQImageBase_bound (n : ℕ) {δ U x y T : ℝ}
    (hδ : 0 < δ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hT : T ∈ Icc δ U) :
    ‖optimalQImageBase n x y T‖ ≤
      ((5/δ+1)/Real.sqrt (2*Real.pi*δ))*((n : ℝ)+1)^4*
        Real.exp (-((n : ℝ)+1)^2/(2*U)) := by
  have ht : 0 < T := hδ.trans_le hT.1
  have hU : 0 < U := ht.trans_le hT.2
  have hm : 1 ≤ (n : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hL := optimalQImageLength_bounds n hx hy
  have hL0 : 0 ≤ optimalQImageLength n x y := by linarith [hL.1]
  have hB := optimalQImageCoefficientB_nonneg n
  have hC := optimalQImageCoefficientC_nonneg n
  have hp : ‖optimalQImageCoefficientC n*optimalQImageLength n x y/T-optimalQImageCoefficientB n‖ ≤
      (5/δ+1)*((n : ℝ)+1)^4 := by
    have hh := norm_sub_le (optimalQImageCoefficientC n*optimalQImageLength n x y/T)
      (optimalQImageCoefficientB n)
    rw [Real.norm_of_nonneg (div_nonneg (mul_nonneg hC hL0) ht.le),Real.norm_of_nonneg hB] at hh
    have hc := mul_le_mul (optimalQImageCoefficientC_le n) hL.2 hL0 (by positivity : 0 ≤ ((n : ℝ)+1)^3)
    have hd := div_le_div₀ (by positivity : 0 ≤ ((n : ℝ)+1)^3*(5*((n : ℝ)+1))) hc hδ hT.1
    have hs : ((n : ℝ)+1)^2 ≤ ((n : ℝ)+1)^4 := by nlinarith [sq_nonneg (((n : ℝ)+1)^2-1)]
    have he : ((n : ℝ)+1)^3*(5*((n : ℝ)+1))/δ + ((n : ℝ)+1)^4 =
        (5/δ+1)*((n : ℝ)+1)^4 := by ring
    exact hh.trans ((add_le_add hd ((optimalQImageCoefficientB_le n).trans hs)).trans_eq he)
  have hexp : Real.exp (-optimalQImageLength n x y^2/(2*T)) ≤
      Real.exp (-((n : ℝ)+1)^2/(2*U)) := by
    apply Real.exp_le_exp.mpr
    have hs := sq_le_sq₀ (by positivity : 0 ≤ (n : ℝ)+1) hL0 |>.mpr hL.1
    have hd := div_le_div₀ (sq_nonneg (optimalQImageLength n x y)) hs (by positivity : 0 < 2*T)
      (show 2*T ≤ 2*U by linarith [hT.2])
    simpa only [neg_div] using neg_le_neg hd
  have hsqrt : Real.sqrt (2*Real.pi*δ) ≤ Real.sqrt (2*Real.pi*T) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hT.1 (by positivity))
  have hg : ‖optimalQImageGaussian (optimalQImageLength n x y) T‖ ≤
      Real.exp (-((n : ℝ)+1)^2/(2*U))/Real.sqrt (2*Real.pi*δ) := by
    unfold optimalQImageGaussian
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact div_le_div₀ (Real.exp_nonneg _) hexp (by positivity) hsqrt
  unfold optimalQImageBase
  rw [norm_mul]
  calc
    _ ≤ ((5/δ+1)*((n : ℝ)+1)^4)*
      (Real.exp (-((n : ℝ)+1)^2/(2*U))/Real.sqrt (2*Real.pi*δ)) :=
        mul_le_mul hp hg (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem norm_optimalQImageMode_bound (n : ℕ) {δ U x y T : ℝ}
    (hδ : 0 < δ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hT : T ∈ Icc δ U) :
    ‖optimalQImageMode n x y T‖ ≤ optimalQImageGaussianBound δ U n := by
  have hnx : |-x| ≤ 1 := by simpa using hx
  have hny : |-y| ≤ 1 := by simpa using hy
  have hpp := norm_optimalQImageBase_bound n hδ hx hy hT
  have hmm := norm_optimalQImageBase_bound n hδ hnx hny hT
  have hpm := norm_optimalQImageBase_bound n hδ hx hny hT
  have hmp := norm_optimalQImageBase_bound n hδ hnx hy hT
  have h₁ := norm_add_le (optimalQImageBase n x y T) (optimalQImageBase n (-x) (-y) T)
  have h₂ := norm_sub_le (optimalQImageBase n x y T+optimalQImageBase n (-x) (-y) T)
    (optimalQImageBase n x (-y) T)
  have h₃ := norm_sub_le (optimalQImageBase n x y T+optimalQImageBase n (-x) (-y) T-
    optimalQImageBase n x (-y) T) (optimalQImageBase n (-x) y T)
  unfold optimalQImageMode optimalQImageGaussianBound
  rw [norm_mul,Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 16)]
  have he : 64*(5/δ+1)/Real.sqrt (2*Real.pi*δ)*((n : ℝ)+1)^4*
      Real.exp (-((n : ℝ)+1)^2/(2*U)) =
      16*(4*(((5/δ+1)/Real.sqrt (2*Real.pi*δ))*((n : ℝ)+1)^4*
        Real.exp (-((n : ℝ)+1)^2/(2*U)))) := by ring
  rw [he]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 16)
  linarith

theorem summable_optimalQImageGaussianBound {δ U : ℝ} (hδ : 0 < δ) (hU : 0 < U) :
    Summable (optimalQImageGaussianBound δ U) := by
  have hr : 0 < 1/(2*U) := by positivity
  have hh := Real.summable_pow_mul_exp_neg_nat_mul 4 hr
  have hs : Summable (fun n : ℕ => ((n : ℝ)+1)^4*Real.exp (-(1/(2*U))*((n : ℝ)+1))) := by
    simpa only [Nat.cast_add,Nat.cast_one] using (summable_nat_add_iff 1).mpr hh
  apply (hs.mul_left (64*(5/δ+1)/Real.sqrt (2*Real.pi*δ))).of_nonneg_of_le
  · intro n
    unfold optimalQImageGaussianBound
    positivity
  · intro n
    unfold optimalQImageGaussianBound
    rw [←mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have hn : ((n : ℝ)+1) ≤ ((n : ℝ)+1)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have he := mul_le_mul_of_nonneg_left hn hr.le
    calc
      -((n : ℝ)+1)^2/(2*U) = -(1/(2*U)*((n : ℝ)+1)^2) := by ring
      _ ≤ -(1/(2*U)*((n : ℝ)+1)) := neg_le_neg he
      _ = -(1/(2*U))*((n : ℝ)+1) := by ring

theorem summable_norm_optimalQImageMode {x y T : ℝ}
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hT : 0 < T) :
    Summable (fun n => ‖optimalQImageMode n x y T‖) :=
  (summable_optimalQImageGaussianBound hT hT).of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => norm_optimalQImageMode_bound n hT hx hy ⟨le_rfl,le_rfl⟩)

theorem summable_optimalQImageMode {x y T : ℝ}
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hT : 0 < T) :
    Summable (fun n => optimalQImageMode n x y T) :=
  (summable_norm_optimalQImageMode hx hy hT).of_norm

theorem measurable_optimalQImageSeries :
    Measurable (fun p : ℝ × ℝ × ℝ => optimalQImageSeries p.1 p.2.1 p.2.2) :=
  Measurable.tsum measurable_optimalQImageMode

theorem continuousAt_optimalQImageMode_time (n : ℕ) (x y : ℝ) {T : ℝ} (hT : 0 < T) :
    ContinuousAt (optimalQImageMode n x y) T := by
  have htne : T ≠ 0 := hT.ne'
  have h2tne : 2*T ≠ 0 := by positivity
  have hsne : Real.sqrt (2*Real.pi*T) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  unfold optimalQImageMode optimalQImageBase optimalQImageGaussian
  fun_prop

theorem continuousAt_optimalQImageSeries_time {x y T : ℝ}
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hT : 0 < T) :
    ContinuousAt (optimalQImageSeries x y) T := by
  have hc : ContinuousOn (optimalQImageSeries x y) (Icc (T/2) (T+1)) :=
    continuousOn_tsum (fun n t ht => (continuousAt_optimalQImageMode_time n x y
      (lt_of_lt_of_le (half_pos hT) ht.1)).continuousWithinAt)
      (summable_optimalQImageGaussianBound (half_pos hT) (by linarith))
        (fun n _ ht => norm_optimalQImageMode_bound n (half_pos hT) hx hy ht)
  exact hc.continuousAt (Icc_mem_nhds (by linarith) (by linarith))

/-- One summable bound controls all spatial points and every time in a compact positive interval. -/
theorem tendstoUniformlyOn_optimalQImageMode {δ U : ℝ} (hδ : 0 < δ) (hU : 0 < U) :
    TendstoUniformlyOn (fun N (p : ℝ × ℝ × ℝ) =>
      ∑ n ∈ Finset.range N,optimalQImageMode n p.1 p.2.1 p.2.2)
      (fun p => optimalQImageSeries p.1 p.2.1 p.2.2) atTop
      {p | |p.1| ≤ 1 ∧ |p.2.1| ≤ 1 ∧ p.2.2 ∈ Icc δ U} :=
  tendstoUniformlyOn_tsum_nat (summable_optimalQImageGaussianBound hδ hU)
    (fun n _ hp => norm_optimalQImageMode_bound n hδ hp.1 hp.2.1 hp.2.2)

end BrownianAffine
