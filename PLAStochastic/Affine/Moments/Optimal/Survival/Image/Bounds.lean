import PLAStochastic.Affine.Moments.Optimal.Survival.Image.Modes

/-! # Gaussian bounds for the explicit optimal image terms -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

theorem expNegInvGlue_uniform_bound {c T t : ℝ} (hc : 0 < c)
    (hT : 0 < T) (ht : t ≤ T) :
    expNegInvGlue (t / c) ≤ Real.exp (-c / T) := by
  rw [← expNegInvGlue_div hc hT]
  exact expNegInvGlue.monotone (div_le_div_of_nonneg_right ht hc.le)

theorem inverseExponentialIntegral_uniform_bound {c T t : ℝ} (hc : 0 < c)
    (hT : 0 < T) (ht : t ≤ T) :
    inverseExponentialIntegral c t ≤ (T / c) * Real.exp (-c / T) := by
  by_cases ht0 : 0 < t
  · have he : Real.exp (-c / t) ≤ Real.exp (-c / T) := by
      rw [← expNegInvGlue_div hc ht0]
      exact expNegInvGlue_uniform_bound hc hT ht
    exact (inverseExponentialIntegral_le hc ht0).trans
      (mul_le_mul (div_le_div_of_nonneg_right ht hc.le) he
        (Real.exp_nonneg _) (by positivity))
  · rw [inverseExponentialIntegral_of_nonpos _ (le_of_not_gt ht0)]
    positivity

theorem optimalImageCoefficientA_bound (n : ℕ) {T t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ T) :
    |optimalImageCoefficientA n t| ≤ 8 * ((n : ℝ) + 1) ^ 2 + T := by
  let m := (n : ℝ) + 1
  have hm : 1 ≤ m := by dsimp [m]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  have hs : 1 ≤ m ^ 2 := by nlinarith
  have hi : 0 ≤ 1 / m ^ 2 := by positivity
  have hi1 : 1 / m ^ 2 ≤ 1 := (div_le_one (by positivity)).mpr hs
  have hu : 0 ≤ 1 - 1 / m ^ 2 := by linarith
  change |(-8 * (2 * m ^ 2 + 1) / 3) + t / 6 * (1 - 1 / m ^ 2)| ≤ _
  calc
    _ ≤ |(-8 * (2 * m ^ 2 + 1) / 3)| + |t / 6 * (1 - 1 / m ^ 2)| := abs_add_le _ _
    _ = 8 * (2 * m ^ 2 + 1) / 3 + t / 6 * (1 - 1 / m ^ 2) := by
      rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg m]) (by norm_num)),
        abs_of_nonneg (by positivity)]
      ring
    _ ≤ 8 * m ^ 2 + T := by
      have hh := mul_le_mul_of_nonneg_left (show 1 - 1 / m ^ 2 ≤ 1 by linarith)
        (show 0 ≤ t / 6 by positivity)
      nlinarith

theorem optimalImageCoefficientB_bound (n : ℕ) {T t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ T) :
    |optimalImageCoefficientB n t| ≤ 27 * ((n : ℝ) + 1) ^ 2 + T := by
  let m := (n : ℝ) + 1
  have hm : 1 ≤ m := by dsimp [m]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  have hm1 : 0 < m + 1 := by positivity
  have hs : 1 ≤ m ^ 2 := by nlinarith
  have hs1 : 1 ≤ (m + 1) ^ 2 := by nlinarith
  have hi : 0 ≤ 1 / m ^ 2 := by positivity
  have hi1 : 1 / m ^ 2 ≤ 1 := (div_le_one (by positivity)).mpr hs
  have hj : 0 ≤ 1 / (m + 1) ^ 2 := by positivity
  have hj1 : 1 / (m + 1) ^ 2 ≤ 1 := (div_le_one (by positivity)).mpr hs1
  have hb : (2 * m + 1) ^ 4 / (3 * m * (m + 1)) ≤ 27 * m ^ 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hpow : (2 * m + 1) ^ 4 ≤ (3 * m) ^ 4 := by gcongr; linarith
    have hc : 0 ≤ m ^ 3 := by positivity
    nlinarith
  change |(2 * m + 1) ^ 4 / (3 * m * (m + 1)) +
    t / 12 * (-2 + 1 / m ^ 2 + 1 / (m + 1) ^ 2)| ≤ _
  calc
    _ ≤ |(2 * m + 1) ^ 4 / (3 * m * (m + 1))| +
      |t / 12 * (-2 + 1 / m ^ 2 + 1 / (m + 1) ^ 2)| := abs_add_le _ _
    _ = (2 * m + 1) ^ 4 / (3 * m * (m + 1)) -
      t / 12 * (-2 + 1 / m ^ 2 + 1 / (m + 1) ^ 2) := by
      rw [abs_of_nonneg (by positivity), abs_of_nonpos
        (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith))]
      ring
    _ ≤ 27 * m ^ 2 + T := by
      have hh := mul_le_mul_of_nonneg_left
        (show -2 ≤ -2 + 1 / m ^ 2 + 1 / (m + 1) ^ 2 by linarith)
        (show 0 ≤ t / 12 by positivity)
      nlinarith

/-- A Gaussian bound retains the manuscript's quadratic growth in the image index. -/
theorem optimalImageMode_gaussian_bound (n : ℕ) {T t : ℝ} (hT : 0 < T) (ht : t ≤ T) :
    ‖optimalImageMode n t‖ ≤
      (40 * ((n : ℝ) + 1) ^ 2 + 4 * T) * Real.exp (-8 * ((n : ℝ) + 1) ^ 2 / T) := by
  by_cases ht0 : 0 < t
  swap
  · rw [optimalImageMode_of_nonpos n (le_of_not_gt ht0), norm_zero]
    positivity
  let m := (n : ℝ) + 1
  have hm : 1 ≤ m := by dsimp [m]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  have hc : 0 < 8 * m ^ 2 := by positivity
  have hd : 0 < 8 * m * (m + 1) := by positivity
  let e := Real.exp (-8 * m ^ 2 / T)
  have he0 : 0 ≤ e := Real.exp_nonneg _
  have he : Real.exp (-(8 * m * (m + 1)) / T) ≤ e := by
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ hT.le
    nlinarith
  have hg₁ : expNegInvGlue (t / (8 * m ^ 2)) ≤ e := by
    convert! expNegInvGlue_uniform_bound hc hT ht using 1
    dsimp only [e]
    congr 1
    ring
  have hg₂ : expNegInvGlue (t / (8 * m * (m + 1))) ≤ e :=
    (expNegInvGlue_uniform_bound hd hT ht).trans he
  have hE₁ : 4 * m ^ 2 * inverseExponentialIntegral (8 * m ^ 2) t ≤ T / 2 * e := by
    have hh := mul_le_mul_of_nonneg_left (inverseExponentialIntegral_uniform_bound hc hT ht)
      (show 0 ≤ 4 * m ^ 2 by positivity)
    convert! hh using 1
    dsimp only [e]
    rw [show -(8 * m ^ 2) = -8 * m ^ 2 by ring]
    field_simp
    ring
  have hE₂ : 4 * m * (m + 1) * inverseExponentialIntegral (8 * m * (m + 1)) t ≤ T / 2 * e := by
    have hh := mul_le_mul_of_nonneg_left (inverseExponentialIntegral_uniform_bound hd hT ht)
      (show 0 ≤ 4 * m * (m + 1) by positivity)
    have hh' : 4 * m * (m + 1) * inverseExponentialIntegral (8 * m * (m + 1)) t ≤
        T / 2 * Real.exp (-(8 * m * (m + 1)) / T) := by
      convert! hh using 1
      field_simp
      ring
    exact hh'.trans (mul_le_mul_of_nonneg_left he (by positivity))
  have hA := mul_le_mul (optimalImageCoefficientA_bound n ht0.le ht) hg₁
    (expNegInvGlue.nonneg _) (show 0 ≤ 8 * m ^ 2 + T by positivity)
  have hB := mul_le_mul (optimalImageCoefficientB_bound n ht0.le ht) hg₂
    (expNegInvGlue.nonneg _) (show 0 ≤ 27 * m ^ 2 + T by positivity)
  change |optimalImageCoefficientA n t * expNegInvGlue (t / (8 * m ^ 2)) +
    optimalImageCoefficientB n t * expNegInvGlue (t / (8 * m * (m + 1))) +
    4 * m ^ 2 * inverseExponentialIntegral (8 * m ^ 2) t -
    4 * m * (m + 1) * inverseExponentialIntegral (8 * m * (m + 1)) t| ≤ _
  calc
    _ ≤ |optimalImageCoefficientA n t * expNegInvGlue (t / (8 * m ^ 2))| +
        |optimalImageCoefficientB n t * expNegInvGlue (t / (8 * m * (m + 1)))| +
        |4 * m ^ 2 * inverseExponentialIntegral (8 * m ^ 2) t| +
        |4 * m * (m + 1) * inverseExponentialIntegral (8 * m * (m + 1)) t| := by
      exact (abs_sub _ _).trans (add_le_add
        ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    _ ≤ (8 * m ^ 2 + T) * e + (27 * m ^ 2 + T) * e + T / 2 * e + T / 2 * e := by
      have h₁ : 0 ≤ 4 * m ^ 2 * inverseExponentialIntegral (8 * m ^ 2) t :=
        mul_nonneg (by positivity) (inverseExponentialIntegral_nonneg _ _)
      have h₂ : 0 ≤ 4 * m * (m + 1) * inverseExponentialIntegral (8 * m * (m + 1)) t :=
        mul_nonneg (by positivity) (inverseExponentialIntegral_nonneg _ _)
      rw [abs_of_nonneg h₁, abs_of_nonneg h₂]
      simp only [abs_mul, abs_of_nonneg (expNegInvGlue.nonneg _)]
      exact add_le_add (add_le_add (add_le_add hA hB) hE₁) hE₂
    _ ≤ (40 * m ^ 2 + 4 * T) * e := by nlinarith [sq_nonneg m]

end BrownianAffine
