import PLAStochastic.Affine.Moments.Optimal.Survival.Image.SmoothMode
import PLAStochastic.Affine.Moments.Optimal.Survival.Image.Bounds
import PLAStochastic.ForMathlib.Analysis.SpecialFunctions.FlatGlueJets
import PLAStochastic.ForMathlib.Analysis.Calculus.LocalSmoothSeries

/-! # Summable local envelopes for every derivative of the optimal image modes -/

noncomputable section
open MeasureTheory Filter Set Finset
open scoped Topology ContDiff Polynomial

namespace BrownianAffine

set_option backward.isDefEq.respectTransparency false

theorem iteratedDeriv_inverseExponentialIntegral_succ {c : ℝ} (hc : 0 < c) (r : ℕ) :
    iteratedDeriv (r + 1) (inverseExponentialIntegral c) = fun t =>
      c⁻¹ * iteratedDeriv r
        (fun x : ℝ => (Polynomial.X : ℝ[X]).eval (x / c)⁻¹ * expNegInvGlue (x / c)) t := by
  rw [iteratedDeriv_succ']
  have he : deriv (inverseExponentialIntegral c) = fun x : ℝ =>
      c⁻¹ * ((Polynomial.X : ℝ[X]).eval (x / c)⁻¹ * expNegInvGlue (x / c)) := by
    funext x
    rw [(hasDerivAt_inverseExponentialIntegral hc x).deriv, Polynomial.eval_X]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, ← mul_assoc,
      inv_mul_cancel₀ hc.ne', one_mul]
  rw [he]
  funext t
  exact iteratedDeriv_const_mul_field c⁻¹ _

theorem iteratedDeriv_inverseExponentialIntegral_uniform_bound (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c T t : ℝ, 1 ≤ c → 0 < T → t ≤ T →
      ‖iteratedDeriv r (inverseExponentialIntegral c) t‖ ≤
        C * (T + 1) * Real.exp (-c / (2 * T)) := by
  cases r with
  | zero =>
    refine ⟨1, zero_le_one, fun c T t hc hT ht => ?_⟩
    have hc0 := zero_lt_one.trans_le hc
    rw [iteratedDeriv_zero, Real.norm_eq_abs, abs_of_nonneg (inverseExponentialIntegral_nonneg c t)]
    have hb := inverseExponentialIntegral_uniform_bound hc0 hT ht
    have hq : T / c ≤ T + 1 := by
      have h := (div_le_iff₀ hc0).mpr (show T ≤ T * c by nlinarith)
      linarith
    have he : Real.exp (-c / T) ≤ Real.exp (-c / (2 * T)) := by
      apply Real.exp_le_exp.mpr
      rw [show -c / (2 * T) = (-c / T) / 2 by ring]
      have : -c / T ≤ 0 := by exact div_nonpos_of_nonpos_of_nonneg (by linarith) hT.le
      linarith
    exact hb.trans (by simpa only [one_mul] using mul_le_mul hq he (Real.exp_nonneg _) (by linarith : 0 ≤ T + 1))
  | succ r =>
    obtain ⟨C, hC, hp⟩ := expNegInvGlue.iteratedDeriv_scaled_uniform_bound (Polynomial.X : ℝ[X]) r
    refine ⟨C, hC, fun c T t hc hT ht => ?_⟩
    rw [iteratedDeriv_inverseExponentialIntegral_succ (zero_lt_one.trans_le hc), norm_mul,
      Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by linarith : 0 ≤ c))]
    have hb := mul_le_mul (inv_le_one_of_one_le₀ hc) (hp c T t hc hT ht) (norm_nonneg _) zero_le_one
    calc
      _ ≤ C * Real.exp (-c / (2 * T)) := by simpa only [one_mul] using hb
      _ ≤ C * (T + 1) * Real.exp (-c / (2 * T)) := by
        have : C ≤ C * (T + 1) := by nlinarith
        exact mul_le_mul_of_nonneg_right this (Real.exp_nonneg _)

private theorem iteratedDeriv_affine_bound (u v : ℝ) (r : ℕ) {T t : ℝ}
    (ht0 : 0 ≤ t) (ht : t ≤ T) :
    |iteratedDeriv r (fun x : ℝ => u + v * x) t| ≤ |u| + |v| * (T + 1) := by
  cases r with
  | zero =>
    simp only [iteratedDeriv_zero]
    calc
      _ ≤ |u| + |v * t| := abs_add_le _ _
      _ = |u| + |v| * t := by rw [abs_mul, abs_of_nonneg ht0]
      _ ≤ _ := by gcongr; linarith
  | succ r =>
    rw [iteratedDeriv_const_add (Nat.succ_pos r), iteratedDeriv_const_mul_field,
      iteratedDeriv_fun_id]
    have hT : 0 ≤ T + 1 := by linarith
    cases r with
    | zero =>
      simp only [Nat.one_ne_zero, if_false, if_true, mul_one]
      nlinarith [abs_nonneg u, abs_nonneg v]
    | succ r =>
      simp only [Nat.succ_ne_zero, if_false, show (r + 1).succ ≠ 1 by omega, mul_zero, abs_zero]
      exact add_nonneg (abs_nonneg u) (mul_nonneg (abs_nonneg v) hT)

theorem iteratedDeriv_optimalImageCoefficientA_bound (n r : ℕ) {T t : ℝ}
    (ht0 : 0 ≤ t) (ht : t ≤ T) :
    |iteratedDeriv r (optimalImageCoefficientA n) t| ≤ 28 * ((n : ℝ) + 1) ^ 2 + T + 1 := by
  let m := (n : ℝ) + 1
  let u : ℝ := -8 * (2 * m ^ 2 + 1) / 3
  let v : ℝ := (1 - 1 / m ^ 2) / 6
  have hm : 1 ≤ m := by dsimp [m]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hm2 : 1 ≤ m ^ 2 := by nlinarith
  have hi : 0 ≤ 1 / m ^ 2 := by positivity
  have hi1 : 1 / m ^ 2 ≤ 1 := (div_le_one (by positivity)).mpr hm2
  have hv : |v| ≤ 1 := by dsimp [v]; rw [abs_le]; constructor <;> linarith
  have hu : |u| ≤ 8 * m ^ 2 := by
    simpa [optimalImageCoefficientA, u, m] using
      optimalImageCoefficientA_bound n (T := 0) (t := 0) le_rfl le_rfl
  have he : optimalImageCoefficientA n = fun x => u + v * x := by
    funext x
    dsimp [optimalImageCoefficientA, u, v, m]
    ring
  rw [he]
  have hb := iteratedDeriv_affine_bound u v r ht0 ht
  have hvT := mul_le_mul_of_nonneg_right hv (show 0 ≤ T + 1 by linarith)
  change _ ≤ 28 * m ^ 2 + T + 1
  nlinarith

theorem iteratedDeriv_optimalImageCoefficientB_bound (n r : ℕ) {T t : ℝ}
    (ht0 : 0 ≤ t) (ht : t ≤ T) :
    |iteratedDeriv r (optimalImageCoefficientB n) t| ≤ 28 * ((n : ℝ) + 1) ^ 2 + T + 1 := by
  let m := (n : ℝ) + 1
  let u : ℝ := (2 * m + 1) ^ 4 / (3 * m * (m + 1))
  let v : ℝ := (-2 + 1 / m ^ 2 + 1 / (m + 1) ^ 2) / 12
  have hm : 1 ≤ m := by dsimp [m]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hm2 : 1 ≤ m ^ 2 := by nlinarith
  have hm12 : 1 ≤ (m + 1) ^ 2 := by nlinarith
  have hi : 0 ≤ 1 / m ^ 2 := by positivity
  have hj : 0 ≤ 1 / (m + 1) ^ 2 := by positivity
  have hi1 : 1 / m ^ 2 ≤ 1 := (div_le_one (by positivity)).mpr hm2
  have hj1 : 1 / (m + 1) ^ 2 ≤ 1 := (div_le_one (by positivity)).mpr hm12
  have hv : |v| ≤ 1 := by dsimp [v]; rw [abs_le]; constructor <;> linarith
  have hu : |u| ≤ 27 * m ^ 2 := by
    simpa [optimalImageCoefficientB, u, m] using
      optimalImageCoefficientB_bound n (T := 0) (t := 0) le_rfl le_rfl
  have he : optimalImageCoefficientB n = fun x => u + v * x := by
    funext x
    dsimp [optimalImageCoefficientB, u, v, m]
    ring
  rw [he]
  have hb := iteratedDeriv_affine_bound u v r ht0 ht
  have hvT := mul_le_mul_of_nonneg_right hv (show 0 ≤ T + 1 by linarith)
  change _ ≤ 28 * m ^ 2 + T + 1
  nlinarith

/-- A product estimate that uses only finitely many fixed derivative orders. -/
theorem iteratedDeriv_mul_scaled_glue_uniform_bound (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℝ → ℝ) (B c T t : ℝ), ContDiff ℝ ∞ f →
      0 ≤ B → 1 ≤ c → 0 < T → t ≤ T →
      (∀ i ≤ r, |iteratedDeriv i f t| ≤ B) →
      ‖iteratedDeriv r (fun x => f x * expNegInvGlue (x / c)) t‖ ≤
        B * C * Real.exp (-c / (2 * T)) := by
  choose C hC hb using fun i => expNegInvGlue.iteratedDeriv_scaled_uniform_bound (1 : ℝ[X]) i
  let A : ℝ := ∑ i ∈ range (r + 1), (r.choose i : ℝ) * C (r - i)
  refine ⟨A, sum_nonneg (fun i _ => mul_nonneg (by positivity) (hC _)), ?_⟩
  intro f B c T t hf hB hc hT ht hjet
  have hf' : ContDiffAt ℝ r f t := hf.of_le (by exact_mod_cast (le_top : (r : ℕ∞) ≤ ⊤)) |>.contDiffAt
  have hg : ContDiffAt ℝ r (fun x => expNegInvGlue (x / c)) t := by
    fun_prop
  rw [iteratedDeriv_fun_mul hf' hg]
  calc
    _ ≤ ∑ i ∈ range (r + 1), ‖(r.choose i : ℝ) * iteratedDeriv i f t *
        iteratedDeriv (r - i) (fun x => expNegInvGlue (x / c)) t‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ range (r + 1), (r.choose i : ℝ) * B * (C (r - i) * Real.exp (-c / (2 * T))) := by
      apply sum_le_sum
      intro i hi
      rw [norm_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), Real.norm_eq_abs]
      have hg' : ‖iteratedDeriv (r - i) (fun x => expNegInvGlue (x / c)) t‖ ≤
          C (r - i) * Real.exp (-c / (2 * T)) := by
        simpa only [Polynomial.eval_one, one_mul] using hb (r - i) c T t hc hT ht
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hjet i (by simpa using hi)) (Nat.cast_nonneg _))
        hg' (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hB)
    _ = B * A * Real.exp (-c / (2 * T)) := by
      dsimp only [A]
      rw [mul_sum, sum_mul]
      apply sum_congr rfl
      intro i _
      ring

/-- The constants are chosen before the positive time bound. -/
theorem iteratedDeriv_optimalImageMode_gaussian_coefficients (r : ℕ) :
    ∃ C E : ℝ, 0 ≤ C ∧ 0 ≤ E ∧ ∀ T : ℝ, 0 < T → ∀ n : ℕ, ∀ t : ℝ, t ≤ T →
      ‖iteratedDeriv r (optimalImageMode n) t‖ ≤
        (2 * (29 + T) * C + 12 * E * (T + 1)) * ((n : ℝ) + 1) ^ 2 *
          Real.exp (-4 * ((n : ℝ) + 1) ^ 2 / T) := by
  obtain ⟨C, hC, hg⟩ := iteratedDeriv_mul_scaled_glue_uniform_bound r
  obtain ⟨E, hE, hI⟩ := iteratedDeriv_inverseExponentialIntegral_uniform_bound r
  refine ⟨C, E, hC, hE, fun T hT n t ht => ?_⟩
  by_cases ht0 : 0 < t
  swap
  · rw [iteratedDeriv_optimalImageMode_of_nonpos n r (le_of_not_gt ht0), norm_zero]
    positivity
  let m := (n : ℝ) + 1
  let c : ℝ := 8 * m ^ 2
  let d : ℝ := 8 * m * (m + 1)
  let B : ℝ := 28 * m ^ 2 + T + 1
  let e : ℝ := Real.exp (-4 * m ^ 2 / T)
  have hm : 1 ≤ m := by dsimp [m]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hm2 : 1 ≤ m ^ 2 := by nlinarith
  have hc : 1 ≤ c := by dsimp [c]; nlinarith
  have hd : 1 ≤ d := by dsimp [d]; nlinarith
  have hce : Real.exp (-c / (2 * T)) = e := by dsimp [c, e]; congr 1; ring
  have hde : Real.exp (-d / (2 * T)) ≤ e := by
    apply Real.exp_le_exp.mpr
    dsimp only [d, e]
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * T) hT).mpr
    nlinarith
  have he : 0 ≤ e := Real.exp_nonneg _
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hAcont : ContDiff ℝ ∞ (optimalImageCoefficientA n) := by
    unfold optimalImageCoefficientA
    fun_prop
  have hBcont : ContDiff ℝ ∞ (optimalImageCoefficientB n) := by
    unfold optimalImageCoefficientB
    fun_prop
  let f : ℝ → ℝ := fun x => optimalImageCoefficientA n x * expNegInvGlue (x / c)
  let g : ℝ → ℝ := fun x => optimalImageCoefficientB n x * expNegInvGlue (x / d)
  let u : ℝ → ℝ := fun x => 4 * m ^ 2 * inverseExponentialIntegral c x
  let v : ℝ → ℝ := fun x => 4 * m * (m + 1) * inverseExponentialIntegral d x
  have hf : ‖iteratedDeriv r f t‖ ≤ B * C * e := by
    simpa only [f, hce] using hg (optimalImageCoefficientA n) B c T t hAcont hB hc hT ht
      (fun i _ => iteratedDeriv_optimalImageCoefficientA_bound n i ht0.le ht)
  have hg' : ‖iteratedDeriv r g t‖ ≤ B * C * e := by
    exact (hg (optimalImageCoefficientB n) B d T t hBcont hB hd hT ht
      (fun i _ => iteratedDeriv_optimalImageCoefficientB_bound n i ht0.le ht)).trans
      (mul_le_mul_of_nonneg_left hde (mul_nonneg hB hC))
  have hu : ‖iteratedDeriv r u t‖ ≤ 4 * m ^ 2 * (E * (T + 1) * e) := by
    dsimp only [u]
    rw [iteratedDeriv_const_mul_field, norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (by simpa only [hce] using hI c T t hc hT ht) (by positivity)
  have hv : ‖iteratedDeriv r v t‖ ≤ 8 * m ^ 2 * (E * (T + 1) * e) := by
    dsimp only [v]
    rw [iteratedDeriv_const_mul_field, norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hb := (hI d T t hd hT ht).trans
      (mul_le_mul_of_nonneg_left hde (by positivity : 0 ≤ E * (T + 1)))
    exact mul_le_mul (show 4 * m * (m + 1) ≤ 8 * m ^ 2 by nlinarith) hb
      (norm_nonneg _) (by positivity)
  have hfc : ContDiff ℝ r f := by
    apply (hAcont.of_le (by exact_mod_cast (le_top : (r : ℕ∞) ≤ ⊤))).mul
    fun_prop
  have hgc : ContDiff ℝ r g := by
    apply (hBcont.of_le (by exact_mod_cast (le_top : (r : ℕ∞) ≤ ⊤))).mul
    fun_prop
  have huc : ContDiff ℝ r u := by
    exact (contDiff_const.mul (contDiff_inverseExponentialIntegral (by linarith : 0 < c))).of_le
      (by exact_mod_cast (le_top : (r : ℕ∞) ≤ ⊤))
  have hvc : ContDiff ℝ r v := by
    exact (contDiff_const.mul (contDiff_inverseExponentialIntegral (by linarith : 0 < d))).of_le
      (by exact_mod_cast (le_top : (r : ℕ∞) ≤ ⊤))
  have hmode : optimalImageMode n = (f + g + u) - v := by
    funext x
    rfl
  rw [hmode]
  change ‖iteratedDeriv r (fun x => (f x + g x + u x) - v x) t‖ ≤ _
  rw [iteratedDeriv_fun_sub ((hfc.add hgc).add huc).contDiffAt hvc.contDiffAt,
    iteratedDeriv_fun_add (hfc.add hgc).contDiffAt huc.contDiffAt,
    iteratedDeriv_fun_add hfc.contDiffAt hgc.contDiffAt]
  have hB' : B ≤ (29 + T) * m ^ 2 := by dsimp [B]; nlinarith
  calc
    _ ≤ ‖iteratedDeriv r f t‖ + ‖iteratedDeriv r g t‖ + ‖iteratedDeriv r u t‖ +
        ‖iteratedDeriv r v t‖ := by
      exact (norm_sub_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ B * C * e + B * C * e + 4 * m ^ 2 * (E * (T + 1) * e) +
        8 * m ^ 2 * (E * (T + 1) * e) := add_le_add (add_le_add (add_le_add hf hg') hu) hv
    _ ≤ (2 * (29 + T) * C + 12 * E * (T + 1)) * m ^ 2 * e := by
      nlinarith [mul_le_mul_of_nonneg_right hB' (mul_nonneg hC he)]

/-- Every fixed derivative order has an index-polynomial Gaussian envelope on `Iic T`. -/
theorem iteratedDeriv_optimalImageMode_gaussian_bound (r : ℕ) {T : ℝ} (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ t : ℝ, t ≤ T →
      ‖iteratedDeriv r (optimalImageMode n) t‖ ≤
        C * ((n : ℝ) + 1) ^ 2 * Real.exp (-4 * ((n : ℝ) + 1) ^ 2 / T) := by
  obtain ⟨C, E, hC, hE, hb⟩ := iteratedDeriv_optimalImageMode_gaussian_coefficients r
  exact ⟨2 * (29 + T) * C + 12 * E * (T + 1), by positivity, hb T hT⟩

end BrownianAffine
