import PLAStochastic.Swing.ConstantEvaluation.Fluctuation.SpitzerAtom
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Monotonicity of `p_a / a` from the Spitzer series (roadmap 1.4, step 3)

With `Q(a) = ∑_{n≥1} Φ(-a√n)/n` (`spitzerExponent`) and `p_a = e^{-Q(a)}`, the paper shows
`d/da log(p_a/a) = ∑_{n≥1} n^{-1/2} φ(a√n) - 1/a < 0` by comparing the antitone sum with its
integral.  We avoid differentiating the series: for `0 < a ≤ c`,

  `Q(a) - Q(c) = ∑ P(a√n < Z ≤ c√n)/n ≤ (c - a) ∑_{n≥1} n^{-1/2} φ(a√n) ≤ (c - a)/a`,

using `P(s < Z ≤ t) ≤ (t - s) φ(s)` and `∑_{n≥1} f(n) ≤ ∫₀^∞ f` for the antitone
`f(x) = x^{-1/2} φ(a√x)`, whose integral is `1/a` (substitution `x = y²`).  Since
`log c - log a ≥ (c - a)/c`, the function `F(t) = -Q(t) - log t` satisfies the local bound
`F(y) - F(x) ≤ (y - x)²/a²` on `[a, c]`, and telescoping (`sub_le_of_local_quadratic_bound`)
gives `F(c) ≤ F(a)`, i.e. `p_c / c ≤ p_a / a`.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Real
open scoped ENNReal NNReal Topology
namespace SwingRepair
namespace Fluctuation

/-! ### The kernel `x^{-1/2} e^{-t²x/2}` -/

/-- `k_t(x) = x^{-1/2} exp(-(t√x)²/2)`. -/
def sqrtGaussKernel (t x : ℝ) : ℝ := (Real.sqrt x)⁻¹ * Real.exp (-(t * Real.sqrt x) ^ 2 / 2)

theorem sqrtGaussKernel_nonneg (t x : ℝ) : 0 ≤ sqrtGaussKernel t x :=
  mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg x)) (Real.exp_pos _).le

theorem sqrtGaussKernel_antitoneOn (t : ℝ) : AntitoneOn (sqrtGaussKernel t) (Ioi 0) := by
  intro x hx y _ hxy
  have hx0 : 0 < x := hx
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hsxy : Real.sqrt x ≤ Real.sqrt y := Real.sqrt_le_sqrt hxy
  unfold sqrtGaussKernel
  refine mul_le_mul ?_ ?_ (Real.exp_pos _).le (inv_nonneg.mpr (Real.sqrt_nonneg x))
  · exact inv_anti₀ hsx hsxy
  · refine Real.exp_le_exp.mpr ?_
    have : (t * Real.sqrt x) ^ 2 ≤ (t * Real.sqrt y) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hx0.le, Real.sq_sqrt (hx0.le.trans hxy)]
      exact mul_le_mul_of_nonneg_left hxy (sq_nonneg t)
    linarith

/-- On `(0, ∞)`, `k_t(x) = x^{1/2 - 1} · g(x^{1/2})` with `g(y) = exp(-(t²/2) y²)`. -/
theorem sqrtGaussKernel_eq_rpow {t x : ℝ} (hx : 0 < x) :
    sqrtGaussKernel t x =
      x ^ ((1 : ℝ) / 2 - 1) * Real.exp (-(t ^ 2 / 2) * (x ^ ((1 : ℝ) / 2)) ^ 2) := by
  unfold sqrtGaussKernel
  have h1 : x ^ ((1 : ℝ) / 2 - 1) = (Real.sqrt x)⁻¹ := by
    rw [show (1 : ℝ) / 2 - 1 = -(1 / 2) by norm_num, Real.rpow_neg hx.le, Real.sqrt_eq_rpow]
  rw [h1, Real.sqrt_eq_rpow]
  congr 2
  ring

theorem sqrtGaussKernel_integrableOn {t : ℝ} (ht : 0 < t) :
    IntegrableOn (sqrtGaussKernel t) (Ioi 0) := by
  have hb : 0 < t ^ 2 / 2 := by positivity
  have hg : IntegrableOn (fun y : ℝ => Real.exp (-(t ^ 2 / 2) * y ^ 2)) (Ioi 0) :=
    (integrable_exp_neg_mul_sq hb).integrableOn
  have := (integrableOn_Ioi_comp_rpow_iff' (fun y : ℝ => Real.exp (-(t ^ 2 / 2) * y ^ 2))
    (p := (1 : ℝ) / 2) (by norm_num)).mpr hg
  refine this.congr_fun (fun x hx => ?_) measurableSet_Ioi
  simp only [smul_eq_mul]
  exact (sqrtGaussKernel_eq_rpow hx).symm

/-- `∫₀^∞ k_t = √(2π)/t`. -/
theorem integral_sqrtGaussKernel {t : ℝ} (ht : 0 < t) :
    ∫ x in Ioi (0 : ℝ), sqrtGaussKernel t x = Real.sqrt (2 * π) / t := by
  have hb : 0 < t ^ 2 / 2 := by positivity
  have hsub := integral_comp_rpow_Ioi_of_pos (g := fun y : ℝ => Real.exp (-(t ^ 2 / 2) * y ^ 2))
    (p := (1 : ℝ) / 2) (by norm_num)
  rw [integral_gaussian_Ioi] at hsub
  have hcongr : ∫ x in Ioi (0 : ℝ), sqrtGaussKernel t x =
      ∫ x in Ioi (0 : ℝ), (2 : ℝ) * (((1 : ℝ) / 2 * x ^ ((1 : ℝ) / 2 - 1)) •
        Real.exp (-(t ^ 2 / 2) * (x ^ ((1 : ℝ) / 2)) ^ 2)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    rw [sqrtGaussKernel_eq_rpow hx, smul_eq_mul]
    ring
  rw [hcongr, integral_const_mul, hsub]
  have hpi : 0 < π := Real.pi_pos
  have : Real.sqrt (π / (t ^ 2 / 2)) = Real.sqrt (2 * π) / t := by
    rw [show π / (t ^ 2 / 2) = (2 * π) / t ^ 2 by field_simp, Real.sqrt_div' _ (sq_nonneg t),
      Real.sqrt_sq ht.le]
  rw [this]
  ring

/-- **Series–integral comparison**: every finite sum `∑_{n ∈ s} k_t(n+1) ≤ √(2π)/t`. -/
theorem sum_sqrtGaussKernel_le {t : ℝ} (ht : 0 < t) (s : Finset ℕ) :
    ∑ n ∈ s, sqrtGaussKernel t (n + 1 : ℕ) ≤ Real.sqrt (2 * π) / t := by
  set F : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (sqrtGaussKernel t x) with hF
  -- each term is dominated by the integral over `(n, n+1]`
  have hterm : ∀ n : ℕ, ENNReal.ofReal (sqrtGaussKernel t (n + 1 : ℕ)) ≤
      ∫⁻ x in Ioc (n : ℝ) ((n + 1 : ℕ) : ℝ), F x := by
    intro n
    have hvol : volume (Ioc (n : ℝ) ((n + 1 : ℕ) : ℝ)) = 1 := by
      rw [Real.volume_Ioc]; push_cast; simp
    calc ENNReal.ofReal (sqrtGaussKernel t (n + 1 : ℕ))
        = ∫⁻ _ in Ioc (n : ℝ) ((n + 1 : ℕ) : ℝ), ENNReal.ofReal (sqrtGaussKernel t (n + 1 : ℕ)) := by
          rw [setLIntegral_const, hvol, mul_one]
      _ ≤ ∫⁻ x in Ioc (n : ℝ) ((n + 1 : ℕ) : ℝ), F x := by
          refine setLIntegral_mono' measurableSet_Ioc fun x hx => ENNReal.ofReal_le_ofReal ?_
          have hx0 : (0 : ℝ) < x := lt_of_le_of_lt (Nat.cast_nonneg n) hx.1
          have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
          exact sqrtGaussKernel_antitoneOn t hx0 hn1 hx.2
  have hdisj : Pairwise (Function.onFun Disjoint fun n : ℕ => Ioc (n : ℝ) ((n + 1 : ℕ) : ℝ)) := by
    intro m n hmn
    rw [Function.onFun, Set.disjoint_left]
    intro x hxm hxn
    rcases lt_or_gt_of_ne hmn with h | h
    · have h1 : ((m + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast h
      linarith [hxm.2, hxn.1]
    · have h1 : ((n + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast h
      linarith [hxn.2, hxm.1]
  have hsub : (⋃ n : ℕ, Ioc (n : ℝ) ((n + 1 : ℕ) : ℝ)) ⊆ Ioi 0 := by
    intro x hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    exact lt_of_le_of_lt (Nat.cast_nonneg n) hn.1
  have hint : ∫⁻ x in Ioi (0 : ℝ), F x = ENNReal.ofReal (Real.sqrt (2 * π) / t) := by
    rw [← integral_sqrtGaussKernel ht, ofReal_integral_eq_lintegral_ofReal
      (sqrtGaussKernel_integrableOn ht) (ae_of_all _ fun x => sqrtGaussKernel_nonneg t x)]
  have hENN : ENNReal.ofReal (∑ n ∈ s, sqrtGaussKernel t (n + 1 : ℕ)) ≤
      ENNReal.ofReal (Real.sqrt (2 * π) / t) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun n _ => sqrtGaussKernel_nonneg t _]
    calc ∑ n ∈ s, ENNReal.ofReal (sqrtGaussKernel t (n + 1 : ℕ))
        ≤ ∑' n : ℕ, ENNReal.ofReal (sqrtGaussKernel t (n + 1 : ℕ)) := ENNReal.sum_le_tsum s
      _ ≤ ∑' n : ℕ, ∫⁻ x in Ioc (n : ℝ) ((n + 1 : ℕ) : ℝ), F x := ENNReal.tsum_le_tsum hterm
      _ = ∫⁻ x in ⋃ n : ℕ, Ioc (n : ℝ) ((n + 1 : ℕ) : ℝ), F x :=
          (lintegral_iUnion (fun n => measurableSet_Ioc) hdisj F).symm
      _ ≤ ∫⁻ x in Ioi (0 : ℝ), F x := lintegral_mono_set hsub
      _ = ENNReal.ofReal (Real.sqrt (2 * π) / t) := hint
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hENN

/-! ### The local bound on the Spitzer exponent -/

theorem gaussianPDFReal_zero_one (y : ℝ) :
    gaussianPDFReal 0 1 y = (Real.sqrt (2 * π))⁻¹ * Real.exp (-y ^ 2 / 2) := by
  simp [gaussianPDFReal]

/-- `Φ(-a√x) - Φ(-c√x) ≤ (c - a) √x φ(a√x)` for `0 ≤ a ≤ c`, `0 ≤ x`. -/
theorem gaussianTailSqrt_sub_drift_le {a c x : ℝ} (ha : 0 ≤ a) (hac : a ≤ c) :
    gaussianTailSqrt a x - gaussianTailSqrt c x ≤
      (c - a) * Real.sqrt x * gaussianPDFReal 0 1 (a * Real.sqrt x) := by
  have hsx := Real.sqrt_nonneg x
  have hle : a * Real.sqrt x ≤ c * Real.sqrt x := mul_le_mul_of_nonneg_right hac hsx
  have hsub : gaussianTailSqrt a x - gaussianTailSqrt c x =
      (gaussianReal 0 1).real (Ioc (a * Real.sqrt x) (c * Real.sqrt x)) := by
    unfold gaussianTailSqrt
    rw [← Ioi_sdiff_Ioi, measureReal_sdiff (Ioi_subset_Ioi hle) measurableSet_Ioi]
  rw [hsub]
  have := gaussianReal_real_Ioc_le (mul_nonneg ha hsx) hle
  calc (gaussianReal 0 1).real (Ioc (a * Real.sqrt x) (c * Real.sqrt x))
      ≤ (c * Real.sqrt x - a * Real.sqrt x) * gaussianPDFReal 0 1 (a * Real.sqrt x) := this
    _ = (c - a) * Real.sqrt x * gaussianPDFReal 0 1 (a * Real.sqrt x) := by ring

/-- The `n`-th term of `Q(a) - Q(c)` is at most `(c - a)(√(2π))⁻¹ k_a(n)`. -/
theorem spitzer_term_sub_le {a c : ℝ} (ha : 0 ≤ a) (hac : a ≤ c) {x : ℝ} (hx : 0 < x) :
    (gaussianTailSqrt a x - gaussianTailSqrt c x) / x ≤
      (c - a) * (Real.sqrt (2 * π))⁻¹ * sqrtGaussKernel a x := by
  have h := gaussianTailSqrt_sub_drift_le (x := x) ha hac
  rw [gaussianPDFReal_zero_one] at h
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hx' : Real.sqrt x / x = (Real.sqrt x)⁻¹ := by
    rw [Real.sqrt_div_self', one_div]
  calc (gaussianTailSqrt a x - gaussianTailSqrt c x) / x
      ≤ (c - a) * Real.sqrt x * ((Real.sqrt (2 * π))⁻¹ *
          Real.exp (-(a * Real.sqrt x) ^ 2 / 2)) / x := by gcongr
    _ = (c - a) * (Real.sqrt (2 * π))⁻¹ *
          ((Real.sqrt x / x) * Real.exp (-(a * Real.sqrt x) ^ 2 / 2)) := by ring
    _ = (c - a) * (Real.sqrt (2 * π))⁻¹ * sqrtGaussKernel a x := by
        rw [hx']; rfl

theorem summable_spitzer_term {a : ℝ} (ha : 0 < a) :
    Summable fun n : ℕ => gaussianTailSqrt a (n + 1 : ℕ) / (n + 1 : ℕ) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (summable_gaussianTailSqrt ha)
  · exact div_nonneg (gaussianTailSqrt_nonneg _ _) (Nat.cast_nonneg _)
  · have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    rw [div_le_iff₀ (by positivity)]
    exact le_mul_of_one_le_right (gaussianTailSqrt_nonneg _ _) h1

/-- **Local bound**: `Q(a) - Q(c) ≤ (c - a)/a` for `0 < a ≤ c`. -/
theorem spitzerExponent_sub_le {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) :
    spitzerExponent a - spitzerExponent c ≤ (c - a) / a := by
  have hc : 0 < c := ha.trans_le hac
  unfold spitzerExponent
  rw [← (summable_spitzer_term ha).tsum_sub (summable_spitzer_term hc)]
  refine tsum_le_of_sum_le' (div_nonneg (by linarith) ha.le) fun s => ?_
  have hstep : ∀ n ∈ s,
      gaussianTailSqrt a (n + 1 : ℕ) / (n + 1 : ℕ) - gaussianTailSqrt c (n + 1 : ℕ) / (n + 1 : ℕ) ≤
        (c - a) * (Real.sqrt (2 * π))⁻¹ * sqrtGaussKernel a (n + 1 : ℕ) := by
    intro n _
    rw [← sub_div]
    exact spitzer_term_sub_le ha.le hac (by positivity)
  calc ∑ n ∈ s, (gaussianTailSqrt a (n + 1 : ℕ) / (n + 1 : ℕ) -
        gaussianTailSqrt c (n + 1 : ℕ) / (n + 1 : ℕ))
      ≤ ∑ n ∈ s, (c - a) * (Real.sqrt (2 * π))⁻¹ * sqrtGaussKernel a (n + 1 : ℕ) :=
        Finset.sum_le_sum hstep
    _ = (c - a) * (Real.sqrt (2 * π))⁻¹ * ∑ n ∈ s, sqrtGaussKernel a (n + 1 : ℕ) := by
        rw [Finset.mul_sum]
    _ ≤ (c - a) * (Real.sqrt (2 * π))⁻¹ * (Real.sqrt (2 * π) / a) := by
        gcongr
        exact sum_sqrtGaussKernel_le ha s
    _ = (c - a) / a := by
        have : Real.sqrt (2 * π) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
        field_simp

/-! ### `p_a / a` is antitone -/

/-- `F(t) = -Q(t) - log t = log(p_t / t)` is antitone on `(0, ∞)`. -/
theorem neg_spitzerExponent_sub_log_antitone {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) :
    -spitzerExponent c - Real.log c ≤ -spitzerExponent a - Real.log a := by
  have hC : (0 : ℝ) ≤ 1 / a ^ 2 := by positivity
  have h := sub_le_of_local_quadratic_bound (f := fun t => -spitzerExponent t - Real.log t)
    (a := a) (c := c) (q := 0) (C := 1 / a ^ 2) hac hC (fun x y hx hxy hy => ?_)
  · simpa using h
  · have hx0 : 0 < x := ha.trans_le hx
    have hy0 : 0 < y := hx0.trans_le hxy
    have hQ := spitzerExponent_sub_le hx0 hxy
    -- `log y - log x ≥ (y - x)/y`
    have hlog : (y - x) / y ≤ Real.log y - Real.log x := by
      have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hy0 hx0)
      rw [Real.log_div hy0.ne' hx0.ne'] at h1
      have : 1 - (y / x)⁻¹ = (y - x) / y := by field_simp
      linarith
    have hxy2 : (y - x) / x - (y - x) / y = (y - x) * (y - x) / (x * y) := by
      field_simp
    have hxa : a ^ 2 ≤ x * y := by nlinarith
    have hfrac : (y - x) * (y - x) / (x * y) ≤ (y - x) * (y - x) / a ^ 2 := by
      apply div_le_div_of_nonneg_left (mul_self_nonneg _) (by positivity) hxa
    show -spitzerExponent y - Real.log y - (-spitzerExponent x - Real.log x) ≤
      (y - x) * (0 + 1 / a ^ 2 * (y - x))
    have : (y - x) * (0 + 1 / a ^ 2 * (y - x)) = (y - x) * (y - x) / a ^ 2 := by ring
    rw [this]
    linarith

/-- **`p_c / c ≤ p_a / a` for `0 < a ≤ c`.** -/
theorem exp_neg_spitzerExponent_div_antitone {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) :
    Real.exp (-spitzerExponent c) / c ≤ Real.exp (-spitzerExponent a) / a := by
  have hc : 0 < c := ha.trans_le hac
  have h := Real.exp_le_exp.mpr (neg_spitzerExponent_sub_log_antitone ha hac)
  rw [Real.exp_sub, Real.exp_sub, Real.exp_log ha, Real.exp_log hc] at h
  exact h

/-- Product form: `p_c · a ≤ p_a · c`. -/
theorem exp_neg_spitzerExponent_mul_le {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) :
    Real.exp (-spitzerExponent c) * a ≤ Real.exp (-spitzerExponent a) * c := by
  have hc : 0 < c := ha.trans_le hac
  have h := exp_neg_spitzerExponent_div_antitone ha hac
  rw [div_le_div_iff₀ hc ha] at h
  exact h

end Fluctuation
end SwingRepair
