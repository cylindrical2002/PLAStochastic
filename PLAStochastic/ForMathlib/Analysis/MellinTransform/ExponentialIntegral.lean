import PLAStochastic.ForMathlib.Analysis.MellinTransform.InverseExponential
import PLAStochastic.ForMathlib.Analysis.SpecialFunctions.ExponentialIntegral

/-! # Mellin transform of `E₁ (c / t)`

For `c > 0` and `re q < 0`,

  `∫ t in Ioi 0, t ^ (q - 1) * E₁ (c / t) = -(c ^ q * Γ (-q)) / q`.

The proof writes `E₁ (x) = ∫ w in Ioi 1, exp (-x w) / w`, exchanges the two
integrals by Fubini, applies the inverse-exponential Mellin formula in `t`,
and integrates `w ^ (q - 1)` over `Ioi 1`.
-/
noncomputable section
open MeasureTheory Set Complex
namespace BrownianAffine

theorem exponentialIntegralE1_eq_integral_Ioi_one {x : ℝ} (hx : 0 < x) :
    exponentialIntegralE1 x = ∫ w in Ioi (1 : ℝ), Real.exp (-(x * w)) / w := by
  have h := integral_comp_mul_left_Ioi (fun v : ℝ => Real.exp (-v) / v) 1 hx
  rw [mul_one] at h
  have h2 : ∫ w in Ioi (1 : ℝ), Real.exp (-(x * w)) / w =
      ∫ w in Ioi (1 : ℝ), x * (Real.exp (-(x * w)) / (x * w)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun w hw => ?_)
    have hw0 : w ≠ 0 := (zero_lt_one.trans (mem_Ioi.mp hw)).ne'
    field_simp
  rw [h2, integral_const_mul, h, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hx.ne', one_mul]
  simp [exponentialIntegralE1, hx]

/-- The Fubini integrand `t ^ (q - 1) * exp (-(c / t) w) / w`. -/
private def e1Kernel (q : ℂ) (c : ℝ) (t w : ℝ) : ℂ :=
  (t : ℂ) ^ (q - 1) * ((Real.exp (-(c / t * w)) / w : ℝ) : ℂ)

private theorem e1Kernel_eq (q : ℂ) (c t w : ℝ) :
    e1Kernel q c t w =
      ((w⁻¹ : ℝ) : ℂ) * ((t : ℂ) ^ (q - 1) * ((Real.exp (-(c * w) / t) : ℝ) : ℂ)) := by
  unfold e1Kernel
  rw [show -(c / t * w) = -(c * w) / t by ring, div_eq_inv_mul (Real.exp _), ofReal_mul]
  ring

private theorem measurable_e1Kernel (q : ℂ) (c : ℝ) :
    Measurable (Function.uncurry (e1Kernel q c)) := by
  unfold e1Kernel Function.uncurry
  fun_prop

private theorem integrable_e1Kernel {q : ℂ} (hq : q.re < 0) {c : ℝ} (hc : 0 < c) :
    Integrable (Function.uncurry (e1Kernel q c))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (1 : ℝ)))) := by
  rw [integrable_prod_iff' (measurable_e1Kernel q c).aestronglyMeasurable]
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    have hw0 : 0 < w := zero_lt_one.trans hw
    have h := (integrableOn_cpow_mul_exp_neg_div hq (mul_pos hc hw0)).const_mul
      ((w⁻¹ : ℝ) : ℂ)
    simpa only [Function.uncurry_apply_pair, e1Kernel_eq] using h
  · have hnorm : ∀ w ∈ Ioi (1 : ℝ),
        c ^ q.re * Real.Gamma (-q.re) * w ^ (q.re - 1) =
          ∫ t in Ioi (0 : ℝ), ‖Function.uncurry (e1Kernel q c) (t, w)‖ := by
      intro w hw
      have hw0 : 0 < w := zero_lt_one.trans hw
      have he : ∫ t in Ioi (0 : ℝ), ‖Function.uncurry (e1Kernel q c) (t, w)‖ =
          ∫ t in Ioi (0 : ℝ), w⁻¹ * (t ^ (q.re - 1) * Real.exp (-(c * w) / t)) := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
        simp only [Function.uncurry_apply_pair, e1Kernel_eq, norm_mul,
          norm_cpow_mul_exp_neg_div (q := q) (c := c * w) ht, Complex.norm_real,
          Real.norm_of_nonneg (inv_pos.mpr hw0).le]
      rw [he, integral_const_mul, integral_rpow_mul_exp_neg_div hq (mul_pos hc hw0),
        Real.mul_rpow hc.le hw0.le, Real.rpow_sub_one hw0.ne']
      field_simp
    have hi := (integrableOn_Ioi_rpow_of_lt (a := q.re - 1) (by linarith)
      zero_lt_one).const_mul (c ^ q.re * Real.Gamma (-q.re))
    exact IntegrableOn.congr_fun (μ := volume) hi hnorm measurableSet_Ioi

private theorem integral_e1Kernel_right {q : ℂ} {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    ∫ w in Ioi (1 : ℝ), e1Kernel q c t w =
      (t : ℂ) ^ (q - 1) * ((exponentialIntegralE1 (c / t) : ℝ) : ℂ) := by
  simp only [e1Kernel]
  rw [integral_const_mul, integral_complex_ofReal,
    exponentialIntegralE1_eq_integral_Ioi_one (div_pos hc ht)]

theorem integrableOn_cpow_mul_exponentialIntegralE1_div {q : ℂ} (hq : q.re < 0) {c : ℝ}
    (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (q - 1) * ((exponentialIntegralE1 (c / t) : ℝ) : ℂ))
      (Ioi 0) := by
  have h := (integrable_e1Kernel hq hc).integral_prod_left
  refine IntegrableOn.congr_fun (μ := volume) h (fun t ht => ?_) measurableSet_Ioi
  exact integral_e1Kernel_right hc ht

theorem integral_cpow_mul_exponentialIntegralE1_div {q : ℂ} (hq : q.re < 0) {c : ℝ}
    (hc : 0 < c) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (q - 1) * ((exponentialIntegralE1 (c / t) : ℝ) : ℂ) =
      -((c : ℂ) ^ q * Gamma (-q)) / q := by
  have hswap := integral_integral_swap (integrable_e1Kernel hq hc)
  have hl : ∫ t in Ioi (0 : ℝ), ∫ w in Ioi (1 : ℝ), e1Kernel q c t w =
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (q - 1) * ((exponentialIntegralE1 (c / t) : ℝ) : ℂ) :=
    setIntegral_congr_fun measurableSet_Ioi (fun t ht => integral_e1Kernel_right hc ht)
  have hr : ∫ w in Ioi (1 : ℝ), ∫ t in Ioi (0 : ℝ), e1Kernel q c t w =
      ∫ w in Ioi (1 : ℝ), (c : ℂ) ^ q * Gamma (-q) * (w : ℂ) ^ (q - 1) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun w hw => ?_)
    have hw0 : 0 < w := zero_lt_one.trans hw
    have hw0' : (w : ℂ) ≠ 0 := ofReal_ne_zero.mpr hw0.ne'
    simp only [e1Kernel_eq]
    rw [integral_const_mul, integral_cpow_mul_exp_neg_div hq (mul_pos hc hw0), ofReal_mul,
      mul_cpow_ofReal_nonneg hc.le hw0.le, cpow_sub _ _ hw0', cpow_one, ofReal_inv]
    field_simp
  have hq0 : q ≠ 0 := by
    rintro rfl
    simp at hq
  rw [← hl, hswap, hr, integral_const_mul,
    integral_Ioi_cpow_of_lt (by simp only [sub_re, one_re]; linarith) zero_lt_one]
  simp only [ofReal_one, one_cpow, sub_add_cancel]
  field_simp

end BrownianAffine
