import PLAStochastic.Index.GEP.PointwiseSmall.WeightedW1Tests
import PLAStochastic.Index.GEP.PointwiseSmall.RealAxis
import PLAStochastic.Index.GEP.Response.KappaBound

/-!
# C-16 support: characteristic functions against the weighted `W₁` distance

For two probability laws on `[0, ∞)`, `e^{iax} - 1` is the test with derivative
`ia e^{iat}`, so the real and imaginary parts are `testFn` of `-a sin(at)` and `a cos(at)`.
Both derivatives are bounded by `|a|`, and `pw_abs_sub_le_dEtaL` gives
`‖∫ e^{iax} dμ - ∫ e^{iax} dρ‖ ≤ 2 |a| d_γ(μ, ρ)`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

theorem testFn_neg_mul_sin {a x : ℝ} (hx : 0 < x) :
    testFn (fun t => -a * Real.sin (a * t)) x = Real.cos (a * x) - 1 := by
  rw [testFn, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hx.le]
  have hderiv : ∀ t ∈ uIcc 0 x, HasDerivAt (fun t => Real.cos (a * t)) (-a * Real.sin (a * t)) t := by
    intro t _
    have h := ((hasDerivAt_id' t).const_mul a).cos
    convert h using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous fun t => -a * Real.sin (a * t)).intervalIntegrable _ _)]
  simp

theorem testFn_mul_cos {a x : ℝ} (hx : 0 < x) :
    testFn (fun t => a * Real.cos (a * t)) x = Real.sin (a * x) := by
  rw [testFn, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hx.le]
  have hderiv : ∀ t ∈ uIcc 0 x, HasDerivAt (fun t => Real.sin (a * t)) (a * Real.cos (a * t)) t := by
    intro t _
    have h := ((hasDerivAt_id' t).const_mul a).sin
    convert h using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous fun t => a * Real.cos (a * t)).intervalIntegrable _ _)]
  simp

/-- On a law carried by `[0, ∞)`, `∫ (cos(ax) - 1) dμ` is the test of `-a sin(at)`. -/
theorem integral_cos_sub_one_eq_testFn {μ : Measure ℝ} (hμ : μ (Iio 0) = 0) (a : ℝ) :
    (∫ x, (Real.cos (a * x) - 1) ∂μ) = ∫ x, testFn (fun t => -a * Real.sin (a * t)) x ∂μ := by
  apply integral_congr_ae
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hμ] with x hx
  have hx0 : 0 ≤ x := by simpa using hx
  rcases hx0.eq_or_lt with h | h
  · rw [← h, testFn_nonneg_arg le_rfl]; simp
  · exact (testFn_neg_mul_sin h).symm

theorem integral_sin_eq_testFn {μ : Measure ℝ} (hμ : μ (Iio 0) = 0) (a : ℝ) :
    (∫ x, Real.sin (a * x) ∂μ) = ∫ x, testFn (fun t => a * Real.cos (a * t)) x ∂μ := by
  apply integral_congr_ae
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hμ] with x hx
  have hx0 : 0 ≤ x := by simpa using hx
  rcases hx0.eq_or_lt with h | h
  · rw [← h, testFn_nonneg_arg le_rfl]; simp
  · exact (testFn_mul_cos h).symm

/-- `∫ e^{iax} dμ = ∫ cos(ax) dμ + i ∫ sin(ax) dμ` for a finite measure. -/
theorem integral_cexp_I_mul_eq {μ : Measure ℝ} [IsFiniteMeasure μ] (a : ℝ) :
    (∫ x, Complex.exp (Complex.I * a * x) ∂μ) =
      ((∫ x, Real.cos (a * x) ∂μ : ℝ) : ℂ) + ((∫ x, Real.sin (a * x) ∂μ : ℝ) : ℂ) * Complex.I := by
  have hpt : ∀ x : ℝ, Complex.exp (Complex.I * a * x) =
      ((Real.cos (a * x) : ℝ) : ℂ) + ((Real.sin (a * x) : ℝ) : ℂ) * Complex.I := by
    intro x
    rw [show Complex.I * a * x = ((a * x : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  simp_rw [hpt]
  have hc : Integrable (fun x : ℝ => ((Real.cos (a * x) : ℝ) : ℂ)) μ :=
    Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x => by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hs : Integrable (fun x : ℝ => ((Real.sin (a * x) : ℝ) : ℂ) * Complex.I) μ :=
    Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x => by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact Real.abs_sin_le_one _)
  rw [integral_add hc hs, integral_mul_const, integral_complex_ofReal, integral_complex_ofReal]

/-- `x e^{γx}` is integrable on `[0,∞)` once some larger exponential is. -/
theorem integrable_mul_exp_of_exp_integrable {μ : Measure ℝ} (hμ : μ (Iio 0) = 0)
    {γ ζ : ℝ} (hγζ : γ < ζ) (hi : Integrable (fun x : ℝ => Real.exp (ζ * x)) μ) :
    Integrable (fun x : ℝ => x * Real.exp (γ * x)) μ := by
  refine (hi.const_mul (1 / (ζ - γ))).mono' (by fun_prop) ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hμ] with x hx
  have hx0 : 0 ≤ x := by simpa using hx
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx0 (Real.exp_pos _).le)]
  simpa only [div_eq_mul_inv, mul_comm, mul_one] using mul_exp_le_exp_div (x := x) hγζ

/-- **Characteristic functions against the weighted `W₁` distance.** -/
theorem norm_integral_cexp_sub_le_dEtaL {μ ρ : ProbabilityMeasure ℝ}
    (hμ : (μ : Measure ℝ) (Iio 0) = 0) (hρ : (ρ : Measure ℝ) (Iio 0) = 0) (a : ℝ) {γ : ℝ}
    (hγ : 0 ≤ γ)
    (hintμ : Integrable (fun x => x * Real.exp (γ * x)) (μ : Measure ℝ))
    (hintρ : Integrable (fun x => x * Real.exp (γ * x)) (ρ : Measure ℝ))
    (hfin : dEtaL γ μ ρ ≠ ⊤) :
    ‖(∫ x, Complex.exp (Complex.I * a * x) ∂(μ : Measure ℝ)) -
        ∫ x, Complex.exp (Complex.I * a * x) ∂(ρ : Measure ℝ)‖ ≤
      2 * |a| * (dEtaL γ μ ρ).toReal := by
  have hbound : ∀ s : ℝ, 0 ≤ s → |a| ≤ |a| * Real.exp (γ * s) := fun s hs =>
    le_mul_of_one_le_right (abs_nonneg a) (Real.one_le_exp (mul_nonneg hγ hs))
  have hχ₁ : ∀ s, 0 ≤ s → |-a * Real.sin (a * s)| ≤ |a| * Real.exp (γ * s) := fun s hs => by
    rw [abs_mul, abs_neg]
    exact (mul_le_of_le_one_right (abs_nonneg a) (Real.abs_sin_le_one _)).trans (hbound s hs)
  have hχ₂ : ∀ s, 0 ≤ s → |a * Real.cos (a * s)| ≤ |a| * Real.exp (γ * s) := fun s hs => by
    rw [abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg a) (Real.abs_cos_le_one _)).trans (hbound s hs)
  have hre := pw_abs_sub_le_dEtaL hμ hρ (by fun_prop : Measurable fun t => -a * Real.sin (a * t))
    hγ hχ₁ hintμ hintρ hfin
  have him := pw_abs_sub_le_dEtaL hμ hρ (by fun_prop : Measurable fun t => a * Real.cos (a * t))
    hγ hχ₂ hintμ hintρ hfin
  rw [← integral_cos_sub_one_eq_testFn hμ, ← integral_cos_sub_one_eq_testFn hρ] at hre
  rw [← integral_sin_eq_testFn hμ, ← integral_sin_eq_testFn hρ] at him
  have hc : ∀ m : Measure ℝ, IsProbabilityMeasure m →
      (∫ x, (Real.cos (a * x) - 1) ∂m) = (∫ x, Real.cos (a * x) ∂m) - 1 := by
    intro m _
    rw [integral_sub (Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)) (integrable_const _),
      integral_const, probReal_univ, one_smul]
  rw [hc _ inferInstance, hc _ inferInstance, sub_sub_sub_cancel_right] at hre
  rw [integral_cexp_I_mul_eq, integral_cexp_I_mul_eq]
  have hsplit : ((∫ x, Real.cos (a * x) ∂(μ : Measure ℝ) : ℝ) : ℂ) +
      ((∫ x, Real.sin (a * x) ∂(μ : Measure ℝ) : ℝ) : ℂ) * Complex.I -
      (((∫ x, Real.cos (a * x) ∂(ρ : Measure ℝ) : ℝ) : ℂ) +
      ((∫ x, Real.sin (a * x) ∂(ρ : Measure ℝ) : ℝ) : ℂ) * Complex.I) =
      (((∫ x, Real.cos (a * x) ∂(μ : Measure ℝ)) - ∫ x, Real.cos (a * x) ∂(ρ : Measure ℝ) : ℝ) : ℂ) +
      (((∫ x, Real.sin (a * x) ∂(μ : Measure ℝ)) - ∫ x, Real.sin (a * x) ∂(ρ : Measure ℝ) : ℝ) : ℂ) *
        Complex.I := by
    push_cast; ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs]
  linarith
