import PLAStochastic.Swing.Ladder.Renewal.RenewalMeasure
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # A uniform strong nonlattice bound from a common Lebesgue component

If an inter-arrival law dominates `c` times Lebesgue measure on `[1,2]`, its
characteristic function obeys `|φ(θ)| ≤ 1 - c(1-2/|θ|)`.  The bound depends on
the law only through `c`, so a family with a common component is uniformly
strongly nonlattice in the sense of Cramér's condition.  This is exactly the
nonlattice hypothesis required by the renewal expansion of `app:limit`.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Complex
open scoped ENNReal NNReal Topology Classical MeasureTheory
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- The exponential character on `[1,2]` has a small integral at high frequency. -/
theorem norm_integral_Icc_exp_mul_I {θ : ℝ} (hθ : θ ≠ 0) :
    ‖∫ x in Icc (1 : ℝ) 2, Complex.exp (θ*x*I)‖ ≤ 2/|θ| := by
  have hc : (θ : ℂ)*I ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, Complex.I_ne_zero, or_false]
    exact_mod_cast hθ
  have hfun : ∀ x : ℝ, Complex.exp ((θ : ℂ)*x*I) = Complex.exp (((θ : ℂ)*I)*x) := by
    intro x
    congr 1
    ring
  have hIcc : (∫ x in Icc (1 : ℝ) 2, Complex.exp (θ*x*I)) =
      ∫ x in (1 : ℝ)..2, Complex.exp (((θ : ℂ)*I)*x) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2),
      ← integral_Icc_eq_integral_Ioc]
    exact setIntegral_congr_fun measurableSet_Icc (fun x _ => hfun x)
  rw [hIcc, integral_exp_mul_complex hc]
  have hnum : ‖Complex.exp (((θ : ℂ)*I)*(2 : ℝ)) - Complex.exp (((θ : ℂ)*I)*(1 : ℝ))‖ ≤ 2 := by
    have h2 : ‖Complex.exp (((θ : ℂ)*I)*(2 : ℝ))‖ = 1 := by
      rw [show ((θ : ℂ)*I)*(2 : ℝ) = ((2*θ : ℝ) : ℂ)*I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    have h1 : ‖Complex.exp (((θ : ℂ)*I)*(1 : ℝ))‖ = 1 := by
      rw [show ((θ : ℂ)*I)*(1 : ℝ) = ((θ : ℝ) : ℂ)*I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    calc ‖Complex.exp (((θ : ℂ)*I)*(2 : ℝ)) - Complex.exp (((θ : ℂ)*I)*(1 : ℝ))‖
        ≤ ‖Complex.exp (((θ : ℂ)*I)*(2 : ℝ))‖ + ‖Complex.exp (((θ : ℂ)*I)*(1 : ℝ))‖ :=
          norm_sub_le _ _
      _ = 2 := by rw [h1, h2]; norm_num
  have hden : ‖(θ : ℂ)*I‖ = |θ| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [norm_div, hden]
  exact div_le_div_of_nonneg_right hnum (abs_pos.mpr hθ).le

/-- The uniform Cramér bound from a common Lebesgue component on `[1,2]`. -/
theorem norm_charFun_le_of_minorization {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {c : ℝ} (hc0 : 0 ≤ c)
    (hmin : ENNReal.ofReal c • volume.restrict (Icc (1 : ℝ) 2) ≤ ν)
    {θ : ℝ} (hθ : θ ≠ 0) :
    ‖charFun ν θ‖ ≤ 1 - c + c*(2/|θ|) := by
  set κ : Measure ℝ := ENNReal.ofReal c • volume.restrict (Icc (1 : ℝ) 2) with hκdef
  have hvol : volume (Icc (1 : ℝ) 2) = 1 := by
    rw [Real.volume_Icc]
    norm_num
  have hκuniv : κ univ = ENNReal.ofReal c := by
    rw [hκdef, Measure.smul_apply, Measure.restrict_apply_univ, hvol, smul_eq_mul, mul_one]
  have hκfin : IsFiniteMeasure κ := ⟨by rw [hκuniv]; exact ENNReal.ofReal_lt_top⟩
  have hc1 : c ≤ 1 := by
    have h : κ univ ≤ ν univ := hmin univ
    rw [hκuniv, measure_univ] at h
    exact ENNReal.ofReal_le_one.mp h
  set ρ : Measure ℝ := ν - κ with hρdef
  have hsum : ρ + κ = ν := Measure.sub_add_cancel_of_le hmin
  have hρuniv : ρ univ = ENNReal.ofReal (1-c) := by
    rw [hρdef, Measure.sub_apply MeasurableSet.univ hmin, measure_univ, hκuniv,
      ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hc0]
  have hρfin : IsFiniteMeasure ρ := ⟨by rw [hρuniv]; exact ENNReal.ofReal_lt_top⟩
  have hmeas : Measurable (fun x : ℝ => Complex.exp (θ*x*I)) := by
    apply Complex.measurable_exp.comp
    exact ((measurable_const.mul Complex.measurable_ofReal).mul measurable_const)
  have hnorm : ∀ x : ℝ, ‖Complex.exp ((θ : ℂ)*x*I)‖ = 1 := by
    intro x
    rw [show (θ : ℂ)*x*I = ((θ*x : ℝ) : ℂ)*I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hintρ : Integrable (fun x : ℝ => Complex.exp (θ*x*I)) ρ := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    refine (hasFiniteIntegral_const (1 : ℂ)).mono ?_
    filter_upwards with x
    rw [hnorm x, norm_one]
  have hintκ : Integrable (fun x : ℝ => Complex.exp (θ*x*I)) κ := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    refine (hasFiniteIntegral_const (1 : ℂ)).mono ?_
    filter_upwards with x
    rw [hnorm x, norm_one]
  have hsplit : charFun ν θ =
      (∫ x, Complex.exp (θ*x*I) ∂ρ) + ∫ x, Complex.exp (θ*x*I) ∂κ := by
    rw [charFun_apply_real, ← hsum, integral_add_measure hintρ hintκ]
  have hρbound : ‖∫ x, Complex.exp ((θ : ℂ)*x*I) ∂ρ‖ ≤ 1-c := by
    calc ‖∫ x, Complex.exp ((θ : ℂ)*x*I) ∂ρ‖ ≤ ∫ x, ‖Complex.exp ((θ : ℂ)*x*I)‖ ∂ρ :=
          norm_integral_le_integral_norm _
      _ = ∫ _x : ℝ, (1 : ℝ) ∂ρ := by
          exact integral_congr_ae (Filter.Eventually.of_forall (fun x => hnorm x))
      _ = ρ.real univ := by simp
      _ = 1-c := by
          rw [Measure.real, hρuniv, ENNReal.toReal_ofReal (by linarith)]
  have hκbound : ‖∫ x, Complex.exp ((θ : ℂ)*x*I) ∂κ‖ ≤ c*(2/|θ|) := by
    rw [hκdef, integral_smul_measure, ENNReal.toReal_ofReal hc0, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hc0]
    exact mul_le_mul_of_nonneg_left (norm_integral_Icc_exp_mul_I hθ) hc0
  calc ‖charFun ν θ‖ = ‖(∫ x, Complex.exp (θ*x*I) ∂ρ) + ∫ x, Complex.exp (θ*x*I) ∂κ‖ := by
        rw [hsplit]
    _ ≤ ‖∫ x, Complex.exp ((θ : ℂ)*x*I) ∂ρ‖ + ‖∫ x, Complex.exp ((θ : ℂ)*x*I) ∂κ‖ :=
        norm_add_le _ _
    _ ≤ (1-c) + c*(2/|θ|) := add_le_add hρbound hκbound

/-! ### The actual Gaussian ladder family is uniformly strongly nonlattice -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

theorem gaussianAscendingLadderLaw_charFun_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : μ.map (X 0) = gaussianReal 0 1)
    {M a : ℝ} (ha : 0 ≤ a) (haM : a ≤ M) {θ : ℝ} (hθ : θ ≠ 0) :
    ‖charFun (gaussianAscendingLadderLaw X μ a) θ‖ ≤
      1 - gaussianAscendingLadderCommonDensity M +
        gaussianAscendingLadderCommonDensity M*(2/|θ|) := by
  have hprob : IsProbabilityMeasure (gaussianAscendingLadderLaw X μ a) :=
    gaussianAscendingLadderLaw_isProbabilityMeasure hX hi a
  exact norm_charFun_le_of_minorization
    (gaussianAscendingLadderCommonDensity_pos M).le
    (gaussianAscendingLadderLaw_common_minorization hX hG ha haM) hθ

/-- Uniform strong nonlattice bound: on every compact drift interval `[0,M]`
the ladder-height characteristic functions stay a fixed distance below one at
every frequency of size at least `4`.  The gap depends only on `M`. -/
theorem gaussianAscendingLadderLaw_uniform_cramer
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : μ.map (X 0) = gaussianReal 0 1)
    {M a : ℝ} (ha : 0 ≤ a) (haM : a ≤ M) {θ : ℝ} (hθ : 4 ≤ |θ|) :
    ‖charFun (gaussianAscendingLadderLaw X μ a) θ‖ ≤
      1 - gaussianAscendingLadderCommonDensity M/2 := by
  have hc : 0 < gaussianAscendingLadderCommonDensity M :=
    gaussianAscendingLadderCommonDensity_pos M
  have hθ0 : θ ≠ 0 := by
    intro h
    rw [h, abs_zero] at hθ
    linarith
  have hθpos : (0 : ℝ) < |θ| := by linarith
  have hfrac : 2/|θ| ≤ 1/2 := by
    rw [div_le_div_iff₀ hθpos (by norm_num : (0 : ℝ) < 2)]
    linarith
  refine (gaussianAscendingLadderLaw_charFun_le hX hi hG ha haM hθ0).trans ?_
  nlinarith

end SwingRepair
