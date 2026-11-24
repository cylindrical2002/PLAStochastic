import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Tactic

/-!
# The canonical infinite exponential series with Kingman rates

The coordinate laws on Measure.infinitePi are Exp((n+1)(n+2)), indexed from zero.
The nonnegative ENNReal sum is defined before convergence is proved; Tonelli and
the telescoping mean series establish almost-everywhere finiteness. The Laplace
transform is obtained from genuine finite independence and bounded convergence.
This module does not yet define a pure-death process or identify the sum with
a Brownian functional.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
namespace BrownianAffine

/-- Direct integration against the real exponential density. -/
theorem integral_expMeasure_density {r : ℝ} (hr : 0 < r) (f : ℝ → ℝ) :
    (∫ x, f x ∂expMeasure r) = ∫ x in Ioi 0, r * Real.exp (-(r * x)) * f x := by
  unfold expMeasure gammaMeasure gammaPDF
  rw [integral_withDensity_eq_integral_toReal_smul
    ((measurable_gammaPDFReal 1 r).ennreal_ofReal)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (gammaPDFReal_nonneg zero_lt_one hr _), smul_eq_mul]
  rw [← integral_Ici_eq_integral_Ioi, ← integral_indicator measurableSet_Ici]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  by_cases hx : 0 ≤ x
  · simp only [gammaPDFReal, hx, if_true, Real.rpow_one, Real.Gamma_one, div_one,
      sub_self, Real.rpow_zero, mul_one, Set.indicator_of_mem (show x ∈ Ici 0 from hx)]
  · simp only [gammaPDFReal, hx, if_false, zero_mul,
      Set.indicator_of_notMem (show x ∉ Ici 0 from hx)]

/-- The positive exponential density gives the exact first moment. -/
theorem integral_id_expMeasure {r : ℝ} (hr : 0 < r) :
    (∫ x, x ∂expMeasure r) = 1 / r := by
  rw [integral_expMeasure_density hr]
  have heq (x : ℝ) : r * Real.exp (-(r * x)) * x =
      r * (x ^ ((2 : ℝ) - 1) * Real.exp (-(r * x))) := by
    norm_num
    ring
  simp_rw [heq]
  rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num : (0 : ℝ) < 2) hr]
  norm_num [Real.Gamma_add_one]
  field_simp

theorem integrable_id_expMeasure {r : ℝ} (hr : 0 < r) :
    Integrable (fun x : ℝ => x) (expMeasure r) := by
  by_contra h
  have hm := integral_id_expMeasure hr
  rw [integral_undef h] at hm
  exact (ne_of_gt (one_div_pos.mpr hr)) hm.symm

/-- The one-coordinate Laplace transform is calculated from the actual density. -/
theorem integral_laplace_expMeasure {r z : ℝ} (hr : 0 < r) (hz : 0 ≤ z) :
    (∫ x, Real.exp (-(z * x)) ∂expMeasure r) = r / (r + z) := by
  rw [integral_expMeasure_density hr]
  have heq (x : ℝ) : r * Real.exp (-(r * x)) * Real.exp (-(z * x)) =
      r * Real.exp ((-(r + z)) * x) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  simp_rw [heq]
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -(r + z) < 0) 0]
  simp only [mul_zero, Real.exp_zero, neg_div_neg_eq]
  ring

theorem expMeasure_ae_pos {r : ℝ} (hr : 0 < r) : ∀ᵐ x ∂expMeasure r, 0 < x := by
  have : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  have hc : (expMeasure r).real (Iic 0) = 0 := by
    rw [← cdf_eq_real, cdf_expMeasure_eq hr]
    simp
  have hn : expMeasure r (Iic 0) = 0 := (measureReal_eq_zero_iff (measure_ne_top _ _)).mp hc
  rw [ae_iff]
  have heq : {x : ℝ | ¬ 0 < x} = Iic 0 := by ext x; simp
  rw [heq]
  exact hn

/-- Rates indexed from zero: 2,6,12,... . -/
def kingmanRate (n : ℕ) : ℝ := (n + 1) * (n + 2)

theorem kingmanRate_pos (n : ℕ) : 0 < kingmanRate n := by
  unfold kingmanRate
  positivity

theorem sum_kingmanRate_inv (N : ℕ) :
    ∑ n ∈ Finset.range N, 1 / kingmanRate n = 1 - 1 / ((N : ℝ) + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [kingmanRate, Nat.cast_add, Nat.cast_one]
    field_simp
    ring

theorem hasSum_kingmanRate_inv : HasSum (fun n => 1 / kingmanRate n) 1 := by
  have hs : Summable (fun n => 1 / kingmanRate n) := by
    apply summable_of_sum_range_le (c := 1) (fun n => (one_div_pos.mpr (kingmanRate_pos n)).le)
    intro N
    rw [sum_kingmanRate_inv]
    have : 0 ≤ 1 / ((N : ℝ) + 1) := by positivity
    linarith
  apply hs.hasSum_iff_tendsto_nat.mpr
  simp_rw [sum_kingmanRate_inv]
  simpa using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

instance kingmanMarginal_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (expMeasure (kingmanRate n)) :=
  isProbabilityMeasure_expMeasure (kingmanRate_pos n)

/-- The actual canonical probability space is the countable product of the exponential laws. -/
def kingmanMeasure : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun n => expMeasure (kingmanRate n))

instance kingmanMeasure_isProbabilityMeasure : IsProbabilityMeasure kingmanMeasure := by
  unfold kingmanMeasure
  infer_instance

def kingmanIncrement (n : ℕ) (ω : ℕ → ℝ) : ℝ := ω n

theorem kingmanIncrement_measurable (n : ℕ) : Measurable (kingmanIncrement n) :=
  measurable_pi_apply n

theorem kingmanIncrement_hasLaw (n : ℕ) :
    HasLaw (kingmanIncrement n) (expMeasure (kingmanRate n)) kingmanMeasure := by
  refine ⟨(kingmanIncrement_measurable n).aemeasurable, ?_⟩
  exact Measure.infinitePi_map_eval (fun n => expMeasure (kingmanRate n)) n

theorem kingmanIncrement_iIndepFun : iIndepFun kingmanIncrement kingmanMeasure := by
  exact iIndepFun_infinitePi (X := fun _ (x : ℝ) => x) (fun _ => measurable_id)

theorem kingmanIncrement_ae_pos (n : ℕ) :
    ∀ᵐ ω ∂kingmanMeasure, 0 < kingmanIncrement n ω := by
  exact ((kingmanIncrement_hasLaw n).ae_iff (by fun_prop)).mpr
    (expMeasure_ae_pos (kingmanRate_pos n))

theorem integral_kingmanIncrement (n : ℕ) :
    (∫ ω, kingmanIncrement n ω ∂kingmanMeasure) = 1 / kingmanRate n := by
  rw [(kingmanIncrement_hasLaw n).integral_eq, integral_id_expMeasure (kingmanRate_pos n)]

theorem integrable_kingmanIncrement (n : ℕ) : Integrable (kingmanIncrement n) kingmanMeasure := by
  by_contra h
  have hi := integral_kingmanIncrement n
  rw [integral_undef h] at hi
  exact (ne_of_gt (one_div_pos.mpr (kingmanRate_pos n))) hi.symm

theorem lintegral_kingmanIncrement (n : ℕ) :
    (∫⁻ ω, ENNReal.ofReal (kingmanIncrement n ω) ∂kingmanMeasure) =
      ENNReal.ofReal (1 / kingmanRate n) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_kingmanIncrement n)
    ((kingmanIncrement_ae_pos n).mono fun _ h => h.le), integral_kingmanIncrement]

/-- The extended nonnegative sum retains divergence explicitly, before it is ruled out a.e. -/
def kingmanTotal (ω : ℕ → ℝ) : ℝ≥0∞ := ∑' n, ENNReal.ofReal (kingmanIncrement n ω)

theorem kingmanTotal_measurable : Measurable kingmanTotal := by
  exact Measurable.tsum (fun n => (kingmanIncrement_measurable n).ennreal_ofReal)

theorem lintegral_kingmanTotal : (∫⁻ ω, kingmanTotal ω ∂kingmanMeasure) = 1 := by
  unfold kingmanTotal
  rw [lintegral_tsum (fun n => (kingmanIncrement_measurable n).ennreal_ofReal.aemeasurable)]
  simp_rw [lintegral_kingmanIncrement]
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun n => (one_div_pos.mpr (kingmanRate_pos n)).le) hasSum_kingmanRate_inv.summable,
    hasSum_kingmanRate_inv.tsum_eq, ENNReal.ofReal_one]

theorem kingmanTotal_ae_finite : ∀ᵐ ω ∂kingmanMeasure, kingmanTotal ω ≠ ∞ := by
  exact (ae_lt_top kingmanTotal_measurable (by rw [lintegral_kingmanTotal]; simp)).mono
    fun _ h => h.ne

theorem kingmanTotal_ae_pos : ∀ᵐ ω ∂kingmanMeasure, 0 < kingmanTotal ω := by
  filter_upwards [kingmanIncrement_ae_pos 0] with ω hω
  exact (ENNReal.ofReal_pos.mpr hω).trans_le (ENNReal.le_tsum 0)

def kingmanTotalReal (ω : ℕ → ℝ) : ℝ := (kingmanTotal ω).toReal

theorem kingmanTotalReal_integrable : Integrable kingmanTotalReal kingmanMeasure :=
  integrable_toReal_of_lintegral_ne_top kingmanTotal_measurable.aemeasurable
    (by rw [lintegral_kingmanTotal]; simp)

theorem integral_kingmanTotalReal : (∫ ω, kingmanTotalReal ω ∂kingmanMeasure) = 1 := by
  unfold kingmanTotalReal
  rw [integral_toReal kingmanTotal_measurable.aemeasurable
    (kingmanTotal_ae_finite.mono fun _ h => lt_top_iff_ne_top.mpr h), lintegral_kingmanTotal,
    ENNReal.toReal_one]

theorem kingmanTotalReal_ae_pos : ∀ᵐ ω ∂kingmanMeasure, 0 < kingmanTotalReal ω := by
  filter_upwards [kingmanTotal_ae_pos, kingmanTotal_ae_finite] with ω hp hf
  exact ENNReal.toReal_pos hp.ne' hf

/-- The real series converges to the finite representative on the actual canonical space. -/
theorem kingmanIncrement_ae_hasSum :
    ∀ᵐ ω ∂kingmanMeasure, HasSum (fun n => kingmanIncrement n ω) (kingmanTotalReal ω) := by
  filter_upwards [kingmanTotal_ae_finite,
    eventually_countable_forall.mpr kingmanIncrement_ae_pos] with ω hf hpos
  have hs := ENNReal.hasSum_toReal hf
  rw [← ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)] at hs
  simpa only [ENNReal.toReal_ofReal (hpos _).le, kingmanTotalReal, kingmanTotal] using hs

def kingmanPartialSum (N : ℕ) (ω : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, kingmanIncrement n ω

def kingmanLaplaceFactor (z : ℝ) (n : ℕ) : ℝ :=
  kingmanRate n / (kingmanRate n + z)

def kingmanLaplace (z : ℝ) : ℝ :=
  ∫ ω, Real.exp (-(z * kingmanTotalReal ω)) ∂kingmanMeasure

theorem integral_laplace_kingmanIncrement {z : ℝ} (hz : 0 ≤ z) (n : ℕ) :
    (∫ ω, Real.exp (-(z * kingmanIncrement n ω)) ∂kingmanMeasure) =
      kingmanLaplaceFactor z n := by
  have h := (kingmanIncrement_hasLaw n).integral_comp
    (show AEStronglyMeasurable (fun x : ℝ => Real.exp (-(z * x)))
      (expMeasure (kingmanRate n)) by fun_prop)
  simpa only [Function.comp_def, integral_laplace_expMeasure (kingmanRate_pos n) hz,
    kingmanLaplaceFactor] using h

/-- Every finite prefix has the product Laplace transform, derived from full independence. -/
theorem integral_laplace_kingmanPartialSum {z : ℝ} (hz : 0 ≤ z) (N : ℕ) :
    (∫ ω, Real.exp (-(z * kingmanPartialSum N ω)) ∂kingmanMeasure) =
      ∏ n ∈ Finset.range N, kingmanLaplaceFactor z n := by
  have hp (ω : ℕ → ℝ) : Real.exp (-(z * kingmanPartialSum N ω)) =
      ∏ n ∈ Finset.range N, Real.exp (-(z * kingmanIncrement n ω)) := by
    rw [← Real.exp_sum]
    congr 1
    simp only [kingmanPartialSum, Finset.mul_sum, Finset.sum_neg_distrib]
  simp_rw [hp]
  have hind := kingmanIncrement_iIndepFun.restrict (Finset.range N)
  have h := hind.integral_fun_prod_comp
    (f := fun _ (x : ℝ) => Real.exp (-(z * x)))
    (fun n => (kingmanIncrement_measurable n).aemeasurable) (fun _ => by fun_prop)
  calc
    _ = ∫ ω, ∏ n : Finset.range N, Real.exp (-(z * kingmanIncrement n ω)) ∂kingmanMeasure := by
      apply integral_congr_ae
      exact Eventually.of_forall fun ω => (Finset.prod_coe_sort (Finset.range N)
        (fun n => Real.exp (-(z * kingmanIncrement n ω)))).symm
    _ = ∏ n : Finset.range N, ∫ ω, Real.exp (-(z * kingmanIncrement n ω)) ∂kingmanMeasure := h
    _ = _ := by
      rw [Finset.prod_coe_sort (Finset.range N)
        (fun n : ℕ => ∫ ω, Real.exp (-(z * kingmanIncrement n ω)) ∂kingmanMeasure)]
      apply Finset.prod_congr rfl
      intro n _
      exact integral_laplace_kingmanIncrement hz n

/-- Bounded convergence of the actual independent sums yields the finite-product limit. -/
theorem kingmanLaplace_tendsto_finiteProducts {z : ℝ} (hz : 0 ≤ z) :
    Tendsto (fun N => ∏ n ∈ Finset.range N, kingmanLaplaceFactor z n) atTop
      (𝓝 (kingmanLaplace z)) := by
  simp_rw [← integral_laplace_kingmanPartialSum hz]
  apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
  · intro N
    dsimp only [kingmanPartialSum, kingmanIncrement]
    fun_prop
  · exact integrable_const 1
  · intro N
    filter_upwards [eventually_countable_forall.mpr kingmanIncrement_ae_pos] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    apply neg_nonpos.mpr
    exact mul_nonneg hz (Finset.sum_nonneg fun n _ => (hω n).le)
  · filter_upwards [kingmanIncrement_ae_hasSum] with ω hω
    exact Real.continuous_exp.continuousAt.tendsto.comp
      (hω.tendsto_sum_nat.const_mul z).neg

/-- Absolute summability of the deviations from 1 proves the infinite product exists. -/
theorem kingmanLaplaceFactor_multipliable {z : ℝ} (hz : 0 ≤ z) :
    Multipliable (kingmanLaplaceFactor z) := by
  have hbase : Summable (fun n => z / kingmanRate n) := by
    simpa only [div_eq_mul_inv, one_mul] using hasSum_kingmanRate_inv.summable.mul_left z
  have hs : Summable (fun n => z / (kingmanRate n + z)) :=
    hbase.of_nonneg_of_le (fun n => div_nonneg hz (by linarith [kingmanRate_pos n]))
      (fun n => div_le_div_of_nonneg_left hz (kingmanRate_pos n) (by linarith))
  have hp := Real.multipliable_one_add_of_summable hs.neg
  convert hp using 1
  funext n
  dsimp only [kingmanLaplaceFactor, Pi.neg_apply]
  have hden : kingmanRate n + z ≠ 0 := ne_of_gt (by linarith [kingmanRate_pos n])
  field_simp [hden]
  ring

theorem kingmanLaplace_hasProd {z : ℝ} (hz : 0 ≤ z) :
    HasProd (kingmanLaplaceFactor z) (kingmanLaplace z) :=
  (kingmanLaplaceFactor_multipliable hz).hasProd_iff_tendsto_nat.mpr
    (kingmanLaplace_tendsto_finiteProducts hz)

/-- The infinite product is the actual Laplace transform of the canonical exponential sum. -/
theorem kingmanLaplace_eq_tprod {z : ℝ} (hz : 0 ≤ z) :
    kingmanLaplace z = ∏' n, kingmanRate n / (kingmanRate n + z) :=
  (kingmanLaplace_hasProd hz).tprod_eq.symm

theorem kingmanTotalReal_measurable : Measurable kingmanTotalReal :=
  kingmanTotal_measurable.ennreal_toReal

/-- The law of the constructed infinite sum, as an actual pushforward probability measure. -/
def kingmanSumMeasure : Measure ℝ := kingmanMeasure.map kingmanTotalReal

instance kingmanSumMeasure_isProbabilityMeasure : IsProbabilityMeasure kingmanSumMeasure :=
  Measure.isProbabilityMeasure_map kingmanTotalReal_measurable.aemeasurable

theorem kingmanTotalReal_hasLaw : HasLaw kingmanTotalReal kingmanSumMeasure kingmanMeasure :=
  ⟨kingmanTotalReal_measurable.aemeasurable, rfl⟩

theorem integrable_laplace_kingmanTotalReal {z : ℝ} (hz : 0 ≤ z) :
    Integrable (fun ω => Real.exp (-(z * kingmanTotalReal ω))) kingmanMeasure := by
  apply (integrable_const (1 : ℝ)).mono'
  · have hm := kingmanTotalReal_measurable
    fun_prop
  · apply Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hz ENNReal.toReal_nonneg))

theorem kingmanLaplace_pos {z : ℝ} (hz : 0 ≤ z) : 0 < kingmanLaplace z :=
  integral_exp_pos (integrable_laplace_kingmanTotalReal hz)

theorem kingmanLaplace_zero : kingmanLaplace 0 = 1 := by
  simp [kingmanLaplace]

end BrownianAffine
