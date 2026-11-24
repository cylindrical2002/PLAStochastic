import PLAStochastic.Swing.Ladder.Law.CompactMoments
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Measure.Sub

/-! # The ladder renewal measure of a parameterised inter-arrival law

The renewal measure of an inter-arrival law `ν` on `[0,∞)` is
`U = ∑_{n≥0} ν^{*n}`.  This file records the convolution powers, the renewal
measure, and the quantitative estimate used later: an inter-arrival law with a
Laplace transform bounded away from one at `-1` has a renewal measure that is
finite on every bounded interval, with a bound depending only on that
transform.  Nothing here assumes a renewal theorem.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical MeasureTheory
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- The `n`-fold additive convolution power of an inter-arrival law. -/
noncomputable def measureConvPow (ν : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | (n+1) => (measureConvPow ν n) ∗ ν

@[simp] theorem measureConvPow_zero (ν : Measure ℝ) :
    measureConvPow ν 0 = Measure.dirac 0 := rfl

@[simp] theorem measureConvPow_succ (ν : Measure ℝ) (n : ℕ) :
    measureConvPow ν (n+1) = (measureConvPow ν n) ∗ ν := rfl

instance measureConvPow_sfinite (ν : Measure ℝ) [SFinite ν] :
    ∀ n, SFinite (measureConvPow ν n)
  | 0 => by rw [measureConvPow_zero]; infer_instance
  | (n+1) => by
      have h := measureConvPow_sfinite ν n
      rw [measureConvPow_succ]
      infer_instance

instance measureConvPow_isProbabilityMeasure (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    ∀ n, IsProbabilityMeasure (measureConvPow ν n)
  | 0 => by rw [measureConvPow_zero]; infer_instance
  | (n+1) => by
      have h := measureConvPow_isProbabilityMeasure ν n
      rw [measureConvPow_succ]
      infer_instance

/-- The renewal measure of the inter-arrival law `ν`. -/
noncomputable def ladderRenewalMeasure (ν : Measure ℝ) : Measure ℝ :=
  Measure.sum (measureConvPow ν)

theorem ladderRenewalMeasure_apply (ν : Measure ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    ladderRenewalMeasure ν A = ∑' n : ℕ, measureConvPow ν n A := by
  rw [ladderRenewalMeasure, Measure.sum_apply _ hA]

/-! ### The Laplace transform -/

/-- `∫ e^{-λx} dν` in `ℝ≥0∞`. -/
noncomputable def ladderLaplace (ν : Measure ℝ) (lam : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (Real.exp (-lam*x)) ∂ν

theorem measurable_expNeg (lam : ℝ) :
    Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (-lam*x))) :=
  ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul measurable_id))

theorem lintegral_measureConvPow_expNeg (ν : Measure ℝ) [SFinite ν] (lam : ℝ) (n : ℕ) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (-lam*x)) ∂measureConvPow ν n) = (ladderLaplace ν lam)^n := by
  induction n with
  | zero => simp [measureConvPow_zero]
  | succ n ih =>
    rw [measureConvPow_succ, Measure.lintegral_conv (measurable_expNeg lam)]
    have hinner : ∀ x : ℝ, (∫⁻ y, ENNReal.ofReal (Real.exp (-lam*(x+y))) ∂ν) =
        ENNReal.ofReal (Real.exp (-lam*x)) * ladderLaplace ν lam := by
      intro x
      rw [ladderLaplace, ← lintegral_const_mul _ (measurable_expNeg lam)]
      refine lintegral_congr fun y => ?_
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      congr 1
      ring_nf
    rw [lintegral_congr hinner, lintegral_mul_const _ (measurable_expNeg lam), ih, pow_succ]

/-! ### Uniform finiteness of the renewal measure on bounded intervals -/

theorem measureConvPow_Icc_le (ν : Measure ℝ) [SFinite ν] {b lam : ℝ} (hlam : 0 ≤ lam)
    (n : ℕ) :
    measureConvPow ν n (Icc 0 b) ≤
      ENNReal.ofReal (Real.exp (lam*b)) * (ladderLaplace ν lam)^n := by
  have hpoint : ∀ x : ℝ, (Icc (0 : ℝ) b).indicator (fun _ => (1 : ℝ≥0∞)) x ≤
      ENNReal.ofReal (Real.exp (lam*b)) * ENNReal.ofReal (Real.exp (-lam*x)) := by
    intro x
    by_cases hx : x ∈ Icc (0 : ℝ) b
    · rw [Set.indicator_of_mem hx, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      refine ENNReal.one_le_ofReal.mpr ?_
      refine Real.one_le_exp ?_
      nlinarith [hx.2]
    · rw [Set.indicator_of_notMem hx]
      exact zero_le
  calc
    measureConvPow ν n (Icc 0 b)
        = ∫⁻ x, (Icc (0 : ℝ) b).indicator (fun _ => (1 : ℝ≥0∞)) x ∂measureConvPow ν n := by
      rw [lintegral_indicator measurableSet_Icc]
      simp
    _ ≤ ∫⁻ x, ENNReal.ofReal (Real.exp (lam*b)) * ENNReal.ofReal (Real.exp (-lam*x))
          ∂measureConvPow ν n := lintegral_mono hpoint
    _ = ENNReal.ofReal (Real.exp (lam*b)) * (ladderLaplace ν lam)^n := by
      rw [lintegral_const_mul _ (measurable_expNeg lam), lintegral_measureConvPow_expNeg]

/-- The renewal measure is finite on every bounded interval, with an explicit
bound depending only on one Laplace transform value. -/
theorem ladderRenewalMeasure_Icc_le (ν : Measure ℝ) [SFinite ν] {b lam q : ℝ}
    (hlam : 0 ≤ lam) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hq : ladderLaplace ν lam ≤ ENNReal.ofReal q) :
    ladderRenewalMeasure ν (Icc 0 b) ≤
      ENNReal.ofReal (Real.exp (lam*b) / (1-q)) := by
  have hq1' : 0 < 1-q := by linarith
  calc
    ladderRenewalMeasure ν (Icc 0 b) = ∑' n : ℕ, measureConvPow ν n (Icc 0 b) :=
      ladderRenewalMeasure_apply ν measurableSet_Icc
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (Real.exp (lam*b)) * (ladderLaplace ν lam)^n :=
      ENNReal.tsum_le_tsum fun n => measureConvPow_Icc_le ν hlam n
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (Real.exp (lam*b)) * (ENNReal.ofReal q)^n := by
      refine ENNReal.tsum_le_tsum fun n => ?_
      exact mul_le_mul' le_rfl (pow_le_pow_left' hq n)
    _ = ENNReal.ofReal (Real.exp (lam*b)) * ∑' n : ℕ, (ENNReal.ofReal q)^n := ENNReal.tsum_mul_left
    _ = ENNReal.ofReal (Real.exp (lam*b)) * (1-ENNReal.ofReal q)⁻¹ := by
      rw [ENNReal.tsum_geometric]
    _ = ENNReal.ofReal (Real.exp (lam*b) / (1-q)) := by
      rw [ENNReal.ofReal_div_of_pos hq1', ENNReal.ofReal_sub _ hq0, ENNReal.ofReal_one,
        ENNReal.div_eq_inv_mul, mul_comm]

end SwingRepair
