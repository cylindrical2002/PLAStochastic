import PLAStochastic.ForMathlib.Probability.KingmanSum.Coefficients
import PLAStochastic.ForMathlib.Analysis.SpecialFunctions.WedgeSeries.SumCDFSeries
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The limit of the exact finite exponential-sum CDF expansions

The factorial coefficient bound supplies a single summable majorant for every
finite expansion. No interchange at the singular endpoint zero is used.
-/
noncomputable section
open Filter Finset
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

private theorem summable_kingmanCDFBound {s : ℝ} (hs : 0 < s) :
    Summable (fun n : ℕ => (2 * ((n : ℝ) + 1) + 1) * Real.exp (-(n : ℝ) * s)) := by
  have h₁ := (Real.summable_pow_mul_exp_neg_nat_mul 1 hs).mul_left 2
  have h₀ := (Real.summable_pow_mul_exp_neg_nat_mul 0 hs).mul_left 3
  convert! h₁.add h₀ using 1
  funext n
  simp only [pow_one, pow_zero, one_mul, neg_mul]
  ring_nf

/-- A summable bound uniform in the number of independent holding times. -/
theorem kingmanCDFMode_bound (N n : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    ‖kingmanCDFCoeff N n * Real.exp (-(kingmanRate n * s))‖ ≤
      (2 * ((n : ℝ) + 1) + 1) * Real.exp (-(n : ℝ) * s) := by
  rw [norm_mul, Real.norm_eq_abs (Real.exp (-(kingmanRate n * s))), abs_of_pos (Real.exp_pos _)]
  have he : Real.exp (-(kingmanRate n * s)) ≤ Real.exp (-(n : ℝ) * s) := by
    apply Real.exp_le_exp.mpr
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hr : (n : ℝ) ≤ kingmanRate n := by unfold kingmanRate; nlinarith [sq_nonneg (n : ℝ)]
    nlinarith [mul_le_mul_of_nonneg_right hr hs]
  exact mul_le_mul (kingmanCDFCoeff_bound N n) he (Real.exp_nonneg _)
    (by positivity)

/-- The finite expansions converge to the same spectral series as the Brownian sum. -/
theorem kingmanCDFExpansion_tendsto {s : ℝ} (hs : 0 < s) :
    Tendsto (fun N : ℕ => 1 + ∑ n ∈ range N,
      kingmanCDFCoeff N n * Real.exp (-(kingmanRate n * s))) atTop
      (𝓝 (sumCDFSeries s)) := by
  have heq (N : ℕ) : (∑' n, kingmanCDFCoeff N n * Real.exp (-(kingmanRate n * s))) =
      ∑ n ∈ range N, kingmanCDFCoeff N n * Real.exp (-(kingmanRate n * s)) := by
    apply tsum_eq_sum
    intro n hn
    rw [kingmanCDFCoeff_eq_zero (by simpa only [mem_range, not_lt] using hn), zero_mul]
  have ht := tendsto_tsum_of_dominated_convergence (summable_kingmanCDFBound hs)
    (fun n => (tendsto_kingmanCDFCoeff n).mul_const (Real.exp (-(kingmanRate n * s))))
    (Eventually.of_forall fun N n => kingmanCDFMode_bound N n hs.le)
  simp only [heq] at ht
  have hh := ht.const_add 1
  simpa only [sumCDFSeries, kingmanRate, neg_mul, mul_assoc] using hh

end BrownianAffine
