import PLAStochastic.ForMathlib.Probability.KingmanSum.Convolution
import PLAStochastic.ForMathlib.Probability.KingmanSum.Coefficients

/-! Exact CDF of the canonical finite sum of independent exponentials. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace BrownianAffine

/-- The finite hypoexponential formula, derived from actual independent coordinates and convolution. -/
theorem kingmanPartialCDF_formula (N : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    kingmanPartialCDF N s =
      1 + ∑ n ∈ Finset.range N,
        kingmanCDFCoeff N n * Real.exp (-(kingmanRate n * s)) := by
  induction N generalizing s with
  | zero =>
      simpa only [Finset.range_zero, Finset.sum_empty, add_zero] using
        kingmanPartialCDF_zero hs
  | succ N ih =>
      rw [kingmanPartialCDF_succ_of_modes N (kingmanCDFCoeff N) (fun t ht => ih ht) hs]
      have hnorm := kingmanCDFCoeff_sum N
      rw [Finset.sum_range_succ] at hnorm
      have hsum :
          (∑ n ∈ Finset.range N,
            (kingmanCDFCoeff N n * kingmanRate N / (kingmanRate N - kingmanRate n)) *
              (Real.exp (-(kingmanRate n * s)) - Real.exp (-(kingmanRate N * s)))) =
          (∑ n ∈ Finset.range N,
            kingmanCDFCoeff (N + 1) n * Real.exp (-(kingmanRate n * s))) -
          (∑ n ∈ Finset.range N, kingmanCDFCoeff (N + 1) n) *
            Real.exp (-(kingmanRate N * s)) := by
        calc
          _ = ∑ n ∈ Finset.range N, kingmanCDFCoeff (N + 1) n *
              (Real.exp (-(kingmanRate n * s)) - Real.exp (-(kingmanRate N * s))) := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [kingmanCDFCoeff_succ (Finset.mem_range.mp hn)]
          _ = _ := by
            simp_rw [mul_sub]
            rw [Finset.sum_sub_distrib, Finset.sum_mul]
      rw [hsum, Finset.sum_range_succ]
      have hlast : kingmanCDFCoeff (N + 1) N =
          -1 - ∑ n ∈ Finset.range N, kingmanCDFCoeff (N + 1) n := by linarith
      rw [hlast]
      ring

end BrownianAffine
