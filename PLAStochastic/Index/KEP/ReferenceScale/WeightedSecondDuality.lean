import PLAStochastic.Index.KEP.ReferenceScale.GammaFourthRegularity
import PLAStochastic.Index.KEP.ReferenceScale.ActualBoundedConeTransfer
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Reading an actual weighted L1 norm from bounded C2 weak tests

A growing compact bump and a smooth sign approximation test the genuine second
density. Their product converges pointwise to its weighted absolute value and
is dominated by that same integrable value. Thus the weak budget controls the
actual norm, with no distributional regularity or duality premise left unpaid.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

def kepDualityBump (n : ℕ) : ContDiffBump (0 : ℝ) :=
  ⟨(n : ℝ) + 1, 2 * ((n : ℝ) + 1), by positivity, by nlinarith [Nat.cast_nonneg (α := ℝ) n]⟩

def kepWeightedSignTest (theta : ℝ) (g : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp (theta * x) * (g x / Real.sqrt ((g x) ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2)) *
    kepDualityBump n x

theorem kepWeightedSignTest_C2 {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (theta : ℝ) (n : ℕ) :
    ContDiff ℝ 2 (kepWeightedSignTest theta g n) := by
  have hden : ContDiff ℝ 2 (fun x => Real.sqrt ((g x) ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2)) :=
    (hg.pow 2 |>.add contDiff_const).sqrt (fun x => by positivity)
  have hbc : ContDiff ℝ 2 (kepDualityBump n) := (kepDualityBump n).contDiff
  exact ((Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).mul
    (hg.div hden (fun x => Real.sqrt_ne_zero'.mpr (by positivity)))).mul
      hbc

theorem kepWeightedSignTest_compact (theta : ℝ) (g : ℝ → ℝ) (n : ℕ) :
    HasCompactSupport (kepWeightedSignTest theta g n) :=
  (kepDualityBump n).hasCompactSupport.mul_left

theorem kepWeightedSignTest_bound (theta : ℝ) (g : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    |kepWeightedSignTest theta g n x| ≤ Real.exp (theta * x) := by
  have hden : 0 < Real.sqrt ((g x) ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2) :=
    Real.sqrt_pos.mpr (by positivity)
  have hsign : |g x / Real.sqrt ((g x) ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2)| ≤ 1 := by
    rw [abs_div, abs_of_pos hden, div_le_one hden]
    exact Real.abs_le_sqrt (by nlinarith only [sq_nonneg (1 / ((n : ℝ) + 1))])
  have hbump : |kepDualityBump n x| ≤ 1 := by
    rw [abs_of_nonneg (kepDualityBump n).nonneg]
    exact (kepDualityBump n).le_one
  unfold kepWeightedSignTest
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (theta * x) * 1 * 1 := by gcongr
    _ = _ := by ring

theorem kepWeightedSignTest_limit (theta : ℝ) (g : ℝ → ℝ) (x : ℝ) :
    Tendsto (fun n : ℕ => kepWeightedSignTest theta g n x * g x) atTop
      (𝓝 (Real.exp (theta * x) * |g x|)) := by
  have hbump : Tendsto (fun n : ℕ => kepDualityBump n x) atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop ⌈|x|⌉₊] with n hn
    symm
    apply (kepDualityBump n).one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    have h1 : |x| ≤ (⌈|x|⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈|x|⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
    change |x| ≤ (n : ℝ) + 1
    linarith
  by_cases hg0 : g x = 0
  · simpa only [hg0, mul_zero, abs_zero] using (tendsto_const_nhds (x := (0 : ℝ)))
  have hdelta : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hden : Tendsto (fun n : ℕ => Real.sqrt ((g x) ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2))
      atTop (𝓝 |g x|) := by
    have ht := ((tendsto_const_nhds (x := (g x) ^ 2)).add (hdelta.pow 2)).sqrt
    norm_num only [zero_pow, add_zero] at ht
    rw [Real.sqrt_sq_eq_abs] at ht
    exact ht
  have hquot := (tendsto_const_nhds (x := g x)).div hden (abs_ne_zero.mpr hg0)
  have hh := (((tendsto_const_nhds (x := Real.exp (theta * x))).mul hquot).mul hbump).mul
    (tendsto_const_nhds (x := g x))
  have hsq : g x * g x = |g x| * |g x| := by rw [← sq, ← sq, sq_abs]
  have he : g x / |g x| * g x = |g x| := by
    calc
      _ = (g x * g x) / |g x| := by ring
      _ = _ := by rw [hsq, mul_div_cancel_right₀ _ (abs_ne_zero.mpr hg0)]
  rw [mul_one, mul_assoc, he] at hh
  exact hh

theorem kep_weighted_second_norm_le_of_C2_tests {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (theta K : ℝ) (hgi : Integrable (fun x => Real.exp (theta * x) * |g x|))
    (hbudget : ∀ phi : ℝ → ℝ, ContDiff ℝ 2 phi → HasCompactSupport phi →
      (∀ x, |phi x| ≤ Real.exp (theta * x)) → |∫ x, phi x * g x| ≤ K) :
    (∫ x, Real.exp (theta * x) * |g x|) ≤ K := by
  have hh := tendsto_integral_of_dominated_convergence
    (fun x => Real.exp (theta * x) * |g x|)
    (fun n => ((kepWeightedSignTest_C2 hg theta n).continuous.mul hg.continuous).aestronglyMeasurable)
    hgi
    (fun n => ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
      exact mul_le_mul_of_nonneg_right (kepWeightedSignTest_bound theta g n x) (abs_nonneg _))
    (ae_of_all _ fun x => kepWeightedSignTest_limit theta g x)
  apply le_of_tendsto hh
  exact Eventually.of_forall fun n => (le_abs_self _).trans
    (hbudget _ (kepWeightedSignTest_C2 hg theta n) (kepWeightedSignTest_compact theta g n)
      (kepWeightedSignTest_bound theta g n))

end

end PGM
