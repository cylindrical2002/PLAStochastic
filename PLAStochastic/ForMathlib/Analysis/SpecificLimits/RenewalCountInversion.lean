import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/-!
# Deterministic inversion of renewal sums

Positive integer cycle spans make the completed-cycle count a total, finite
inverse of their partial sums. Convergence of the average span to a positive
number implies the reciprocal count rate. A uniformly bounded terminal remainder
then gives the two-segments-per-cycle rate used by the repair renewal argument.
-/

open Filter Finset
open scoped Topology

namespace SwingRepair

/-- Total span of the first `n` cycles. -/
def cycleSum (L : ℕ → ℕ) (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, L i

/-- Number of fully completed cycles through sample `N`. Positivity ensures the
search bound `N` contains every admissible cycle index. -/
def completedCount (L : ℕ → ℕ) (N : ℕ) : ℕ :=
  Nat.findGreatest (fun n => cycleSum L n ≤ N) N

@[simp] theorem cycleSum_zero (L : ℕ → ℕ) : cycleSum L 0 = 0 := by
  simp [cycleSum]

@[simp] theorem cycleSum_succ (L : ℕ → ℕ) (n : ℕ) :
    cycleSum L (n + 1) = cycleSum L n + L n := by
  simp [cycleSum, Finset.sum_range_succ]

theorem cycleSum_strictMono {L : ℕ → ℕ} (hpos : ∀ n, 0 < L n) :
    StrictMono (cycleSum L) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [cycleSum_succ]
  exact Nat.lt_add_of_pos_right (hpos n)

theorem le_cycleSum {L : ℕ → ℕ} (hpos : ∀ n, 0 < L n) (n : ℕ) :
    n ≤ cycleSum L n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [cycleSum_succ]
    have := hpos n
    omega

theorem completedCount_le (L : ℕ → ℕ) (N : ℕ) : completedCount L N ≤ N :=
  Nat.findGreatest_le N

theorem cycleSum_completedCount_le (L : ℕ → ℕ) (N : ℕ) :
    cycleSum L (completedCount L N) ≤ N := by
  exact Nat.findGreatest_spec (P := fun n => cycleSum L n ≤ N) (Nat.zero_le N) (by simp)

theorem le_completedCount {L : ℕ → ℕ} (hpos : ∀ n, 0 < L n)
    {n N : ℕ} (hn : cycleSum L n ≤ N) : n ≤ completedCount L N :=
  Nat.le_findGreatest ((le_cycleSum hpos n).trans hn) hn

/-- The completed count is exactly the order inverse of the increasing cycle sums. -/
theorem le_completedCount_iff {L : ℕ → ℕ} (hpos : ∀ n, 0 < L n) (n N : ℕ) :
    n ≤ completedCount L N ↔ cycleSum L n ≤ N :=
  ⟨fun hn => ((cycleSum_strictMono hpos).monotone hn).trans
    (cycleSum_completedCount_le L N), le_completedCount hpos⟩

theorem lt_cycleSum_completedCount_succ {L : ℕ → ℕ} (hpos : ∀ n, 0 < L n) (N : ℕ) :
    N < cycleSum L (completedCount L N + 1) := by
  by_contra h
  have := le_completedCount hpos (Nat.le_of_not_gt h)
  omega

theorem completedCount_mono {L : ℕ → ℕ} (hpos : ∀ n, 0 < L n) :
    Monotone (completedCount L) := by
  intro N M hNM
  exact le_completedCount hpos ((cycleSum_completedCount_le L N).trans hNM)

/-- Every fixed cycle is eventually completed, independently of any average-limit assumption. -/
theorem tendsto_completedCount_atTop {L : ℕ → ℕ} (hpos : ∀ n, 0 < L n) :
    Tendsto (completedCount L) atTop atTop := by
  apply tendsto_atTop.mpr
  intro n
  filter_upwards [eventually_ge_atTop (cycleSum L n)] with N hN
  exact le_completedCount hpos hN

/-- Advancing the sum index by one leaves its average-span limit unchanged. -/
theorem tendsto_cycleSum_succ_div {L : ℕ → ℕ} {m : ℝ}
    (havg : Tendsto (fun n : ℕ => (cycleSum L n : ℝ) / (n : ℝ)) atTop (𝓝 m)) :
    Tendsto (fun n : ℕ => (cycleSum L (n + 1) : ℝ) / (n : ℝ)) atTop (𝓝 m) := by
  have hs := havg.comp (tendsto_add_atTop_nat 1)
  have hr : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / (n : ℝ)) atTop (𝓝 1) := by
    simpa only [one_mul, zero_add, add_zero, div_one, add_comm] using
      tendsto_add_mul_div_add_mul_atTop_nhds (1 : ℝ) 0 1 (d := 1) one_ne_zero
  have h := hs.mul hr
  simp only [mul_one] at h
  apply h.congr'
  exact Eventually.of_forall fun n => by
    dsimp only [Function.comp_def]
    push_cast
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp

/-- Inverting the completed-cycle count gives the original average-span limit. -/
theorem tendsto_sample_div_completedCount {L : ℕ → ℕ} (hpos : ∀ n, 0 < L n) {m : ℝ}
    (havg : Tendsto (fun n : ℕ => (cycleSum L n : ℝ) / (n : ℝ)) atTop (𝓝 m)) :
    Tendsto (fun N : ℕ => (N : ℝ) / (completedCount L N : ℝ)) atTop (𝓝 m) := by
  have hC := tendsto_completedCount_atTop hpos
  have hlo := havg.comp hC
  have hhi := (tendsto_cycleSum_succ_div havg).comp hC
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
  · intro N
    have hb : (cycleSum L (completedCount L N) : ℝ) ≤ (N : ℝ) :=
      Nat.cast_le.mpr (cycleSum_completedCount_le L N)
    simpa only [Function.comp_def] using! div_le_div_of_nonneg_right hb
      (Nat.cast_nonneg (completedCount L N) : (0 : ℝ) ≤ completedCount L N)
  · intro N
    have hb : (N : ℝ) ≤ (cycleSum L (completedCount L N + 1) : ℝ) :=
      Nat.cast_le.mpr (lt_cycleSum_completedCount_succ hpos N).le
    simpa only [Function.comp_def] using! div_le_div_of_nonneg_right hb
      (Nat.cast_nonneg (completedCount L N) : (0 : ℝ) ≤ completedCount L N)

/-- Deterministic renewal inversion: completed cycles per sample tend to the reciprocal mean. -/
theorem tendsto_completedCount_div {L : ℕ → ℕ} (hpos : ∀ n, 0 < L n) {m : ℝ}
    (hm : 0 < m)
    (havg : Tendsto (fun n : ℕ => (cycleSum L n : ℝ) / (n : ℝ)) atTop (𝓝 m)) :
    Tendsto (fun N : ℕ => (completedCount L N : ℝ) / (N : ℝ)) atTop (𝓝 (1 / m)) := by
  simpa only [inv_div, one_div] using
    (tendsto_sample_div_completedCount hpos havg).inv₀ hm.ne'

/-- A remainder of absolute size at most one vanishes after division by sample count. -/
theorem tendsto_remainder_div_zero {R : ℕ → ℝ} (hR : ∀ N, |R N| ≤ 1) :
    Tendsto (fun N : ℕ => R N / (N : ℝ)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_div_atTop_nhds_zero_nat (-1 : ℝ))
    (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  · intro N
    exact div_le_div_of_nonneg_right (abs_le.mp (hR N)).1 (Nat.cast_nonneg _)
  · intro N
    exact div_le_div_of_nonneg_right (abs_le.mp (hR N)).2 (Nat.cast_nonneg _)

/-- Two segments per completed cycle and a bounded terminal remainder give the rate `2 / m`. -/
theorem tendsto_segmentCount_div_of_abs {L : ℕ → ℕ} (hpos : ∀ n, 0 < L n) {m : ℝ}
    (hm : 0 < m)
    (havg : Tendsto (fun n : ℕ => (cycleSum L n : ℝ) / (n : ℝ)) atTop (𝓝 m))
    {M : ℕ → ℝ} (hM : ∀ N, |M N - 2 * (completedCount L N : ℝ)| ≤ 1) :
    Tendsto (fun N : ℕ => M N / (N : ℝ)) atTop (𝓝 (2 / m)) := by
  have hc := (tendsto_completedCount_div hpos hm havg).const_mul 2
  have hr := tendsto_remainder_div_zero hM
  have h := hc.add hr
  simp only [add_zero, mul_one_div] at h
  apply h.congr'
  exact Eventually.of_forall fun N => by dsimp; ring

/-- Natural-valued output counts may instead use the algorithm's two one-sided bounds. -/
theorem tendsto_segmentCount_div {L : ℕ → ℕ} (hpos : ∀ n, 0 < L n) {m : ℝ}
    (hm : 0 < m)
    (havg : Tendsto (fun n : ℕ => (cycleSum L n : ℝ) / (n : ℝ)) atTop (𝓝 m))
    {M : ℕ → ℕ} (hM : ∀ N, 2 * completedCount L N ≤ M N ∧
      M N ≤ 2 * completedCount L N + 1) :
    Tendsto (fun N : ℕ => (M N : ℝ) / (N : ℝ)) atTop (𝓝 (2 / m)) := by
  apply tendsto_segmentCount_div_of_abs hpos hm havg
  intro N
  have hlo : 2 * (completedCount L N : ℝ) ≤ (M N : ℝ) := by exact_mod_cast (hM N).1
  have hhi : (M N : ℝ) ≤ 2 * (completedCount L N : ℝ) + 1 := by exact_mod_cast (hM N).2
  rw [abs_le]
  constructor <;> linarith

end SwingRepair
