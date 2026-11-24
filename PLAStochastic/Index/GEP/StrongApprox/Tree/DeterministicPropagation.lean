import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# WP5: deterministic propagation on a dyadic coupling tree

An error at a child equals half its parent's error plus a local quantile
defect. Conservation of the two children's totals then controls every partial
sum of the leaves by the depth times a uniform node bound.
-/

namespace PGM

open Finset

/-- Halving at each split prevents node errors from accumulating with depth. -/
theorem sa_dyadic_node_bound {e : ℕ → ℕ → ℝ} {J : ℕ} {R D : ℝ}
    (hR : 0 ≤ R) (hD : 0 ≤ D) (hroot : |e 0 0| ≤ R)
    (hstep : ∀ j < J, ∀ i < 2 ^ (j + 1),
      |e (j + 1) i - e j (i / 2) / 2| ≤ D) :
    ∀ j ≤ J, ∀ i < 2 ^ j, |e j i| ≤ R + 2 * D := by
  intro j hj
  induction j with
  | zero =>
      intro i hi
      have : i = 0 := by simpa using hi
      subst i
      exact hroot.trans (by linarith)
  | succ j ih =>
      intro i hi
      have hjJ : j < J := by omega
      have hi' : i / 2 < 2 ^ j := by
        rw [pow_succ] at hi
        omega
      have hp := ih (by omega) (i / 2) hi'
      calc
        |e (j + 1) i| = |(e (j + 1) i - e j (i / 2) / 2) + e j (i / 2) / 2| := by
          congr 1
          ring
        _ ≤ |e (j + 1) i - e j (i / 2) / 2| + |e j (i / 2) / 2| := abs_add_le _ _
        _ ≤ D + (R + 2 * D) / 2 := by
          rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          exact add_le_add (hstep j hjJ i hi) (div_le_div_of_nonneg_right hp (by norm_num))
        _ ≤ R + 2 * D := by linarith

/-- Splitting a finite sum into adjacent pairs. -/
theorem sa_sum_range_pairs (f : ℕ → ℝ) (k : ℕ) :
    ∑ i ∈ range (2 * k), f i = ∑ i ∈ range k, (f (2 * i) + f (2 * i + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
        sum_range_succ, sum_range_succ, ih, sum_range_succ]
      ring

/-- Prefix sums at the next level reduce to a parent prefix and at most one child. -/
theorem sa_dyadic_prefix_even {e : ℕ → ℕ → ℝ} {j k : ℕ}
    (hcon : ∀ i < k, e (j + 1) (2 * i) + e (j + 1) (2 * i + 1) = e j i) :
    ∑ i ∈ range (2 * k), e (j + 1) i = ∑ i ∈ range k, e j i := by
  rw [sa_sum_range_pairs]
  apply sum_congr rfl
  intro i hi
  exact hcon i (mem_range.mp hi)

/-- Every leaf prefix uses at most one node per level. -/
theorem sa_dyadic_prefix_bound {e : ℕ → ℕ → ℝ} {J : ℕ} {C : ℝ}
    (hC : 0 ≤ C)
    (hcon : ∀ j < J, ∀ i < 2 ^ j,
      e (j + 1) (2 * i) + e (j + 1) (2 * i + 1) = e j i)
    (hnode : ∀ j ≤ J, ∀ i < 2 ^ j, |e j i| ≤ C) :
    ∀ j ≤ J, ∀ k ≤ 2 ^ j, |∑ i ∈ range k, e j i| ≤ ((j : ℝ) + 1) * C := by
  intro j hj
  induction j with
  | zero =>
      intro k hk
      have hk' : k = 0 ∨ k = 1 := by simpa using (Nat.le_one_iff_eq_zero_or_eq_one.mp hk)
      rcases hk' with rfl | rfl
      · simpa using hC
      · simpa using hnode 0 (by omega) 0 (by norm_num)
  | succ j ih =>
      intro k hk
      have hjJ : j < J := by omega
      have hhalf : k / 2 ≤ 2 ^ j := by
        rw [pow_succ] at hk
        omega
      have heven := sa_dyadic_prefix_even (j := j) (k := k / 2)
        (fun i hi => hcon j hjJ i (hi.trans_le hhalf))
      have hp := ih (by omega) (k / 2) hhalf
      have hmod : k % 2 = 0 ∨ k % 2 = 1 := by omega
      rcases hmod with hm | hm
      · have hkE : k = 2 * (k / 2) := by omega
        rw [hkE, heven]
        exact hp.trans (by push_cast; nlinarith)
      · have hkO : k = 2 * (k / 2) + 1 := by omega
        have hklt : 2 * (k / 2) < 2 ^ (j + 1) := by omega
        rw [hkO, sum_range_succ, heven]
        calc
          _ ≤ |∑ i ∈ range (k / 2), e j i| + |e (j + 1) (2 * (k / 2))| := abs_add_le _ _
          _ ≤ ((j : ℝ) + 1) * C + C := add_le_add hp (hnode (j + 1) hj _ hklt)
          _ = _ := by push_cast; ring

/-- The deterministic endpoint estimate consumed by the strong approximation. -/
theorem sa_dyadic_coupling_error {s w : ℕ → ℕ → ℝ} {J : ℕ} {R D : ℝ}
    (hR : 0 ≤ R) (hD : 0 ≤ D) (hroot : |s 0 0 - w 0 0| ≤ R)
    (hs : ∀ j < J, ∀ i < 2 ^ j,
      s (j + 1) (2 * i) + s (j + 1) (2 * i + 1) = s j i)
    (hw : ∀ j < J, ∀ i < 2 ^ j,
      w (j + 1) (2 * i) + w (j + 1) (2 * i + 1) = w j i)
    (hstep : ∀ j < J, ∀ i < 2 ^ (j + 1),
      |(s (j + 1) i - w (j + 1) i) - (s j (i / 2) - w j (i / 2)) / 2| ≤ D) :
    ∀ k ≤ 2 ^ J,
      |(∑ i ∈ range k, s J i) - ∑ i ∈ range k, w J i| ≤
        ((J : ℝ) + 1) * (R + 2 * D) := by
  have hn := sa_dyadic_node_bound (e := fun j i => s j i - w j i) hR hD hroot hstep
  have hc : ∀ j < J, ∀ i < 2 ^ j,
      (s (j + 1) (2 * i) - w (j + 1) (2 * i)) +
        (s (j + 1) (2 * i + 1) - w (j + 1) (2 * i + 1)) = s j i - w j i := by
    intro j hj i hi
    linarith [hs j hj i hi, hw j hj i hi]
  intro k hk
  simpa only [sum_sub_distrib] using
    sa_dyadic_prefix_bound (by positivity : 0 ≤ R + 2 * D) hc hn J le_rfl k hk

end PGM
