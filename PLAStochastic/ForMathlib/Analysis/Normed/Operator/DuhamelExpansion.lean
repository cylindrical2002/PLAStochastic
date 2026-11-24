import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

/-!
# Noncommutative Duhamel expansion for a killed operator

The formula keeps every interval projection in the powers of `Q` and `R`.
It applies to continuous linear endomorphisms and does not assume the low- and
high-frequency pieces commute. This is the algebraic identity in §4 of
`research/2026-09-28-gep-closure/kernel-bv.md`.
-/

namespace PGM
open scoped BigOperators

/-- Duhamel's formula in an arbitrary semiring, with no commutation assumption. -/
theorem kBV_duhamel {A : Type*} [Semiring A] (Q S R : A) (hQ : Q = S + R) (n : ℕ) :
    Q ^ n = R ^ n + ∑ j ∈ Finset.range n, Q ^ (n - 1 - j) * S * R ^ j := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsum : (∑ j ∈ Finset.range n, Q ^ (n - 1 - j) * S * R ^ j) * R =
        ∑ j ∈ Finset.range n, Q ^ (n + 1 - 1 - (j + 1)) * S * R ^ (j + 1) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      have heq : n + 1 - 1 - (j + 1) = n - 1 - j := by omega
      rw [heq, pow_succ]
      simp only [mul_assoc]
    calc Q ^ (n + 1) = Q ^ n * S + Q ^ n * R := by
          rw [pow_succ, hQ, mul_add]
      _ = Q ^ n * S + (R ^ n + ∑ j ∈ Finset.range n, Q ^ (n - 1 - j) * S * R ^ j) * R := by rw [← ih]
      _ = R ^ (n + 1) + ∑ j ∈ Finset.range (n + 1), Q ^ (n + 1 - 1 - j) * S * R ^ j := by
          rw [add_mul, hsum, pow_succ, Finset.sum_range_succ']
          simp only [Nat.add_sub_cancel, Nat.sub_zero, pow_zero, mul_one]
          ac_rfl

/-- The noncommutative identity specialized to actual continuous linear operators.
The remainder is the pure high-frequency chain `R^n`; all other words contain
one regularizing step `S`. -/
theorem kBV_duhamel_apply {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (Q S R : E →L[𝕜] E)
    (hQ : Q = S + R) (n : ℕ) (u : E) :
    (Q ^ n) u = (R ^ n) u +
      ∑ j ∈ Finset.range n, (Q ^ (n - 1 - j)) (S ((R ^ j) u)) := by
  have h := congrArg (fun T : E →L[𝕜] E => T u) (kBV_duhamel Q S R hQ n)
  simpa only [add_apply, sum_apply, mul_apply_eq_comp] using h

/-- The pure high-frequency word has an exponentially small norm when its
operator norm is bounded by `ρ`. It requires no regularity of the input. -/
theorem kBV_duhamel_remainder_bound {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (R : E →L[𝕜] E)
    {ρ : ℝ} (hρ : ‖R‖ ≤ ρ) (n : ℕ) (u : E) :
    ‖(R ^ n) u‖ ≤ ρ ^ n * ‖u‖ := by
  cases n with
  | zero => simp
  | succ n =>
    calc ‖(R ^ (n + 1)) u‖ ≤ ‖R ^ (n + 1)‖ * ‖u‖ := (R ^ (n + 1)).le_opNorm u
      _ ≤ ‖R‖ ^ (n + 1) * ‖u‖ := mul_le_mul_of_nonneg_right
        (norm_pow_le' R (Nat.succ_pos n)) (norm_nonneg _)
      _ ≤ ρ ^ (n + 1) * ‖u‖ := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) hρ (n + 1)) (norm_nonneg _)

end PGM
