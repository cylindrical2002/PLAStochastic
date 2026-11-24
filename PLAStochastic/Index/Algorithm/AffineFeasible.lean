import PLAStochastic.Index.Algorithm.RankPromotion
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# ALG-OPT affine feasibility and constant-line bound

This module defines the ALG-OPT feasibility predicate `prefixAffineFeasible`
and the constant-line bound `q = ⌊2ε⌋ + 1`. The actual greedy scan/restart run
is `finSegLen`/`finCut`/`finSegCount` in `PLAStochastic.Index.Algorithm.Segmentation`.
-/

namespace PGM

/-! ## The finite constant-line lower bound -/

/--
A natural `q` with `q - 1 ≤ 2 * eps` is covered by the constant line at
height `eps`: every integer rank in the prefix has error at most `eps`.
This is the elementary geometric input behind the usual
`floor (2 * eps) + 1` lower bound for a greedy segment length.  We state the
real inequality explicitly and provide the canonical floor instantiation
below; connecting it to a PLA stopping predicate remains separate.
-/
theorem constantLine_covers_of_bound {eps : ℝ} {q : ℕ}
    (hq : ((q : ℝ) - 1) ≤ 2 * eps) :
    ∀ i < q, |(i : ℝ) - eps| ≤ eps := by
  intro i hi
  have hil : i ≤ q - 1 := Nat.le_pred_of_lt hi
  have hilr : (i : ℝ) ≤ (q : ℝ) - 1 := by
    calc
      (i : ℝ) ≤ (q - 1 : ℕ) := by exact_mod_cast hil
      _ = (q : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ q)]
        norm_num
  have hilupper : (i : ℝ) ≤ 2 * eps := hilr.trans hq
  have hi0 : (0 : ℝ) ≤ (i : ℝ) := by exact_mod_cast (Nat.zero_le i)
  apply (abs_le).2
  constructor <;> linarith

/--
An explicit interface for the integer immediately after `2*eps`.  The two
inequalities characterize the intended value `q = floor (2*eps) + 1`; keeping
them as fields also lets a stopping-rule development consume the certificate
without unfolding the real-floor implementation.
-/
structure ConstantLineLengthCertificate (eps : ℝ) where
  q : ℕ
  lower : 2 * eps < q
  upper : ((q : ℝ) - 1) ≤ 2 * eps

theorem ConstantLineLengthCertificate.q_ge_three {eps : ℝ}
    (C : ConstantLineLengthCertificate eps) (heps : 1 ≤ eps) :
    3 ≤ C.q := by
  have h : (2 : ℝ) < C.q := lt_of_le_of_lt (by linarith) C.lower
  exact_mod_cast h

theorem ConstantLineLengthCertificate.covers {eps : ℝ}
    (C : ConstantLineLengthCertificate eps) :
    ∀ i < C.q, |(i : ℝ) - eps| ≤ eps :=
  constantLine_covers_of_bound C.upper

/-- The canonical certificate with `q = floor (2 * eps) + 1`. -/
noncomputable def ConstantLineLengthCertificate.of_nonneg {eps : ℝ}
    (heps : 0 ≤ eps) : ConstantLineLengthCertificate eps :=
  { q := Nat.floor (2 * eps) + 1
    lower := by
      have h := Nat.lt_floor_add_one (2 * eps)
      simpa [Nat.cast_add, Nat.cast_one] using h
    upper := by
      have h := Nat.floor_le (show (0 : ℝ) ≤ 2 * eps by linarith)
      simpa [Nat.cast_add, Nat.cast_one] using h }

/-! ## Prefix affine feasibility -/

/-- Affine `eps`-feasibility for a finite prefix of an arbitrary key stream.
    The rank is counted by the number of keys, so a prefix of length `r`
    uses indices `0, ..., r - 1`. -/
def prefixAffineFeasible (eps : ℝ) (keys : ℕ → ℝ) (length : ℕ) : Prop :=
  ∃ a b : ℝ, ∀ i < length, |(i : ℝ) - (a * keys i + b)| ≤ eps

theorem prefixAffineFeasible_constantLine {eps : ℝ} {keys : ℕ → ℝ}
    (C : ConstantLineLengthCertificate eps) {length : ℕ}
    (hlen : length ≤ C.q) : prefixAffineFeasible eps keys length := by
  refine ⟨0, eps, ?_⟩
  intro i hi
  have hiq : i < C.q := lt_of_lt_of_le hi hlen
  have h := C.covers i hiq
  simpa using h


end PGM
