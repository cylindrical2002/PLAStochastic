import PLAStochastic.ForMathlib.Analysis.Calculus.MellinOperator
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin

/-!
# Track O: the radial insertion polynomials

Objects of the radial formula for the high-frequency bound of the actual one-layer output
(`research/2026-09-29-ceps-full-expansion/smoothing.md` (S4)–(S6),
`output-closure.md` §2; design `research/2026-10-02-lean-ceps/design.md`, interface T2).

For `n` gap coordinates and a sequence `c : Fin j → Fin n` of insertion positions,
`outCount c l` counts the insertions at `l`, and `outMon f α x = ∏_l (mellinOp^[α l] f)(x l)`.
The `j`-fold dilation generator `ℒ^j` applied to `∏_l f(x_l)` is
`outMonSum f j x = ∑_{c : Fin j → Fin n} outMon f (outCount c) x`
(no multinomial coefficients: each insertion order is a separate term), and
`outRadial f k x = ∑_{i ≤ k} outCoeff k i · outMonSum f i x` is
`∏_{a=1}^k (ℒ - a) ∏_l f(x_l)`, where `outCoeff k i` is the coefficient of `t^i` in
`∏_{a=1}^k (t - a)`.
-/

noncomputable section

open Finset

namespace PGM

variable {n : ℕ}

/-- Number of insertions at position `l`. -/
def outCount {j : ℕ} (c : Fin j → Fin n) (l : Fin n) : ℕ := #{t | c t = l}

/-- The insertion monomial `∏_l (mellinOp^[α l] f)(x l)`. -/
def outMon (f : ℝ → ℝ) (α : Fin n → ℕ) (x : Fin n → ℝ) : ℝ := ∏ l, mellinOp^[α l] f (x l)

/-- `ℒ^j ∏_l f(x_l)`, summed over insertion sequences. -/
def outMonSum (f : ℝ → ℝ) (j : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∑ c : Fin j → Fin n, outMon f (outCount c) x

/-- Coefficients of `∏_{a=1}^k (t - a)`. -/
def outCoeff : ℕ → ℕ → ℝ
  | 0, i => if i = 0 then 1 else 0
  | k + 1, 0 => -((k : ℝ) + 1) * outCoeff k 0
  | k + 1, i + 1 => outCoeff k i - ((k : ℝ) + 1) * outCoeff k (i + 1)

/-- `∏_{a=1}^k (ℒ - a) ∏_l f(x_l)`. -/
def outRadial (f : ℝ → ℝ) (k : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∑ i ∈ range (k + 1), outCoeff k i * outMonSum f i x

theorem outCoeff_eq_zero : ∀ {k i : ℕ}, k < i → outCoeff k i = 0
  | 0, i, h => by simp [outCoeff, Nat.pos_iff_ne_zero.mp h]
  | k + 1, 0, h => absurd h (Nat.not_lt_zero _)
  | k + 1, i + 1, h => by
    rw [outCoeff, outCoeff_eq_zero (by omega : k < i), outCoeff_eq_zero (by omega : k < i + 1)]
    ring

theorem outCount_cons {j : ℕ} (l : Fin n) (c : Fin j → Fin n) (l' : Fin n) :
    outCount (Fin.cons l c : Fin (j + 1) → Fin n) l' =
      outCount c l' + if l = l' then 1 else 0 := by
  classical
  simp only [outCount, Finset.card_filter]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

theorem outCount_zero (c : Fin 0 → Fin n) : outCount c = fun _ => 0 := by
  funext l; simp [outCount]

theorem sum_outCount {j : ℕ} (c : Fin j → Fin n) : ∑ l, outCount c l = j := by
  classical
  simp only [outCount]
  rw [← Finset.card_eq_sum_card_fiberwise (fun t _ => Finset.mem_univ (c t))]
  simp

theorem outCount_le {j : ℕ} (c : Fin j → Fin n) (l : Fin n) : outCount c l ≤ j := by
  calc outCount c l ≤ ∑ l', outCount c l' :=
        Finset.single_le_sum (f := outCount c) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
    _ = j := sum_outCount c

theorem outMonSum_zero (f : ℝ → ℝ) (x : Fin n → ℝ) : outMonSum f 0 x = ∏ l, f (x l) := by
  simp [outMonSum, outMon, outCount_zero]

theorem outRadial_zero (f : ℝ → ℝ) (x : Fin n → ℝ) : outRadial f 0 x = ∏ l, f (x l) := by
  simp [outRadial, outCoeff, outMonSum_zero]

/-- The insertion monomials vanish off the positive orthant when `f` vanishes on `(-∞, 0]`. -/
theorem outMon_eq_zero {f : ℝ → ℝ} (hf0 : ∀ x ≤ 0, f x = 0) (α : Fin n → ℕ)
    {x : Fin n → ℝ} {l : Fin n} (hl : x l ≤ 0) : outMon f α x = 0 :=
  Finset.prod_eq_zero (Finset.mem_univ l) (mellinOp_iterate_eq_zero_of_nonpos hf0 _ _ hl)

theorem outMonSum_eq_zero {f : ℝ → ℝ} (hf0 : ∀ x ≤ 0, f x = 0) (j : ℕ)
    {x : Fin n → ℝ} {l : Fin n} (hl : x l ≤ 0) : outMonSum f j x = 0 :=
  Finset.sum_eq_zero fun _ _ => outMon_eq_zero hf0 _ hl

theorem outRadial_eq_zero {f : ℝ → ℝ} (hf0 : ∀ x ≤ 0, f x = 0) (k : ℕ)
    {x : Fin n → ℝ} {l : Fin n} (hl : x l ≤ 0) : outRadial f k x = 0 :=
  Finset.sum_eq_zero fun i _ => by rw [outMonSum_eq_zero hf0 i hl, mul_zero]

/-- Recursion of `outRadial`: `∑_i c_{k,i} (M_{i+1} - (k+1) M_i) = ∑_i c_{k+1,i} M_i`. -/
theorem outCoeff_succ_sum (k : ℕ) (M : ℕ → ℝ) :
    ∑ i ∈ range (k + 1), outCoeff k i * (M (i + 1) - ((k : ℝ) + 1) * M i) =
      ∑ i ∈ range (k + 2), outCoeff (k + 1) i * M i := by
  rw [Finset.sum_range_succ' _ (k + 1)]
  simp only [outCoeff]
  have h1 : ∑ i ∈ range (k + 1), (outCoeff k i - ((k : ℝ) + 1) * outCoeff k (i + 1)) * M (i + 1)
      = ∑ i ∈ range (k + 1), outCoeff k i * M (i + 1) -
        ((k : ℝ) + 1) * ∑ i ∈ range (k + 1), outCoeff k (i + 1) * M (i + 1) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [h1]
  have h2 : ∑ i ∈ range (k + 1), outCoeff k (i + 1) * M (i + 1) =
      ∑ i ∈ range (k + 1), outCoeff k i * M i - outCoeff k 0 * M 0 := by
    rw [Finset.sum_range_succ (fun i => outCoeff k (i + 1) * M (i + 1)),
      outCoeff_eq_zero (by omega : k < k + 1), zero_mul, add_zero,
      Finset.sum_range_succ' (fun i => outCoeff k i * M i)]
    ring
  rw [h2]
  have h3 : ∑ i ∈ range (k + 1), outCoeff k i * (M (i + 1) - ((k : ℝ) + 1) * M i) =
      ∑ i ∈ range (k + 1), outCoeff k i * M (i + 1) -
        ((k : ℝ) + 1) * ∑ i ∈ range (k + 1), outCoeff k i * M i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h3]
  ring

end PGM
