import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# The Mellin (dilation) operator on functions of one real variable

`mellinOp h = (x h)' = h + x h'` is the generator of the dilations `h ↦ λ h(λ x)` at
`λ = 1`. This file records:

* vanishing: if `h = 0` on `(-∞, 0]` then so are all iterates `mellinOp^[a] h`
  (`mellinOp_iterate_eq_zero_of_nonpos`);
* smoothness: `mellinOp` loses one derivative (`contDiff_mellinOp`,
  `contDiff_mellinOp_iterate`);
* the score `mellinScore h = mellinOp h / h` (zero where `h = 0`) satisfies
  `mellinScore h · h = mellinOp h` for nonnegative `h`, because each zero of a
  nonnegative function is a local minimum, where the derivative vanishes
  (`mellinScore_mul_self`).
-/

noncomputable section

open Set Filter Topology

namespace PGM

/-- The Mellin operator `(mellinOp h)(x) = h(x) + x h'(x) = (x h(x))'`. -/
def mellinOp (h : ℝ → ℝ) : ℝ → ℝ := fun x => h x + x * deriv h x

theorem mellinOp_apply (h : ℝ → ℝ) (x : ℝ) : mellinOp h x = h x + x * deriv h x := rfl

/-- `mellinOp` preserves vanishing on `(-∞, 0]`. -/
theorem mellinOp_eq_zero_of_nonpos {h : ℝ → ℝ} (h0 : ∀ x ≤ 0, h x = 0) :
    ∀ x ≤ 0, mellinOp h x = 0 := by
  intro x hx
  rcases hx.lt_or_eq with hlt | rfl
  · have hev : h =ᶠ[𝓝 x] fun _ => 0 :=
      Filter.eventually_of_mem (Iio_mem_nhds hlt) fun y hy => h0 y (le_of_lt hy)
    rw [mellinOp_apply, h0 x hx, hev.deriv_eq, deriv_const]
    ring
  · rw [mellinOp_apply, h0 0 le_rfl]
    ring

theorem mellinOp_iterate_eq_zero_of_nonpos {h : ℝ → ℝ} (h0 : ∀ x ≤ 0, h x = 0) (a : ℕ) :
    ∀ x ≤ 0, mellinOp^[a] h x = 0 := by
  induction a with
  | zero => simpa using h0
  | succ a ih =>
    rw [Function.iterate_succ_apply']
    exact mellinOp_eq_zero_of_nonpos ih

/-- `mellinOp` loses one derivative. -/
theorem contDiff_mellinOp {p : ℕ} {h : ℝ → ℝ} (hh : ContDiff ℝ (p + 1) h) :
    ContDiff ℝ p (mellinOp h) := by
  have h1 : ContDiff ℝ p h := hh.of_le (by exact_mod_cast Nat.le_succ p)
  have h2 : ContDiff ℝ p (deriv h) := hh.deriv'
  exact ContDiff.add h1 (ContDiff.mul contDiff_id h2)

theorem contDiff_mellinOp_iterate {m : ℕ} {h : ℝ → ℝ} (hh : ContDiff ℝ m h) :
    ∀ a ≤ m, ContDiff ℝ (m - a : ℕ) (mellinOp^[a] h) := by
  intro a
  induction a with
  | zero => intro _; simpa using hh
  | succ a ih =>
    intro ha
    rw [Function.iterate_succ_apply']
    have h' := ih (Nat.le_of_succ_le ha)
    have e : m - a = (m - (a + 1)) + 1 := by omega
    rw [e] at h'
    exact contDiff_mellinOp (by exact_mod_cast h')

theorem differentiable_mellinOp_iterate {m : ℕ} {h : ℝ → ℝ} (hh : ContDiff ℝ m h) {a : ℕ}
    (ha : a < m) : Differentiable ℝ (mellinOp^[a] h) :=
  (contDiff_mellinOp_iterate hh a ha.le).differentiable
    (by have : m - a ≠ 0 := by omega
        exact_mod_cast this)

theorem measurable_mellinOp {h : ℝ → ℝ} (hh : Measurable h) : Measurable (mellinOp h) :=
  hh.add (measurable_id.mul (measurable_deriv h))

theorem measurable_mellinOp_iterate {h : ℝ → ℝ} (hh : Measurable h) :
    ∀ a, Measurable (mellinOp^[a] h) := by
  intro a
  induction a with
  | zero => simpa using hh
  | succ a ih =>
    rw [Function.iterate_succ_apply']
    exact measurable_mellinOp ih

/-- At a zero of a nonnegative differentiable function, `mellinOp` vanishes. -/
theorem mellinOp_eq_zero_of_eq_zero {h : ℝ → ℝ} (hpos : ∀ y, 0 ≤ h y) {x : ℝ}
    (hx : h x = 0) : mellinOp h x = 0 := by
  have hmin : IsLocalMin h x := Filter.Eventually.of_forall fun y => by
    rw [hx]; exact hpos y
  rw [mellinOp_apply, hx, hmin.deriv_eq_zero]
  ring

/-- The scale score `mellinOp h / h`, equal to zero where `h = 0`. -/
def mellinScore (h : ℝ → ℝ) : ℝ → ℝ := fun x => mellinOp h x / h x

theorem mellinScore_mul_self {h : ℝ → ℝ} (hpos : ∀ y, 0 ≤ h y) (x : ℝ) :
    mellinScore h x * h x = mellinOp h x := by
  by_cases hx : h x = 0
  · rw [hx, mul_zero, mellinOp_eq_zero_of_eq_zero hpos hx]
  · exact div_mul_cancel₀ _ hx

end PGM
