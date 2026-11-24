import PLAStochastic.Index.Algorithm.SegmentLength
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Slope bounds and perturbation transfer for prefix feasibility

Deterministic facts about `prefixAffineFeasible` used to compare a key window with a
perturbed copy of it (`lem:slope` in `proofK_reader_bridge.tex`, `eq:Rbound` and
`lem:Kslope` in `proofK_rank_geometry_core.tex`).  Windows are prefixes of the ranks
`0, …, τ`; a window starting at `r` is handled through `prefixAffineFeasible_window`.

* `abs_slope_le`: a witness `(a, b)` on the ranks `0, …, τ` with key span
  `Z = z τ - z 0 > 0` has `|a| ≤ (τ + 2 eps) / Z` (`slope_mul_span_mem`,
  `abs_slope_le_of_two_point` give the endpoint and two-point forms);
* `prefixAffineFeasible_perturb`, `prefixAffineFeasible_transfer(_symm)`: if
  `|y i - (c + s z i)| ≤ ρ` with `s > 0`, feasibility passes between `z` and `y` at the
  cost `(τ + 2 eps) ρ / (s Z)`, respectively `(τ + 2 eps) ρ / (y τ - y 0)`;
* `abs_taylor_remainder_le`: `|φ u - φ u₀ - φ' u₀ (u - u₀)| ≤ L / 2 (u - u₀)²` when
  `φ'` is `L`-Lipschitz on an interval;
* `prefixAffineFeasible_curved_of_feasible`, `prefixAffineFeasible_of_feasible_curved`:
  for curved keys `φ (z j / S)` with `φ' ≥ δ > 0`, feasibility transfers in both
  directions with extra tolerance `(τ + 2 eps) (L / (2 δ)) (z τ - z 0) / S`;
* `prefixAffineFeasible_of_tube`, `prefixAffineFeasible_curved_of_tube`: a tube of
  half-width `x` around the line `z 0 + j μ` gives `(x / μ)`-feasibility, and its
  curved analogue.
-/

namespace PGM

/-! ## Slope bounds for feasible windows -/

/-- Any two ranks of an affine witness pin its slope: the key difference, scaled by the
slope, is within `2 eps` of the rank difference. -/
theorem slope_two_point {eps a b : ℝ} {z : ℕ → ℝ} {len : ℕ}
    (hab : ∀ i < len, |(i : ℝ) - (a * z i + b)| ≤ eps) {i j : ℕ} (hi : i < len)
    (hj : j < len) :
    |((j : ℝ) - i) - a * (z j - z i)| ≤ 2 * eps := by
  have h1 := hab i hi
  have h2 := hab j hj
  have heq : ((j : ℝ) - i) - a * (z j - z i) =
      ((j : ℝ) - (a * z j + b)) - ((i : ℝ) - (a * z i + b)) := by ring
  rw [heq]
  calc |((j : ℝ) - (a * z j + b)) - ((i : ℝ) - (a * z i + b))|
      ≤ |(j : ℝ) - (a * z j + b)| + |(i : ℝ) - (a * z i + b)| := abs_sub _ _
    _ ≤ 2 * eps := by linarith

/-- Endpoint form of `slope_two_point`: for a witness on the ranks `0, …, τ`,
`a * (z τ - z 0) ∈ [τ - 2 eps, τ + 2 eps]`. -/
theorem slope_mul_span_mem {eps a b : ℝ} {z : ℕ → ℝ} {τ : ℕ}
    (hab : ∀ i < τ + 1, |(i : ℝ) - (a * z i + b)| ≤ eps) :
    (τ : ℝ) - 2 * eps ≤ a * (z τ - z 0) ∧ a * (z τ - z 0) ≤ τ + 2 * eps := by
  have h := slope_two_point hab (i := 0) (j := τ) (by omega) (by omega)
  simp only [Nat.cast_zero, sub_zero] at h
  constructor <;> linarith [(abs_le.mp h).1, (abs_le.mp h).2]

/-- Slope bound from any two ranks `i < j` with increasing keys. -/
theorem abs_slope_le_of_two_point {eps a b : ℝ} {z : ℕ → ℝ} {len : ℕ}
    (hab : ∀ i < len, |(i : ℝ) - (a * z i + b)| ≤ eps) {i j : ℕ} (hij : i < j)
    (hj : j < len) (hz : z i < z j) :
    |a| ≤ ((j : ℝ) - i + 2 * eps) / (z j - z i) := by
  have h := slope_two_point hab (by omega : i < len) hj
  have hji : (i : ℝ) < j := by exact_mod_cast hij
  have hd : 0 < z j - z i := by linarith
  rw [le_div_iff₀ hd]
  rcases abs_le.mp h with ⟨h1, h2⟩
  rcases abs_cases a with ⟨ha, -⟩ | ⟨ha, -⟩
  · rw [ha]; linarith
  · rw [ha]; linarith

/-- **Slope bound.** For a witness on the ranks `0, …, τ` whose key span
`Z = z τ - z 0` is positive, `|a| ≤ (τ + 2 eps) / Z`. -/
theorem abs_slope_le {eps a b : ℝ} {z : ℕ → ℝ} {τ : ℕ}
    (hab : ∀ i < τ + 1, |(i : ℝ) - (a * z i + b)| ≤ eps) (hZ : 0 < z τ - z 0) :
    |a| ≤ ((τ : ℝ) + 2 * eps) / (z τ - z 0) := by
  rcases slope_mul_span_mem hab with ⟨h1, h2⟩
  have hτ : (0 : ℝ) ≤ τ := Nat.cast_nonneg τ
  rw [le_div_iff₀ hZ]
  rcases abs_cases a with ⟨ha, -⟩ | ⟨ha, -⟩
  · rw [ha]; exact h2
  · rw [ha]; linarith

/-! ## Perturbation transfer -/

/-- Feasibility is monotone in the tolerance. -/
theorem prefixAffineFeasible_of_le {eps eps' : ℝ} {p : ℕ → ℝ} {len : ℕ}
    (h : prefixAffineFeasible eps p len) (hle : eps ≤ eps') :
    prefixAffineFeasible eps' p len := by
  rcases h with ⟨a, b, hab⟩
  exact ⟨a, b, fun i hi => (hab i hi).trans hle⟩

/-- **Perturbation transfer.** If `z` has a witness of slope `a` with `|a| ≤ A` and
`y` is within `ρ` of the increasing affine image `c + s z`, then `y` is feasible with
tolerance `eps + A ρ / s`, via the witness `(a / s, b - a c / s)`. -/
theorem prefixAffineFeasible_perturb {eps a b A ρ s c : ℝ} {z y : ℕ → ℝ} {len : ℕ}
    (hab : ∀ i < len, |(i : ℝ) - (a * z i + b)| ≤ eps) (ha : |a| ≤ A) (hs : 0 < s)
    (hy : ∀ i < len, |y i - (c + s * z i)| ≤ ρ) :
    prefixAffineFeasible (eps + A * ρ / s) y len := by
  refine ⟨a / s, b - a * c / s, fun i hi => ?_⟩
  have h1 := hab i hi
  have h2 := hy i hi
  have heq : (i : ℝ) - (a / s * y i + (b - a * c / s)) =
      ((i : ℝ) - (a * z i + b)) - a / s * (y i - (c + s * z i)) := by
    field_simp
    ring
  rw [heq]
  have h3 : |a / s * (y i - (c + s * z i))| ≤ A * ρ / s := by
    rw [abs_mul, abs_div, abs_of_pos hs, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (mul_le_mul ha h2 (abs_nonneg _)
      ((abs_nonneg a).trans ha)) hs.le
  calc |((i : ℝ) - (a * z i + b)) - a / s * (y i - (c + s * z i))|
      ≤ |(i : ℝ) - (a * z i + b)| + |a / s * (y i - (c + s * z i))| := abs_sub _ _
    _ ≤ eps + A * ρ / s := add_le_add h1 h3

/-- **Window transfer, forward.** On the ranks `0, …, τ` with key span
`Z = z τ - z 0 > 0`, feasibility of `z` transfers to any `y` within `ρ` of
`c + s z` (`s > 0`), at the cost `(τ + 2 eps) ρ / (s Z)`. -/
theorem prefixAffineFeasible_transfer {eps ρ s c : ℝ} {z y : ℕ → ℝ} {τ : ℕ}
    (h : prefixAffineFeasible eps z (τ + 1)) (hZ : 0 < z τ - z 0) (hs : 0 < s)
    (hy : ∀ i < τ + 1, |y i - (c + s * z i)| ≤ ρ) :
    prefixAffineFeasible (eps + ((τ : ℝ) + 2 * eps) * ρ / (s * (z τ - z 0))) y
      (τ + 1) := by
  rcases h with ⟨a, b, hab⟩
  have h' := prefixAffineFeasible_perturb hab (abs_slope_le hab hZ) hs hy
  have heq : ((τ : ℝ) + 2 * eps) / (z τ - z 0) * ρ / s =
      ((τ : ℝ) + 2 * eps) * ρ / (s * (z τ - z 0)) := by
    field_simp
  rwa [heq] at h'

/-- **Window transfer, reverse.** The roles of `y` and `z` exchanged: on the ranks
`0, …, τ` with `y`-span `Y = y τ - y 0 > 0`, feasibility of `y` transfers back to `z`
at the cost `(τ + 2 eps) ρ / Y` (the inverse map `z ≈ (y - c) / s` has error `ρ / s`
and the factor `1 / s` cancels). -/
theorem prefixAffineFeasible_transfer_symm {eps ρ s c : ℝ} {z y : ℕ → ℝ} {τ : ℕ}
    (h : prefixAffineFeasible eps y (τ + 1)) (hY : 0 < y τ - y 0) (hs : 0 < s)
    (hy : ∀ i < τ + 1, |y i - (c + s * z i)| ≤ ρ) :
    prefixAffineFeasible (eps + ((τ : ℝ) + 2 * eps) * ρ / (y τ - y 0)) z (τ + 1) := by
  have hz : ∀ i < τ + 1, |z i - (-(c / s) + s⁻¹ * y i)| ≤ ρ / s := by
    intro i hi
    have heq : z i - (-(c / s) + s⁻¹ * y i) = -((y i - (c + s * z i)) / s) := by
      field_simp
      ring
    rw [heq, abs_neg, abs_div, abs_of_pos hs]
    exact div_le_div_of_nonneg_right (hy i hi) hs.le
  have h' := prefixAffineFeasible_transfer h hY (inv_pos.mpr hs) hz
  have heq : ((τ : ℝ) + 2 * eps) * (ρ / s) / (s⁻¹ * (y τ - y 0)) =
      ((τ : ℝ) + 2 * eps) * ρ / (y τ - y 0) := by
    field_simp
  rwa [heq] at h'

/-! ## The tube criterion -/

/-- **Tube criterion.** If the keys `z 0, …, z τ` stay within `x` of the line
`z 0 + j μ` with `μ > 0`, then the line `j = (z j - z 0) / μ` certifies
`(x / μ)`-feasibility of the first `τ + 1` keys. -/
theorem prefixAffineFeasible_of_tube {x μ : ℝ} {z : ℕ → ℝ} {τ : ℕ} (hμ : 0 < μ)
    (h : ∀ j ≤ τ, |z j - (z 0 + j * μ)| ≤ x) :
    prefixAffineFeasible (x / μ) z (τ + 1) := by
  refine ⟨1 / μ, -(z 0 / μ), fun j hj => ?_⟩
  have heq : (j : ℝ) - (1 / μ * z j + -(z 0 / μ)) = -((z j - (z 0 + j * μ)) / μ) := by
    field_simp
    ring
  rw [heq, abs_neg, abs_div, abs_of_pos hμ]
  exact div_le_div_of_nonneg_right (h j (by omega)) hμ.le

/-! ## Curvature (Taylor) bound -/

/-- A function with nonnegative derivative (within the interval) on `[p, q]` is monotone
there. -/
private theorem monotoneOn_Icc_of_hasDerivWithinAt {g g' : ℝ → ℝ} {p q : ℝ}
    (hg : ∀ x ∈ Set.Icc p q, HasDerivWithinAt g (g' x) (Set.Icc p q) x)
    (hg' : ∀ x ∈ Set.Icc p q, 0 ≤ g' x) : MonotoneOn g (Set.Icc p q) :=
  monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc p q)
    (fun x hx => (hg x hx).continuousWithinAt)
    (fun x hx => (hg x (interior_subset hx)).mono interior_subset)
    (fun x hx => hg' x (interior_subset hx))

/-- Derivative of the signed Taylor remainder plus a quadratic. -/
private theorem hasDerivWithinAt_taylorAux {φ φ' : ℝ → ℝ} {s : Set ℝ} {x u₀ : ℝ}
    (σ κ : ℝ) (h : HasDerivWithinAt φ (φ' x) s x) :
    HasDerivWithinAt (fun t => σ * (φ t - φ u₀ - φ' u₀ * (t - u₀)) + κ * (t - u₀) ^ 2)
      (σ * (φ' x - φ' u₀) + κ * (2 * (x - u₀))) s x := by
  have h1 : HasDerivWithinAt (fun t => t - u₀) 1 s x := (hasDerivWithinAt_id x s).sub_const u₀
  have h2 := ((h.sub_const (φ u₀)).sub (h1.const_mul (φ' u₀))).const_mul σ
  have h3 := (h1.mul h1).const_mul κ
  have h4 := (h2.add h3).congr_deriv
    (show _ = σ * (φ' x - φ' u₀) + κ * (2 * (x - u₀)) by ring)
  exact h4.congr (fun t _ => by simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]; ring)
    (by simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]; ring)

/-- **Curvature bound.** If `φ` has derivative `φ'` (within `I`) on an interval `I`
and `φ'` is `L`-Lipschitz on `I`, then the first-order Taylor remainder at any
`u₀ ∈ I` is at most `L / 2 * (u - u₀) ^ 2` on `I`. -/
theorem abs_taylor_remainder_le {φ φ' : ℝ → ℝ} {I : Set ℝ} {L : ℝ} (hI : I.OrdConnected)
    (hφ : ∀ x ∈ I, HasDerivWithinAt φ (φ' x) I x)
    (hLip : ∀ x ∈ I, ∀ y ∈ I, |φ' x - φ' y| ≤ L * |x - y|) {u₀ u : ℝ}
    (hu₀ : u₀ ∈ I) (hu : u ∈ I) :
    |φ u - φ u₀ - φ' u₀ * (u - u₀)| ≤ L / 2 * (u - u₀) ^ 2 := by
  rcases le_total u₀ u with hle | hle
  · -- on `[u₀, u]`, `L/2 (t - u₀)² ∓ R(t)` is monotone
    have hsub : Set.Icc u₀ u ⊆ I := hI.out hu₀ hu
    have key : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
        0 ≤ σ * (φ u - φ u₀ - φ' u₀ * (u - u₀)) + L / 2 * (u - u₀) ^ 2 := by
      intro σ hσ
      have hmono := monotoneOn_Icc_of_hasDerivWithinAt
        (g := fun t => σ * (φ t - φ u₀ - φ' u₀ * (t - u₀)) + L / 2 * (t - u₀) ^ 2)
        (fun x hx => hasDerivWithinAt_taylorAux σ (L / 2) ((hφ x (hsub hx)).mono hsub))
        (fun x hx => by
          have hx' := hLip x (hsub hx) u₀ hu₀
          rw [abs_of_nonneg (sub_nonneg.mpr hx.1)] at hx'
          rcases abs_le.mp hx' with ⟨h1, h2⟩
          rcases hσ with rfl | rfl <;> linarith)
        ⟨le_refl u₀, hle⟩ ⟨hle, le_refl u⟩ hle
      simpa using hmono
    have k1 := key 1 (Or.inl rfl)
    have k2 := key (-1) (Or.inr rfl)
    rw [abs_le]
    constructor <;> linarith
  · -- on `[u, u₀]`, `±R(t) - L/2 (t - u₀)²` is monotone
    have hsub : Set.Icc u u₀ ⊆ I := hI.out hu hu₀
    have key : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
        σ * (φ u - φ u₀ - φ' u₀ * (u - u₀)) - L / 2 * (u - u₀) ^ 2 ≤ 0 := by
      intro σ hσ
      have hmono := monotoneOn_Icc_of_hasDerivWithinAt
        (g := fun t => σ * (φ t - φ u₀ - φ' u₀ * (t - u₀)) + -(L / 2) * (t - u₀) ^ 2)
        (fun x hx => hasDerivWithinAt_taylorAux σ (-(L / 2)) ((hφ x (hsub hx)).mono hsub))
        (fun x hx => by
          have hx' := hLip x (hsub hx) u₀ hu₀
          rw [abs_of_nonpos (sub_nonpos.mpr hx.2)] at hx'
          rcases abs_le.mp hx' with ⟨h1, h2⟩
          rcases hσ with rfl | rfl <;> linarith)
        ⟨le_refl u, hle⟩ ⟨hle, le_refl u₀⟩ hle
      have : σ * (φ u - φ u₀ - φ' u₀ * (u - u₀)) + -(L / 2) * (u - u₀) ^ 2 ≤ 0 := by
        simpa using hmono
      linarith
    have k1 := key 1 (Or.inl rfl)
    have k2 := key (-1) (Or.inr rfl)
    rw [abs_le]
    constructor <;> linarith

/-- Mean value lower bound: if `φ' ≥ δ` on the interval `I`, then
`φ u - φ u₀ ≥ δ (u - u₀)` for `u₀ ≤ u` in `I`. -/
theorem mul_sub_le_sub_of_le_deriv {φ φ' : ℝ → ℝ} {I : Set ℝ} {δ : ℝ} (hI : I.OrdConnected)
    (hφ : ∀ x ∈ I, HasDerivWithinAt φ (φ' x) I x) (hδ : ∀ x ∈ I, δ ≤ φ' x) {u₀ u : ℝ}
    (hu₀ : u₀ ∈ I) (hu : u ∈ I) (hle : u₀ ≤ u) :
    δ * (u - u₀) ≤ φ u - φ u₀ := by
  have hsub : Set.Icc u₀ u ⊆ I := hI.out hu₀ hu
  have hmono := monotoneOn_Icc_of_hasDerivWithinAt (g := fun t => φ t - δ * t)
    (fun x hx => ((hφ x (hsub hx)).mono hsub).sub
      ((hasDerivWithinAt_id x _).const_mul δ))
    (fun x hx => by have := hδ x (hsub hx); simp only [mul_one]; linarith)
    ⟨le_refl u₀, hle⟩ ⟨hle, le_refl u⟩ hle
  simp only at hmono
  linarith

/-! ## Window transfer under a smooth monotone change of keys -/

/-- The curved keys `φ (z j / S)` are within `L / 2 * ((z τ - z 0) / S) ^ 2` of their
tangent-line image at the window start. -/
private theorem curved_tangent_bound {φ φ' : ℝ → ℝ} {I : Set ℝ} {L S : ℝ} {z : ℕ → ℝ}
    {τ : ℕ} (hI : I.OrdConnected) (hφ : ∀ x ∈ I, HasDerivWithinAt φ (φ' x) I x)
    (hLip : ∀ x ∈ I, ∀ y ∈ I, |φ' x - φ' y| ≤ L * |x - y|) (hL : 0 ≤ L) (hS : 0 < S)
    (hzI : ∀ j ≤ τ, z j / S ∈ I) (hz : ∀ j ≤ τ, z 0 ≤ z j ∧ z j ≤ z τ) :
    ∀ i < τ + 1, |φ (z i / S) - ((φ (z 0 / S) - φ' (z 0 / S) * (z 0 / S)) +
      φ' (z 0 / S) / S * z i)| ≤ L / 2 * ((z τ - z 0) / S) ^ 2 := by
  intro i hi
  have hT := abs_taylor_remainder_le hI hφ hLip (hzI 0 (Nat.zero_le _)) (hzI i (by omega))
  have heq : φ (z i / S) - ((φ (z 0 / S) - φ' (z 0 / S) * (z 0 / S)) +
      φ' (z 0 / S) / S * z i) =
      φ (z i / S) - φ (z 0 / S) - φ' (z 0 / S) * (z i / S - z 0 / S) := by ring
  rw [heq]
  refine hT.trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
  have h1 : z i / S - z 0 / S = (z i - z 0) / S := by ring
  rw [h1]
  have hzi := hz i (by omega)
  have h2 : 0 ≤ (z i - z 0) / S := div_nonneg (by linarith) hS.le
  have h3 : (z i - z 0) / S ≤ (z τ - z 0) / S :=
    div_le_div_of_nonneg_right (by linarith) hS.le
  exact pow_le_pow_left₀ h2 h3 2

/-- A Lipschitz constant of a function on a set with two distinct points is
nonnegative. -/
private theorem lip_nonneg {φ' : ℝ → ℝ} {I : Set ℝ} {L x y : ℝ}
    (hLip : ∀ x ∈ I, ∀ y ∈ I, |φ' x - φ' y| ≤ L * |x - y|) (hx : x ∈ I) (hy : y ∈ I)
    (hxy : x ≠ y) : 0 ≤ L := by
  have h := hLip x hx y hy
  have hpos : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
  by_contra hneg
  have : L * |x - y| < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hneg) hpos
  linarith [abs_nonneg (φ' x - φ' y)]

/-- **Curvature transfer, forward.** Let `φ` have an `L`-Lipschitz derivative `φ' ≥ δ > 0`
on an interval `I`, let `S > 0`, and let the keys `z 0 ≤ z j ≤ z τ` (`j ≤ τ`) satisfy
`z j / S ∈ I` and `z 0 < z τ`. If `z` is `eps`-feasible on the ranks `0, …, τ`, then so
are the curved keys `φ (z j / S)`, with the extra tolerance
`Ψ = (τ + 2 eps) (L / (2 δ)) (z τ - z 0) / S`. -/
theorem prefixAffineFeasible_curved_of_feasible {φ φ' : ℝ → ℝ} {I : Set ℝ}
    {L δ S eps : ℝ} {z : ℕ → ℝ} {τ : ℕ} (hI : I.OrdConnected)
    (hφ : ∀ x ∈ I, HasDerivWithinAt φ (φ' x) I x)
    (hLip : ∀ x ∈ I, ∀ y ∈ I, |φ' x - φ' y| ≤ L * |x - y|)
    (hδ : 0 < δ) (hφδ : ∀ x ∈ I, δ ≤ φ' x) (hS : 0 < S)
    (hzI : ∀ j ≤ τ, z j / S ∈ I) (hz : ∀ j ≤ τ, z 0 ≤ z j ∧ z j ≤ z τ)
    (hZ : z 0 < z τ) (h : prefixAffineFeasible eps z (τ + 1)) :
    prefixAffineFeasible (eps + ((τ : ℝ) + 2 * eps) * (L / (2 * δ)) * (z τ - z 0) / S)
      (fun j => φ (z j / S)) (τ + 1) := by
  have heps : 0 ≤ eps := by
    obtain ⟨a, b, hab⟩ := h
    exact (abs_nonneg _).trans (hab 0 (by omega))
  have hZS : z 0 / S ≠ z τ / S := by
    intro he
    rw [div_left_inj' hS.ne'] at he
    linarith
  have hL : 0 ≤ L := lip_nonneg hLip (hzI 0 (Nat.zero_le _)) (hzI τ le_rfl) hZS
  have hd : δ ≤ φ' (z 0 / S) := hφδ _ (hzI 0 (Nat.zero_le _))
  have hd0 : 0 < φ' (z 0 / S) := lt_of_lt_of_le hδ hd
  have hZ' : 0 < z τ - z 0 := by linarith
  have ht := prefixAffineFeasible_transfer h hZ' (div_pos hd0 hS)
    (curved_tangent_bound hI hφ hLip hL hS hzI hz)
  refine prefixAffineFeasible_of_le ht (add_le_add le_rfl ?_)
  have hτ : 0 ≤ (τ : ℝ) + 2 * eps := by positivity
  have e1 : ((τ : ℝ) + 2 * eps) * (L / 2 * ((z τ - z 0) / S) ^ 2) /
      (φ' (z 0 / S) / S * (z τ - z 0)) =
      ((τ : ℝ) + 2 * eps) * (L * (z τ - z 0)) / (2 * S * φ' (z 0 / S)) := by
    field_simp
  have e2 : ((τ : ℝ) + 2 * eps) * (L / (2 * δ)) * (z τ - z 0) / S =
      ((τ : ℝ) + 2 * eps) * (L * (z τ - z 0)) / (2 * S * δ) := by
    field_simp
  rw [e1, e2]
  exact div_le_div_of_nonneg_left (mul_nonneg hτ (mul_nonneg hL hZ'.le)) (by positivity)
    (mul_le_mul_of_nonneg_left hd (by positivity))

/-- **Curvature transfer, reverse.** Under the hypotheses of
`prefixAffineFeasible_curved_of_feasible`, `eps`-feasibility of the curved keys
`φ (z j / S)` on the ranks `0, …, τ` gives feasibility of `z` with the same extra
tolerance `Ψ = (τ + 2 eps) (L / (2 δ)) (z τ - z 0) / S`; the curved span is at least
`δ (z τ - z 0) / S` by the mean value inequality. -/
theorem prefixAffineFeasible_of_feasible_curved {φ φ' : ℝ → ℝ} {I : Set ℝ}
    {L δ S eps : ℝ} {z : ℕ → ℝ} {τ : ℕ} (hI : I.OrdConnected)
    (hφ : ∀ x ∈ I, HasDerivWithinAt φ (φ' x) I x)
    (hLip : ∀ x ∈ I, ∀ y ∈ I, |φ' x - φ' y| ≤ L * |x - y|)
    (hδ : 0 < δ) (hφδ : ∀ x ∈ I, δ ≤ φ' x) (hS : 0 < S)
    (hzI : ∀ j ≤ τ, z j / S ∈ I) (hz : ∀ j ≤ τ, z 0 ≤ z j ∧ z j ≤ z τ)
    (hZ : z 0 < z τ) (h : prefixAffineFeasible eps (fun j => φ (z j / S)) (τ + 1)) :
    prefixAffineFeasible (eps + ((τ : ℝ) + 2 * eps) * (L / (2 * δ)) * (z τ - z 0) / S)
      z (τ + 1) := by
  have heps : 0 ≤ eps := by
    obtain ⟨a, b, hab⟩ := h
    exact (abs_nonneg _).trans (hab 0 (by omega))
  have hZS : z 0 / S ≠ z τ / S := by
    intro he
    rw [div_left_inj' hS.ne'] at he
    linarith
  have hL : 0 ≤ L := lip_nonneg hLip (hzI 0 (Nat.zero_le _)) (hzI τ le_rfl) hZS
  have hd : δ ≤ φ' (z 0 / S) := hφδ _ (hzI 0 (Nat.zero_le _))
  have hd0 : 0 < φ' (z 0 / S) := lt_of_lt_of_le hδ hd
  have hZ' : 0 < z τ - z 0 := by linarith
  -- the curved span dominates `δ Z / S`
  have hY : δ * ((z τ - z 0) / S) ≤ φ (z τ / S) - φ (z 0 / S) := by
    have := mul_sub_le_sub_of_le_deriv hI hφ hφδ (hzI 0 (Nat.zero_le _)) (hzI τ le_rfl)
      (div_le_div_of_nonneg_right hZ.le hS.le)
    have e : z τ / S - z 0 / S = (z τ - z 0) / S := by ring
    rwa [e] at this
  have hYpos : 0 < δ * ((z τ - z 0) / S) := mul_pos hδ (div_pos hZ' hS)
  have ht := prefixAffineFeasible_transfer_symm h (lt_of_lt_of_le hYpos hY)
    (div_pos hd0 hS) (curved_tangent_bound hI hφ hLip hL hS hzI hz)
  refine prefixAffineFeasible_of_le ht (add_le_add le_rfl ?_)
  have hτ : 0 ≤ (τ : ℝ) + 2 * eps := by positivity
  have hρ : 0 ≤ ((τ : ℝ) + 2 * eps) * (L / 2 * ((z τ - z 0) / S) ^ 2) := by positivity
  calc ((τ : ℝ) + 2 * eps) * (L / 2 * ((z τ - z 0) / S) ^ 2) /
        (φ (z τ / S) - φ (z 0 / S))
      ≤ ((τ : ℝ) + 2 * eps) * (L / 2 * ((z τ - z 0) / S) ^ 2) /
        (δ * ((z τ - z 0) / S)) := div_le_div_of_nonneg_left hρ hYpos hY
    _ = ((τ : ℝ) + 2 * eps) * (L / (2 * δ)) * (z τ - z 0) / S := by
        field_simp

/-- **Tube criterion for curved keys.** If the keys `z 0, …, z τ` stay within `x` of the
line `z 0 + j μ` (`μ > 0`), then under the hypotheses of
`prefixAffineFeasible_curved_of_feasible` the curved keys `φ (z j / S)` are feasible with
tolerance `x / μ + (τ + 2 x / μ) (L / (2 δ)) (z τ - z 0) / S`. -/
theorem prefixAffineFeasible_curved_of_tube {φ φ' : ℝ → ℝ} {I : Set ℝ}
    {L δ S x μ : ℝ} {z : ℕ → ℝ} {τ : ℕ} (hI : I.OrdConnected)
    (hφ : ∀ v ∈ I, HasDerivWithinAt φ (φ' v) I v)
    (hLip : ∀ v ∈ I, ∀ w ∈ I, |φ' v - φ' w| ≤ L * |v - w|)
    (hδ : 0 < δ) (hφδ : ∀ v ∈ I, δ ≤ φ' v) (hS : 0 < S)
    (hzI : ∀ j ≤ τ, z j / S ∈ I) (hz : ∀ j ≤ τ, z 0 ≤ z j ∧ z j ≤ z τ)
    (hZ : z 0 < z τ) (hμ : 0 < μ) (htube : ∀ j ≤ τ, |z j - (z 0 + j * μ)| ≤ x) :
    prefixAffineFeasible
      (x / μ + ((τ : ℝ) + 2 * (x / μ)) * (L / (2 * δ)) * (z τ - z 0) / S)
      (fun j => φ (z j / S)) (τ + 1) :=
  prefixAffineFeasible_curved_of_feasible hI hφ hLip hδ hφδ hS hzI hz hZ
    (prefixAffineFeasible_of_tube hμ htube)

end PGM
