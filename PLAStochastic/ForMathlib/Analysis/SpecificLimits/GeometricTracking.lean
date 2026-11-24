import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Contraction, Cauchy limits and pseudo-orbit tracking

The real-analysis steps of `closure-assembly.md` §2–3, with no probability:

* `orbit_contract`: two orbits along which a map halves a distance approach geometrically;
* `geometric_cauchy_limit`: a sequence with `|r j - r k| ≤ M / 2^j` (`j ≤ k`) converges, and
  its limit is approached at the same rate;
* `sum_geometric_le`: `∑_{j<L} M / 2^j ≤ 2 M`;
* `tracking_sum`: `b 1 = 0`, `b (j+1) ≤ δ j + b j / 2` give `∑ b ≤ 2 ∑ δ`.
-/

namespace PGM

open Filter Topology Finset

/-- Two orbits along which `Φ` halves `d` approach geometrically. -/
theorem orbit_contract {α : Type*} (Φ : α → α) (d : α → α → ℝ) (x y : α)
    (h : ∀ i, d (Φ^[i + 1] x) (Φ^[i + 1] y) ≤ d (Φ^[i] x) (Φ^[i] y) / 2) :
    ∀ i, d (Φ^[i] x) (Φ^[i] y) ≤ d x y / 2 ^ i := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    calc d (Φ^[i + 1] x) (Φ^[i + 1] y) ≤ d (Φ^[i] x) (Φ^[i] y) / 2 := h i
      _ ≤ d x y / 2 ^ i / 2 := by gcongr
      _ = d x y / 2 ^ (i + 1) := by rw [pow_succ, div_div]

/-- A sequence with geometric Cauchy control converges at the same rate. -/
theorem geometric_cauchy_limit {r : ℕ → ℝ} {M : ℝ}
    (h : ∀ j k, j ≤ k → |r j - r k| ≤ M / 2 ^ j) :
    ∃ c, Tendsto r atTop (𝓝 c) ∧ ∀ j, |r j - c| ≤ M / 2 ^ j := by
  have hcau : CauchySeq r := by
    refine cauchySeq_of_le_geometric_two (C := 2 * M) fun n => ?_
    rw [Real.dist_eq]
    calc |r n - r (n + 1)| ≤ M / 2 ^ n := h n (n + 1) (Nat.le_succ n)
      _ = 2 * M / 2 / 2 ^ n := by ring
  obtain ⟨c, hc⟩ := cauchySeq_tendsto_of_complete hcau
  refine ⟨c, hc, fun j => ?_⟩
  have hlim : Tendsto (fun k => |r j - r k|) atTop (𝓝 (|r j - c|)) :=
    (tendsto_const_nhds.sub hc).abs
  exact le_of_tendsto hlim (eventually_atTop.2 ⟨j, fun k hk => h j k hk⟩)

theorem sum_geometric_le {M : ℝ} (hM : 0 ≤ M) (L : ℕ) :
    ∑ j ∈ range L, M / 2 ^ j ≤ 2 * M := by
  calc ∑ j ∈ range L, M / 2 ^ j = M * ∑ j ∈ range L, (1 / 2 : ℝ) ^ j := by
        rw [mul_sum]
        exact sum_congr rfl fun j _ => by rw [one_div_pow, mul_one_div]
    _ ≤ M * 2 := by gcongr; exact sum_geometric_two_le L
    _ = 2 * M := by ring

/-- Tracking a pseudo-orbit by a true orbit of a one-half contraction. -/
theorem tracking_sum {b δ : ℕ → ℝ} (hδ : ∀ j, 0 ≤ δ j) (hb1 : b 1 = 0)
    (hrec : ∀ j, 1 ≤ j → b (j + 1) ≤ δ j + b j / 2) :
    ∀ L, ∑ j ∈ Ico 1 L, b j ≤ 2 * ∑ j ∈ Ico 1 L, δ j := by
  -- the positive part of `b` satisfies the same recursion
  set b' : ℕ → ℝ := fun j => max (b j) 0 with hb'
  have hb'1 : b' 1 = 0 := by simp [hb', hb1]
  have hb'rec : ∀ j, 1 ≤ j → b' (j + 1) ≤ δ j + b' j / 2 := by
    intro j hj
    have h1 := hrec j hj
    have h2 : b j ≤ b' j := le_max_left _ _
    have h3 : 0 ≤ b' j := le_max_right _ _
    exact max_le (by linarith) (by linarith [hδ j])
  have key : ∀ L, 1 ≤ L → ∑ j ∈ Ico 1 L, b' j + 2 * b' L ≤ 2 * ∑ j ∈ Ico 1 L, δ j := by
    intro L hL
    induction L, hL using Nat.le_induction with
    | base => simp [hb'1]
    | succ L hL ih =>
      rw [sum_Ico_succ_top hL, sum_Ico_succ_top hL]
      have := hb'rec L hL
      linarith
  intro L
  rcases Nat.eq_zero_or_pos L with h0 | hpos
  · subst h0; simp
  · have hk := key L hpos
    have hle : ∑ j ∈ Ico 1 L, b j ≤ ∑ j ∈ Ico 1 L, b' j :=
      sum_le_sum fun j _ => le_max_left _ _
    have : 0 ≤ b' L := le_max_right _ _
    linarith

end PGM
