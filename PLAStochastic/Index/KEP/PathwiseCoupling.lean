import PLAStochastic.Index.KEP.PrefixStability
import PLAStochastic.Index.KEP.PivotStopping
import PLAStochastic.Index.Algorithm.SlopeTransfer

/-!
# Pathwise coupling of a curved hierarchy with its affine reference

All statements are deterministic.  A reference base pair sequence `z'` (unit counts,
positive gaps, all layers finite) has the strictly increasing keys
`y t = pairKeys z' t`, `y 0 = 0`.  An actual base pair sequence `z` (unit counts, all
layers finite) has, up to the base rank `d`, the curved keys
`pairKeys z t = φ (y t / S) - φ 0`, where `φ` has an `L`-Lipschitz derivative
`φ' ≥ δ > 0` on an order-connected set `I ⊇ [0, y d / S]`.

* `feasible_curved_of_feasible_ref`, `feasible_ref_of_feasible_curved`: the curvature
  transfer of `PLAStochastic.Index.Algorithm.SlopeTransfer` for a window of `τ + 1` keys at strictly increasing
  positions, with an additive constant in the curved keys and a target tolerance;
  a window of one key is feasible at any nonnegative tolerance (`prefixAffineFeasible_one`).
* `layerPivot_coupling_of_le`: on the good event (margin, block length, key span) of the
  reference blocks below layer `L_top` starting before `s`, if the curved region contains the
  ranks `[0, s]` (`s ≤ d`), the curved and the reference hierarchies have the same pivots at
  every position at or before `s` in either hierarchy, through layer `L_top`.
-/

namespace PGM

noncomputable section

open Classical Finset

/-! ## Curvature transfer with a constant shift and a target tolerance -/

section Transfer

variable {φ φ' : ℝ → ℝ} {I : Set ℝ} {L δ S : ℝ}

/-- **Forward transfer.** Reference positions `p` (strictly increasing, `p j / S ∈ I`)
that are `θ`-feasible on the ranks `0, …, τ` make the curved keys
`q j = φ (p j / S) + c` feasible at any tolerance `eps ≥ 0` dominating
`θ + (τ + 2 θ) (L / (2 δ)) (p τ - p 0) / S`. -/
theorem feasible_curved_of_feasible_ref {θ eps c : ℝ} {p q : ℕ → ℝ} {τ : ℕ}
    (hI : I.OrdConnected) (hφ : ∀ x ∈ I, HasDerivWithinAt φ (φ' x) I x)
    (hLip : ∀ x ∈ I, ∀ y ∈ I, |φ' x - φ' y| ≤ L * |x - y|)
    (hδ : 0 < δ) (hφδ : ∀ x ∈ I, δ ≤ φ' x) (hS : 0 < S)
    (hp : StrictMono p) (hpI : ∀ j ≤ τ, p j / S ∈ I) (hq : ∀ j ≤ τ, q j = φ (p j / S) + c)
    (heps : 0 ≤ eps) (hΨ : θ + ((τ : ℝ) + 2 * θ) * (L / (2 * δ)) * (p τ - p 0) / S ≤ eps)
    (h : prefixAffineFeasible θ p (τ + 1)) : prefixAffineFeasible eps q (τ + 1) := by
  rcases Nat.eq_zero_or_pos τ with rfl | hτ
  · exact prefixAffineFeasible_one heps q
  · have h1 := prefixAffineFeasible_curved_of_feasible hI hφ hLip hδ hφδ hS hpI
      (fun j hj => ⟨hp.monotone (Nat.zero_le j), hp.monotone hj⟩) (hp hτ) h
    have h2 := (prefixAffineFeasible_affine_iff (s := 1) (c := c) one_ne_zero).mpr h1
    rw [prefixAffineFeasible_congr (p' := q)
      (fun i hi => by rw [hq i (by omega), one_mul])] at h2
    exact prefixAffineFeasible_of_le h2 hΨ

/-- **Reverse transfer.** Under the hypotheses of `feasible_curved_of_feasible_ref`,
`θ`-feasibility of the curved keys `q j = φ (p j / S) + c` on the ranks `0, …, τ` makes
the positions `p` feasible at any tolerance `eps ≥ 0` dominating
`θ + (τ + 2 θ) (L / (2 δ)) (p τ - p 0) / S`. -/
theorem feasible_ref_of_feasible_curved {θ eps c : ℝ} {p q : ℕ → ℝ} {τ : ℕ}
    (hI : I.OrdConnected) (hφ : ∀ x ∈ I, HasDerivWithinAt φ (φ' x) I x)
    (hLip : ∀ x ∈ I, ∀ y ∈ I, |φ' x - φ' y| ≤ L * |x - y|)
    (hδ : 0 < δ) (hφδ : ∀ x ∈ I, δ ≤ φ' x) (hS : 0 < S)
    (hp : StrictMono p) (hpI : ∀ j ≤ τ, p j / S ∈ I) (hq : ∀ j ≤ τ, q j = φ (p j / S) + c)
    (heps : 0 ≤ eps) (hΨ : θ + ((τ : ℝ) + 2 * θ) * (L / (2 * δ)) * (p τ - p 0) / S ≤ eps)
    (h : prefixAffineFeasible θ q (τ + 1)) : prefixAffineFeasible eps p (τ + 1) := by
  rcases Nat.eq_zero_or_pos τ with rfl | hτ
  · exact prefixAffineFeasible_one heps p
  · rw [prefixAffineFeasible_congr (p' := fun i => 1 * φ (p i / S) + c)
      (fun i hi => by rw [hq i (by omega), one_mul])] at h
    have h1 := prefixAffineFeasible_of_feasible_curved hI hφ hLip hδ hφδ hS hpI
      (fun j hj => ⟨hp.monotone (Nat.zero_le j), hp.monotone hj⟩) (hp hτ)
      ((prefixAffineFeasible_affine_iff one_ne_zero).mp h)
    exact prefixAffineFeasible_of_le h1 hΨ

/-- Monotonicity of the curvature cost `A c G / S` in `A ≥ 0` and `G ≥ 0`; a negative
coefficient `c` makes the cost nonpositive. -/
theorem curvCost_le {A A' c G G' S u : ℝ} (hA : 0 ≤ A) (hAA : A ≤ A') (hG : 0 ≤ G)
    (hGG : G ≤ G') (hS : 0 < S) (hu : 0 ≤ u) (h : A' * c * G' / S ≤ u) :
    A * c * G / S ≤ u := by
  rcases le_or_gt 0 c with hc | hc
  · refine le_trans (div_le_div_of_nonneg_right ?_ hS.le) h
    exact mul_le_mul (mul_le_mul_of_nonneg_right hAA hc) hGG hG
      (mul_nonneg (hA.trans hAA) hc)
  · refine le_trans (div_nonpos_of_nonpos_of_nonneg ?_ hS.le) hu
    exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hA hc.le) hG

end Transfer

/-! ## The coupled hierarchies -/

section Hierarchy

variable {eps : ℝ} {z z' : ℕ → ℝ × ℕ}

/-- Positive gaps give strictly increasing keys. -/
theorem pairKeys_strictMono (hgap : ∀ t, 0 < (z t).1) : StrictMono (pairKeys z) :=
  strictMono_nat_of_lt_succ fun t => by
    simp only [pairKeys, sum_range_succ]
    linarith [hgap t]

/-- The key sequence starts at `0`. -/
theorem pairKeys_zero (z : ℕ → ℝ × ℕ) : pairKeys z 0 = 0 := by simp [pairKeys]

/-- With nonnegative threshold and finite layers, the base pivots of every block are
strictly increasing. -/
theorem blockPivots_strictMono (heps : 0 ≤ eps) (hz : ∀ t, (z t).2 = 1)
    (hfin : AllLayersFinite eps z) (ℓ k : ℕ) : StrictMono (blockPivots eps z ℓ k) :=
  fun _ _ hij => layerPivot_strictMono heps hz hfin ℓ (Nat.add_lt_add_left hij _)

variable {φ φ' : ℝ → ℝ} {I : Set ℝ} {L δ S : ℝ} {d : ℕ}

/-- **Pathwise coupling of the curved hierarchy with its affine reference.**  The
reference base pairs `z'` have unit counts, positive gaps and finite layers, with keys
`y = pairKeys z'`; the actual base pairs `z` have unit counts, finite layers and the
curved keys `pairKeys z t = φ (y t / S) - φ 0` for `t ≤ d`, where `φ` has derivative
`φ' ≥ δ > 0` within the order-connected set `I ⊇ [0, y d / S]` and `φ'` is `L`-Lipschitz
on `I`, and `s ≤ d`.  Suppose that for every layer `ℓ < L_top`, `0 ≤ u ℓ ≤ eps` and
`(Tmax + 1 + 2 (eps + u ℓ)) (L / (2 δ)) Gmax ℓ / S ≤ u ℓ`, and that every reference
layer-`ℓ` block `k` starting before `s`, with `T = layerBlockLen eps z' ℓ k` keys at the
base pivots `b = blockPivots eps z' ℓ k`, satisfies
* (M) the margin: `y ∘ b` is `(eps - u ℓ)`-feasible on `T` keys and
  `(eps + u ℓ)`-infeasible on `T + 1` keys;
* (T) `T ≤ Tmax`;  (G) `y (b T) - y (b 0) ≤ Gmax ℓ`.

Then through layer `L_top` the two hierarchies have the same pivot at every position
where one of them has a pivot at or before `s`.  The windows compared by
`layerPivot_stable_of_margin` only use base keys at ranks `≤ s`, so no block needs to end
inside the curved region. -/
theorem layerPivot_coupling_of_le (heps : 0 ≤ eps) (hz : ∀ t, (z t).2 = 1)
    (hz' : ∀ t, (z' t).2 = 1) (hgap : ∀ t, 0 < (z' t).1) (hfin : AllLayersFinite eps z)
    (hfin' : AllLayersFinite eps z')
    (hI : I.OrdConnected) (hIcc : Set.Icc 0 (pairKeys z' d / S) ⊆ I)
    (hφ : ∀ x ∈ I, HasDerivWithinAt φ (φ' x) I x)
    (hLip : ∀ x ∈ I, ∀ y ∈ I, |φ' x - φ' y| ≤ L * |x - y|)
    (hδ : 0 < δ) (hφδ : ∀ x ∈ I, δ ≤ φ' x) (hS : 0 < S)
    (hcurve : ∀ t ≤ d, pairKeys z t = φ (pairKeys z' t / S) - φ 0)
    {L_top s Tmax : ℕ} {u Gmax : ℕ → ℝ} (hsd : s ≤ d)
    (hu : ∀ ℓ < L_top, 0 ≤ u ℓ ∧ u ℓ ≤ eps)
    (hΨ : ∀ ℓ < L_top,
      ((Tmax : ℝ) + 1 + 2 * (eps + u ℓ)) * (L / (2 * δ)) * Gmax ℓ / S ≤ u ℓ)
    (hM : ∀ ℓ < L_top, ∀ k, blockPivots eps z' ℓ k 0 < s →
      prefixAffineFeasible (eps - u ℓ) (fun i => pairKeys z' (blockPivots eps z' ℓ k i))
          (layerBlockLen eps z' ℓ k) ∧
        ¬ prefixAffineFeasible (eps + u ℓ) (fun i => pairKeys z' (blockPivots eps z' ℓ k i))
          (layerBlockLen eps z' ℓ k + 1))
    (hT : ∀ ℓ < L_top, ∀ k, blockPivots eps z' ℓ k 0 < s → layerBlockLen eps z' ℓ k ≤ Tmax)
    (hG : ∀ ℓ < L_top, ∀ k, blockPivots eps z' ℓ k 0 < s →
      pairKeys z' (blockPivots eps z' ℓ k (layerBlockLen eps z' ℓ k)) -
        pairKeys z' (blockPivots eps z' ℓ k 0) ≤ Gmax ℓ) :
    ∀ ℓ ≤ L_top, ∀ j, (layerPivot eps z ℓ j ≤ s ∨ layerPivot eps z' ℓ j ≤ s) →
      layerPivot eps z ℓ j = layerPivot eps z' ℓ j := by
  have hy : StrictMono (pairKeys z') := pairKeys_strictMono hgap
  have hpos : ∀ t ≤ d, pairKeys z' t / S ∈ I := by
    intro t ht
    have h0 : pairKeys z' 0 ≤ pairKeys z' t := hy.monotone (Nat.zero_le t)
    rw [pairKeys_zero] at h0
    exact hIcc ⟨div_nonneg h0 hS.le, div_le_div_of_nonneg_right (hy.monotone ht) hS.le⟩
  -- the prefix of `τ + 1` keys of a reference block, all at ranks `≤ d`
  have key : ∀ ℓ < L_top, ∀ k, blockPivots eps z' ℓ k 0 < s → ∀ τ ≤ layerBlockLen eps z' ℓ k,
      blockPivots eps z' ℓ k τ ≤ d →
      (StrictMono fun i => pairKeys z' (blockPivots eps z' ℓ k i)) ∧
      (∀ j ≤ τ, pairKeys z' (blockPivots eps z' ℓ k j) / S ∈ I) ∧
      (∀ j ≤ τ, pairKeys z (blockPivots eps z' ℓ k j) =
        φ (pairKeys z' (blockPivots eps z' ℓ k j) / S) + -φ 0) ∧
      0 ≤ pairKeys z' (blockPivots eps z' ℓ k τ) - pairKeys z' (blockPivots eps z' ℓ k 0) ∧
      pairKeys z' (blockPivots eps z' ℓ k τ) - pairKeys z' (blockPivots eps z' ℓ k 0) ≤
        Gmax ℓ := by
    intro ℓ hℓ k h0 τ hτ hbd
    have hb : StrictMono (blockPivots eps z' ℓ k) := blockPivots_strictMono heps hz' hfin' ℓ k
    have hbd' : ∀ j ≤ τ, blockPivots eps z' ℓ k j ≤ d := fun j hj => (hb.monotone hj).trans hbd
    refine ⟨hy.comp hb, fun j hj => hpos _ (hbd' j hj), fun j hj => ?_,
      sub_nonneg.mpr (hy.monotone (hb.monotone (Nat.zero_le τ))),
      le_trans (sub_le_sub_right (hy.monotone (hb.monotone hτ)) _) (hG ℓ hℓ k h0)⟩
    rw [hcurve _ (hbd' j hj), sub_eq_add_neg]
  refine layerPivot_stable_of_margin heps hz hz' hfin hfin' hM ?_ ?_
  · intro ℓ hℓ k h0 n hn hbn h
    rcases n with _ | τ
    · exact prefixAffineFeasible_zero _ _
    · have hbn' : blockPivots eps z' ℓ k τ ≤ s := by simpa using hbn
      obtain ⟨hp, hpI, hq, hs0, hs1⟩ := key ℓ hℓ k h0 τ (by omega) (hbn'.trans hsd)
      have hT' : (τ : ℝ) + 1 ≤ Tmax := by exact_mod_cast hn.trans (hT ℓ hℓ k h0)
      have hτ0 : (0 : ℝ) ≤ τ := Nat.cast_nonneg τ
      have hu0 := (hu ℓ hℓ).1
      have hue := (hu ℓ hℓ).2
      refine feasible_curved_of_feasible_ref hI hφ hLip hδ hφδ hS hp hpI hq heps ?_ h
      have := curvCost_le (A := (τ : ℝ) + 2 * (eps - u ℓ)) (by linarith) (by linarith)
        hs0 hs1 hS hu0 (hΨ ℓ hℓ)
      linarith
  · intro ℓ hℓ k h0 hbT h
    obtain ⟨hp, hpI, hq, hs0, hs1⟩ := key ℓ hℓ k h0 _ le_rfl (hbT.trans hsd)
    have hT' : (layerBlockLen eps z' ℓ k : ℝ) ≤ Tmax := by exact_mod_cast hT ℓ hℓ k h0
    have hT0 : (0 : ℝ) ≤ layerBlockLen eps z' ℓ k := Nat.cast_nonneg _
    have hu0 := (hu ℓ hℓ).1
    have hue := (hu ℓ hℓ).2
    refine feasible_ref_of_feasible_curved hI hφ hLip hδ hφδ hS hp hpI hq (by linarith) ?_ h
    have := curvCost_le (A := (layerBlockLen eps z' ℓ k : ℝ) + 2 * eps) (by linarith)
      (by linarith) hs0 hs1 hS hu0 (hΨ ℓ hℓ)
    linarith

end Hierarchy

end

end PGM
