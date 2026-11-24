import PLAStochastic.Index.KEP.PivotRestart

/-!
# Pivot counts in a base window and one-layer contraction

Source: `pgm-analysis/research/2026-09-28-kep-additive/count-route.md`, §3.1, the
deterministic step `N_L ≤ N_{L-1} / q + 1` applied to the suffix window.

For a base pair sequence `z` (all counts `1`) let `winCount eps z L a b` be the number of
layer-`L` pivots `layerPivot eps z L j` in the base window `[a, b)`.

* **Window splitting** (`winCount_le_winCount_add`): `[a, b)` splits at `c`.
* **Layer `0`** (`winCount_zero`): the layer-`0` pivots are the base ranks, so the count is
  `b - a`.
* **One-layer contraction** (`winCount_succ_le`): the layer-`(L+1)` pivots in `[a, b)` are
  layer-`L` pivots at block starts `β j`, consecutive block starts are at least
  `q = ⌊2 eps⌋₊ + 1` apart, and every layer-`L` index between `β j₀` and `β j₁` has its pivot
  in `[a, b)` by monotonicity.  Hence
  `winCount eps z (L + 1) a b ≤ winCount eps z L a b / q + 1`.

No finiteness of the window in terms of `N` is used: the statements hold for every base
window of every sequence with finite segments on all layers.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open Classical Finset

variable {eps : ℝ} {z : ℕ → ℝ × ℕ}

/-- Number of layer-`L` pivots in the base window `[a, b)`. -/
def winCount (eps : ℝ) (z : ℕ → ℝ × ℕ) (L a b : ℕ) : ℕ :=
  #{j ∈ range b | a ≤ layerPivot eps z L j ∧ layerPivot eps z L j < b}

/-- The `j`-th layer-`L` pivot has base rank at least `j`. -/
theorem le_layerPivot (heps : 0 ≤ eps) (hz : ∀ t, (z t).2 = 1) (hfin : AllLayersFinite eps z)
    (L j : ℕ) : j ≤ layerPivot eps z L j :=
  le_pairRank (pairLayer_pos heps hfin (fun t => (hz t).ge) L) j

/-- Counting over any index range containing `range b` gives the window count. -/
theorem card_filter_layerPivot_eq_winCount (heps : 0 ≤ eps) (hz : ∀ t, (z t).2 = 1)
    (hfin : AllLayersFinite eps z) (L a : ℕ) {b N : ℕ} (hb : b ≤ N) :
    #{j ∈ range N | a ≤ layerPivot eps z L j ∧ layerPivot eps z L j < b} =
      winCount eps z L a b := by
  unfold winCount
  congr 1
  ext j
  simp only [mem_filter, mem_range]
  constructor
  · rintro ⟨-, h1, h2⟩
    exact ⟨lt_of_le_of_lt (le_layerPivot heps hz hfin L j) h2, h1, h2⟩
  · rintro ⟨hj, h1, h2⟩
    exact ⟨by omega, h1, h2⟩

/-- **Window splitting.** -/
theorem winCount_le_winCount_add (heps : 0 ≤ eps) (hz : ∀ t, (z t).2 = 1)
    (hfin : AllLayersFinite eps z) (L : ℕ) {a c b : ℕ} (hcb : c ≤ b) :
    winCount eps z L a b ≤ winCount eps z L a c + winCount eps z L c b := by
  rw [← card_filter_layerPivot_eq_winCount heps hz hfin L a hcb]
  unfold winCount
  refine (card_le_card fun j hj => ?_).trans (card_union_le _ _)
  simp only [mem_filter, mem_union] at hj ⊢
  by_cases h : layerPivot eps z L j < c
  · exact Or.inl ⟨hj.1, hj.2.1, h⟩
  · exact Or.inr ⟨hj.1, not_lt.1 h, hj.2.2⟩

theorem winCount_mono_left (eps : ℝ) (z : ℕ → ℝ × ℕ) (L : ℕ) {a a' b : ℕ} (h : a ≤ a') :
    winCount eps z L a' b ≤ winCount eps z L a b := by
  unfold winCount
  refine card_le_card fun j hj => ?_
  simp only [mem_filter] at hj ⊢
  exact ⟨hj.1, h.trans hj.2.1, hj.2.2⟩

/-- **Layer `0`.**  The layer-`0` pivots are the base ranks. -/
theorem winCount_zero (eps : ℝ) (hz : ∀ t, (z t).2 = 1) (a b : ℕ) :
    winCount eps z 0 a b = b - a := by
  unfold winCount
  have hset : {j ∈ range b | a ≤ layerPivot eps z 0 j ∧ layerPivot eps z 0 j < b} = Ico a b := by
    ext j
    simp only [mem_filter, mem_range, mem_Ico, layerPivot_zero hz]
    omega
  rw [hset, Nat.card_Ico]

/-- **One-layer contraction.**  With `q = ⌊2 eps⌋₊ + 1`,
    `winCount eps z (L + 1) a b ≤ winCount eps z L a b / q + 1`. -/
theorem winCount_succ_le (heps : 0 ≤ eps) (hz : ∀ t, (z t).2 = 1) (hfin : AllLayersFinite eps z)
    (L a b : ℕ) :
    winCount eps z (L + 1) a b ≤ winCount eps z L a b / (⌊2 * eps⌋₊ + 1) + 1 := by
  set T := {j ∈ range b | a ≤ layerPivot eps z (L + 1) j ∧ layerPivot eps z (L + 1) j < b}
    with hT
  set T' := {j ∈ range b | a ≤ layerPivot eps z L j ∧ layerPivot eps z L j < b} with hT'
  show #T ≤ #T' / (⌊2 * eps⌋₊ + 1) + 1
  rcases T.eq_empty_or_nonempty with h | h
  · rw [h, card_empty]
    exact Nat.zero_le _
  set j₀ := T.min' h
  set j₁ := T.max' h
  have hmem₀ := mem_filter.1 (T.min'_mem h)
  have hmem₁ := mem_filter.1 (T.max'_mem h)
  rw [layerPivot_succ] at hmem₀ hmem₁
  have hle : j₀ ≤ j₁ := T.min'_le _ (T.max'_mem h)
  have hsub : T ⊆ Icc j₀ j₁ := fun j hj => mem_Icc.2 ⟨T.min'_le j hj, T.le_max' j hj⟩
  have hβ := blockStart_add_mul_le heps (hfin L) j₀ (j₁ - j₀)
  rw [Nat.add_sub_cancel' hle] at hβ
  have hmono := layerPivot_mono eps z L
  have hsub' : Icc (blockStart eps (pairLayer eps L z) j₀) (blockStart eps (pairLayer eps L z) j₁)
      ⊆ T' := by
    intro i hi
    rw [mem_Icc] at hi
    have h1 : a ≤ layerPivot eps z L i := hmem₀.2.1.trans (hmono hi.1)
    have h2 : layerPivot eps z L i < b := lt_of_le_of_lt (hmono hi.2) hmem₁.2.2
    exact mem_filter.2 ⟨mem_range.2 (lt_of_le_of_lt (le_layerPivot heps hz hfin L i) h2), h1, h2⟩
  have hcard' : blockStart eps (pairLayer eps L z) j₁ + 1 - blockStart eps (pairLayer eps L z) j₀ ≤
      #T' := by
    have := card_le_card hsub'
    rwa [Nat.card_Icc] at this
  have hq : 0 < ⌊2 * eps⌋₊ + 1 := Nat.succ_pos _
  have hd : j₁ - j₀ ≤ #T' / (⌊2 * eps⌋₊ + 1) := by
    rw [Nat.le_div_iff_mul_le hq, Nat.mul_comm]
    omega
  calc #T ≤ #(Icc j₀ j₁) := card_le_card hsub
    _ = j₁ + 1 - j₀ := Nat.card_Icc _ _
    _ ≤ #T' / (⌊2 * eps⌋₊ + 1) + 1 := by omega

/-- Iterated contraction in real form: `winCount (L+1) ≤ winCount L / q + 1`. -/
theorem winCount_succ_le_real (heps : 0 ≤ eps) (hz : ∀ t, (z t).2 = 1)
    (hfin : AllLayersFinite eps z) (L a b : ℕ) :
    (winCount eps z (L + 1) a b : ℝ) ≤
      (winCount eps z L a b : ℝ) / (⌊2 * eps⌋₊ + 1 : ℝ) + 1 := by
  have h := winCount_succ_le heps hz hfin L a b
  have h1 : ((winCount eps z (L + 1) a b : ℕ) : ℝ) ≤
      ((winCount eps z L a b / (⌊2 * eps⌋₊ + 1) + 1 : ℕ) : ℝ) := by exact_mod_cast h
  have h2 : ((winCount eps z L a b / (⌊2 * eps⌋₊ + 1) : ℕ) : ℝ) ≤
      (winCount eps z L a b : ℝ) / (⌊2 * eps⌋₊ + 1 : ℝ) := by
    have := Nat.cast_div_le (α := ℝ) (m := winCount eps z L a b) (n := ⌊2 * eps⌋₊ + 1)
    push_cast at this
    exact this
  push_cast at h1
  linarith

end

end PGM
