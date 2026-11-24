import PLAStochastic.Index.Algorithm.EndpointHierarchyBounds

/-!
# Causal prefix stability of the endpoint hierarchy

Two endpoint hierarchies are run on the same base-rank set: an actual base pair
sequence `z` and a reference base pair sequence `z'`, both with unit counts, so the
base ranks are the identity and the base keys are `pairKeys z` and `pairKeys z'`.
The layer-`ℓ` base pivots `layerPivot eps z ℓ j` are the base ranks of the layer-`ℓ`
keys, and the layer-`ℓ` keys are the base keys at these pivots
(`pairKeys_pairLayer`).

This file formalizes `ksc:lem:causal-stability` of `proofK_endpoint_scale.tex`:
if every reference block below layer `L` starting before the base rank `s` has a
margin, and the PLA feasibility of its windows ending by `s` transfers between the
two key sequences up to that margin, then the two hierarchies have the same pivots
at every pivot position lying at or before `s` in either hierarchy, through layer
`L` (`layerPivot_stable_of_margin`).  The block crossing `s` (the halo block) is
used only through its prefixes ending by `s`; it prevents the actual hierarchy from
cutting before `s` there.
-/

namespace PGM

noncomputable section

open Classical Finset

/-! ## Pivots, blocks and windows -/

/-- Base pivots of layer `ℓ`: the base rank of the `j`-th layer-`ℓ` key. -/
def layerPivot (eps : ℝ) (z : ℕ → ℝ × ℕ) (ℓ j : ℕ) : ℕ := pairRank (pairLayer eps ℓ z) j

/-- Number of layer-`ℓ` keys in block `k` of layer `ℓ`. -/
def layerBlockLen (eps : ℝ) (z : ℕ → ℝ × ℕ) (ℓ k : ℕ) : ℕ :=
  (pairSegLen eps ((pairShift eps)^[k] (pairLayer eps ℓ z))).toNat

/-- Base pivots of block `k` of layer `ℓ`: `i ↦` the base rank of its `i`-th key. -/
def blockPivots (eps : ℝ) (z : ℕ → ℝ × ℕ) (ℓ k i : ℕ) : ℕ :=
  layerPivot eps z ℓ (blockStart eps (pairLayer eps ℓ z) k + i)

section

variable {eps : ℝ} {z z' : ℕ → ℝ × ℕ}

theorem pairRank_of_unit (hz : ∀ t, (z t).2 = 1) (j : ℕ) : pairRank z j = j := by
  simp [pairRank, hz]

theorem layerPivot_zero (hz : ∀ t, (z t).2 = 1) (j : ℕ) : layerPivot eps z 0 j = j :=
  pairRank_of_unit hz j

theorem layerPivot_succ (eps : ℝ) (z : ℕ → ℝ × ℕ) (ℓ j : ℕ) :
    layerPivot eps z (ℓ + 1) j = layerPivot eps z ℓ (blockStart eps (pairLayer eps ℓ z) j) := by
  unfold layerPivot
  rw [pairLayer_succ, pairRank_layerMap]

theorem layerPivot_mono (eps : ℝ) (z : ℕ → ℝ × ℕ) (ℓ : ℕ) : Monotone (layerPivot eps z ℓ) :=
  pairRank_mono _

/-- The layer-`ℓ` keys are the base keys at the layer-`ℓ` pivots. -/
theorem pairKeys_pairLayer (hz : ∀ t, (z t).2 = 1) :
    ∀ ℓ j, pairKeys (pairLayer eps ℓ z) j = pairKeys z (layerPivot eps z ℓ j)
  | 0, j => by rw [layerPivot_zero hz]; rfl
  | ℓ + 1, j => by
    rw [pairLayer_succ, pairKeys_layerMap, pairKeys_pairLayer hz ℓ, layerPivot_succ]

theorem pairKeys_shift (w : ℕ → ℝ × ℕ) (a i : ℕ) :
    pairKeys (fun t => w (a + t)) i = pairKeys w (a + i) - pairKeys w a := by
  simp only [pairKeys]
  rw [sum_range_add]
  ring

/-- On a sequence with finite segments, a prefix of block `k` is feasible exactly
    when it is not longer than the block. -/
theorem feasible_block_iff {w : ℕ → ℝ × ℕ} (hfin : AllSegmentsFinite eps w) (k n : ℕ) :
    prefixAffineFeasible eps (fun i => pairKeys w (blockStart eps w k + i)) n ↔
      n ≤ (pairSegLen eps ((pairShift eps)^[k] w)).toNat := by
  have hshift : pairKeys ((pairShift eps)^[k] w) =
      fun i => 1 * pairKeys w (blockStart eps w k + i) + -pairKeys w (blockStart eps w k) := by
    rw [pairShift_iterate]
    funext i
    rw [pairKeys_shift]
    ring
  obtain ⟨T, hT⟩ := ENat.ne_top_iff_exists.mp (hfin k)
  cases n with
  | zero => simp [prefixAffineFeasible_zero]
  | succ t =>
    have h1 : prefixAffineFeasible eps (pairKeys ((pairShift eps)^[k] w)) (t + 1) ↔
        prefixAffineFeasible eps (fun i => pairKeys w (blockStart eps w k + i)) (t + 1) := by
      rw [hshift]
      exact prefixAffineFeasible_affine_iff one_ne_zero
    rw [← h1, ← lt_segLen_iff]
    change (t : ℕ∞) < pairSegLen eps _ ↔ _
    rw [← hT, ENat.toNat_natCast, Nat.cast_lt]
    omega

/-- With nonnegative threshold and finite segments, the pivots of every layer are
    strictly increasing. -/
theorem layerPivot_strictMono (heps : 0 ≤ eps) (hz : ∀ t, (z t).2 = 1)
    (hfin : AllLayersFinite eps z) (ℓ : ℕ) : StrictMono (layerPivot eps z ℓ) := by
  have hpos := pairLayer_pos heps hfin (fun t => (hz t).ge) ℓ
  refine strictMono_nat_of_lt_succ fun j => ?_
  have := hpos j
  simp only [layerPivot, pairRank, sum_range_succ]
  omega

/-! ## One layer -/

/-- **One layer of the stability argument.**  If the layer-`ℓ` pivots of the two
    hierarchies agree wherever one of them is at most `s`, and the reference blocks
    of layer `ℓ` starting before `s` satisfy the window transfer `hA`/`hB` for the
    actual base keys, then the layer-`ℓ` block starts agree wherever one of the two
    start pivots is at most `s`. -/
theorem blockStart_eq_of_layerPivot (heps : 0 ≤ eps) (hz : ∀ t, (z t).2 = 1)
    (hz' : ∀ t, (z' t).2 = 1) (hfin : AllLayersFinite eps z) (hfin' : AllLayersFinite eps z')
    {ℓ s : ℕ}
    (IH : ∀ j, (layerPivot eps z ℓ j ≤ s ∨ layerPivot eps z' ℓ j ≤ s) →
      layerPivot eps z ℓ j = layerPivot eps z' ℓ j)
    (hA : ∀ k, blockPivots eps z' ℓ k 0 < s → ∀ n ≤ layerBlockLen eps z' ℓ k,
      blockPivots eps z' ℓ k (n - 1) ≤ s →
      prefixAffineFeasible eps (fun i => pairKeys z (blockPivots eps z' ℓ k i)) n)
    (hB : ∀ k, blockPivots eps z' ℓ k 0 < s →
      blockPivots eps z' ℓ k (layerBlockLen eps z' ℓ k) ≤ s →
      ¬ prefixAffineFeasible eps (fun i => pairKeys z (blockPivots eps z' ℓ k i))
        (layerBlockLen eps z' ℓ k + 1)) :
    ∀ k, (layerPivot eps z ℓ (blockStart eps (pairLayer eps ℓ z) k) ≤ s ∨
        layerPivot eps z' ℓ (blockStart eps (pairLayer eps ℓ z') k) ≤ s) →
      blockStart eps (pairLayer eps ℓ z) k = blockStart eps (pairLayer eps ℓ z') k
  | 0, _ => by simp [blockStart]
  | k + 1, hk => by
    have hPs : StrictMono (layerPivot eps z ℓ) := layerPivot_strictMono heps hz hfin ℓ
    have hP's : StrictMono (layerPivot eps z' ℓ) := layerPivot_strictMono heps hz' hfin' ℓ
    have hPm : Monotone (layerPivot eps z ℓ) := hPs.monotone
    have hP'm : Monotone (layerPivot eps z' ℓ) := hP's.monotone
    have hβ : blockStart eps (pairLayer eps ℓ z) k = blockStart eps (pairLayer eps ℓ z') k :=
      blockStart_eq_of_layerPivot heps hz hz' hfin hfin' IH hA hB k
        (hk.imp (le_trans (hPm (blockStart_mono eps _ k.le_succ)))
          (le_trans (hP'm (blockStart_mono eps _ k.le_succ))))
    obtain ⟨β, hβdef⟩ : ∃ β, blockStart eps (pairLayer eps ℓ z') k = β := ⟨_, rfl⟩
    obtain ⟨T, hTdef⟩ :
        ∃ T, (pairSegLen eps ((pairShift eps)^[k] (pairLayer eps ℓ z))).toNat = T := ⟨_, rfl⟩
    obtain ⟨T', hT'def⟩ : ∃ T', layerBlockLen eps z' ℓ k = T' := ⟨_, rfl⟩
    have hT1 : 1 ≤ T := hTdef ▸ one_le_toNat_pairSegLen heps (hfin ℓ k)
    have hT'1 : 1 ≤ T' := hT'def ▸ one_le_toNat_pairSegLen heps (hfin' ℓ k)
    have hE : blockStart eps (pairLayer eps ℓ z) (k + 1) = β + T := by
      rw [blockStart_succ, hβ, hβdef, hTdef]
    have hE' : blockStart eps (pairLayer eps ℓ z') (k + 1) = β + T' := by
      rw [blockStart_succ, hβdef, ← hT'def]
      rfl
    have hb : ∀ i, blockPivots eps z' ℓ k i = layerPivot eps z' ℓ (β + i) := by
      intro i
      rw [← hβdef]
      rfl
    -- the actual block: feasibility of its prefixes
    have hfeas : ∀ n, prefixAffineFeasible eps
        (fun i => pairKeys (pairLayer eps ℓ z) (β + i)) n ↔ n ≤ T := by
      intro n
      rw [← hTdef, ← hβdef, ← hβ]
      exact feasible_block_iff (hfin ℓ) k n
    -- the actual keys of the block are the actual base keys at the reference pivots
    have hkey : ∀ n, (∀ i < n, layerPivot eps z ℓ (β + i) ≤ s ∨
          layerPivot eps z' ℓ (β + i) ≤ s) →
        (prefixAffineFeasible eps (fun i => pairKeys (pairLayer eps ℓ z) (β + i)) n ↔
          prefixAffineFeasible eps (fun i => pairKeys z (blockPivots eps z' ℓ k i)) n) := by
      intro n hn
      apply prefixAffineFeasible_congr
      intro i hi
      rw [pairKeys_pairLayer hz, hb, IH _ (hn i hi)]
    rw [hE, hE'] at hk ⊢
    -- the reference block starts before `s`
    have h0 : blockPivots eps z' ℓ k 0 < s := by
      rw [hb, add_zero]
      rcases hk with h | h
      · have h' : layerPivot eps z ℓ β < s := (hPs (by omega : β < β + T)).trans_le h
        rw [← IH β (Or.inl h'.le)]
        exact h'
      · exact (hP's (by omega : β < β + T')).trans_le h
    by_cases hc : layerPivot eps z' ℓ (β + T') ≤ s
    · -- the reference block ends by `s`: the actual block ends at the same pivot
      have hle : ∀ i ≤ T', layerPivot eps z' ℓ (β + i) ≤ s :=
        fun i hi => (hP'm (Nat.add_le_add_left hi β)).trans hc
      have h1 : T' ≤ T := by
        have hx := hA k h0 T' hT'def.ge (by rw [hb]; exact hle _ (Nat.sub_le T' 1))
        rw [← hT'def] at hx
        rw [← hfeas, hkey T' (fun i hi => Or.inr (hle i hi.le))]
        rwa [hT'def] at hx
      have h2 : T ≤ T' := by
        have hx := hB k h0 (by rw [hb, hT'def]; exact hc)
        rw [hT'def] at hx
        have : ¬ T' + 1 ≤ T := by
          rw [← hfeas, hkey (T' + 1) (fun i hi => Or.inr (hle i (by omega)))]
          exact hx
        omega
      omega
    · -- the reference block crosses `s` (the halo): the actual block cannot end by `s`
      exfalso
      have hs : layerPivot eps z ℓ (β + T) ≤ s := hk.resolve_right hc
      have hTT : T + 1 ≤ T' := by
        by_contra hTT
        apply hc
        rw [IH _ (Or.inl hs)] at hs
        exact (hP'm (by omega)).trans hs
      have hx := hA k h0 (T + 1) (by rw [hT'def]; exact hTT)
        (by rw [hb, Nat.add_sub_cancel, ← IH _ (Or.inl hs)]; exact hs)
      rw [← hkey (T + 1) (fun i hi => Or.inl ((hPm (by omega)).trans hs)), hfeas] at hx
      omega

/-! ## All layers -/

/-- **Prefix stability, window-transfer form.**  Suppose that for every layer
    `ℓ < L` and every reference layer-`ℓ` block `k` starting before `s` (with block
    length `T = layerBlockLen eps z' ℓ k` and base pivots `b = blockPivots eps z' ℓ k`):
    `hA` every prefix of length `n ≤ T` ending by `s` is `eps`-feasible for the actual
    base keys at `b`, and `hB` if the block ends by `s`, its prefix of length `T + 1`
    is `eps`-infeasible for the actual base keys at `b`.  Then through layer `L`, the
    two hierarchies have the same pivot at every position where one of them has a
    pivot at or before `s`. -/
theorem layerPivot_stable (heps : 0 ≤ eps) (hz : ∀ t, (z t).2 = 1)
    (hz' : ∀ t, (z' t).2 = 1) (hfin : AllLayersFinite eps z) (hfin' : AllLayersFinite eps z')
    {L s : ℕ}
    (hA : ∀ ℓ < L, ∀ k, blockPivots eps z' ℓ k 0 < s → ∀ n ≤ layerBlockLen eps z' ℓ k,
      blockPivots eps z' ℓ k (n - 1) ≤ s →
      prefixAffineFeasible eps (fun i => pairKeys z (blockPivots eps z' ℓ k i)) n)
    (hB : ∀ ℓ < L, ∀ k, blockPivots eps z' ℓ k 0 < s →
      blockPivots eps z' ℓ k (layerBlockLen eps z' ℓ k) ≤ s →
      ¬ prefixAffineFeasible eps (fun i => pairKeys z (blockPivots eps z' ℓ k i))
        (layerBlockLen eps z' ℓ k + 1)) :
    ∀ ℓ ≤ L, ∀ j, (layerPivot eps z ℓ j ≤ s ∨ layerPivot eps z' ℓ j ≤ s) →
      layerPivot eps z ℓ j = layerPivot eps z' ℓ j
  | 0, _, j, _ => by rw [layerPivot_zero hz, layerPivot_zero hz']
  | ℓ + 1, hℓ, j, hj => by
    have IH := layerPivot_stable heps hz hz' hfin hfin' hA hB ℓ (by omega)
    rw [layerPivot_succ, layerPivot_succ] at hj ⊢
    have hbs := blockStart_eq_of_layerPivot heps hz hz' hfin hfin' IH (hA ℓ (by omega))
      (hB ℓ (by omega)) j hj
    rw [hbs] at hj ⊢
    exact IH _ hj

/-- **Causal prefix stability** (`ksc:lem:causal-stability`).  For every layer
    `ℓ < L` and every reference layer-`ℓ` block `k` starting before `s`, with block
    length `T = layerBlockLen eps z' ℓ k` and base pivots `b = blockPivots eps z' ℓ k`,
    let `Wx θ r` (resp. `Wy θ r`) be the `θ`-feasibility of the first `r` actual
    (resp. reference) base keys at `b`.  Assume
    * (M) the margin `u ℓ`: `Wy (eps - u ℓ) T` and `¬ Wy (eps + u ℓ) (T + 1)`;
    * (A) for `n ≤ T` with `b (n - 1) ≤ s`: `Wy (eps - u ℓ) n → Wx eps n`;
    * (B) if `b T ≤ s`: `Wx eps (T + 1) → Wy (eps + u ℓ) (T + 1)`.
    Then for all `ℓ ≤ L` and `j`, if `layerPivot eps z ℓ j ≤ s` or
    `layerPivot eps z' ℓ j ≤ s`, the two pivots are equal. -/
theorem layerPivot_stable_of_margin (heps : 0 ≤ eps) (hz : ∀ t, (z t).2 = 1)
    (hz' : ∀ t, (z' t).2 = 1) (hfin : AllLayersFinite eps z) (hfin' : AllLayersFinite eps z')
    {L s : ℕ} {u : ℕ → ℝ}
    (hM : ∀ ℓ < L, ∀ k, blockPivots eps z' ℓ k 0 < s →
      prefixAffineFeasible (eps - u ℓ) (fun i => pairKeys z' (blockPivots eps z' ℓ k i))
          (layerBlockLen eps z' ℓ k) ∧
        ¬ prefixAffineFeasible (eps + u ℓ) (fun i => pairKeys z' (blockPivots eps z' ℓ k i))
          (layerBlockLen eps z' ℓ k + 1))
    (hA : ∀ ℓ < L, ∀ k, blockPivots eps z' ℓ k 0 < s → ∀ n ≤ layerBlockLen eps z' ℓ k,
      blockPivots eps z' ℓ k (n - 1) ≤ s →
      prefixAffineFeasible (eps - u ℓ) (fun i => pairKeys z' (blockPivots eps z' ℓ k i)) n →
      prefixAffineFeasible eps (fun i => pairKeys z (blockPivots eps z' ℓ k i)) n)
    (hB : ∀ ℓ < L, ∀ k, blockPivots eps z' ℓ k 0 < s →
      blockPivots eps z' ℓ k (layerBlockLen eps z' ℓ k) ≤ s →
      prefixAffineFeasible eps (fun i => pairKeys z (blockPivots eps z' ℓ k i))
          (layerBlockLen eps z' ℓ k + 1) →
      prefixAffineFeasible (eps + u ℓ) (fun i => pairKeys z' (blockPivots eps z' ℓ k i))
          (layerBlockLen eps z' ℓ k + 1)) :
    ∀ ℓ ≤ L, ∀ j, (layerPivot eps z ℓ j ≤ s ∨ layerPivot eps z' ℓ j ≤ s) →
      layerPivot eps z ℓ j = layerPivot eps z' ℓ j :=
  layerPivot_stable heps hz hz' hfin hfin'
    (fun ℓ hℓ k h0 n hn hbn =>
      hA ℓ hℓ k h0 n hn hbn (prefixAffineFeasible_mono (hM ℓ hℓ k h0).1 hn))
    (fun ℓ hℓ k h0 hbT hx => (hM ℓ hℓ k h0).2 (hB ℓ hℓ k h0 hbT hx))

end

end

end PGM
