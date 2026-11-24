import PLAStochastic.Index.Algorithm.Segmentation
import PLAStochastic.ForMathlib.Probability.Process.IIDRegeneration

/-!
# The endpoint hierarchy (ALG-PGM): finite run and infinite layer structure

`epLayer eps p n ℓ` is layer `ℓ` of ALG-PGM on the keys `p 0, …, p (n-1)`:
the keys of the layer and their number.  Layer `ℓ + 1` consists of the first keys
of the ALG-OPT segments of layer `ℓ`.  `epHeight` is the first layer `ℓ ≥ 1`
with a single key.

For the probabilistic analysis the same hierarchy is run on an infinite gap
sequence.  A layer is a sequence of pairs `(gap, count)`: `count` is the number
of input gaps spanned by one layer gap.  `layerMap` aggregates the pairs over the
ALG-OPT segments of the layer keys; it is written through `shiftBy` so that the
regeneration theorems of `PLAStochastic.ForMathlib.Probability.Process.IIDRegeneration` apply to it directly.

The main result `epHeight_eq` identifies the finite height with the first layer
whose leading hyper-segment spans at least `n` input ranks, provided every
segment of every infinite layer is finite (a probability-one event).
-/

namespace PGM

noncomputable section

open Classical Finset

/-! ## Initial segments and counts -/

theorem count_eq_find_of_downward {P : ℕ → Prop} [DecidablePred P]
    (hdown : ∀ j, P (j + 1) → P j) {m : ℕ} (hm : ¬ P m) :
    Nat.count P m = Nat.find (⟨m, hm⟩ : ∃ j, ¬ P j) := by
  set k := Nat.find (⟨m, hm⟩ : ∃ j, ¬ P j) with hk
  have hkm : k ≤ m := Nat.find_min' _ hm
  have hbelow : ∀ j < k, P j := fun j hj => not_not.mp (Nat.find_min _ hj)
  have habove : ∀ j, k ≤ j → ¬ P j := by
    intro j hj hPj
    have hdown' : ∀ i, P (k + i) → P k := by
      intro i
      induction i with
      | zero => exact id
      | succ i ih => exact fun h => ih (hdown _ h)
    exact Nat.find_spec (⟨m, hm⟩ : ∃ j, ¬ P j) (hdown' (j - k) (by rwa [Nat.add_sub_cancel' hj]))
  rw [Nat.count_eq_card_filter_range]
  have : (range m).filter P = range k := by
    ext j
    simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨_, hP⟩
      by_contra hc
      exact habove j (not_lt.mp hc) hP
    · intro hj
      exact ⟨lt_of_lt_of_le hj hkm, hbelow j hj⟩
  rw [this, card_range]

/-! ## The finite ALG-PGM run -/

/-- Layer `ℓ` of ALG-PGM on `p 0, …, p (n-1)`: its keys and its number of keys. -/
def epLayer (eps : ℝ) (p : ℕ → ℝ) (n : ℕ) : ℕ → (ℕ → ℝ) × ℕ
  | 0 => (p, n)
  | ℓ + 1 =>
    ((fun j => (epLayer eps p n ℓ).1 (finCut eps (epLayer eps p n ℓ).1 (epLayer eps p n ℓ).2 j)),
      finSegCount eps (epLayer eps p n ℓ).1 (epLayer eps p n ℓ).2)

/-- The height of ALG-PGM: the first layer `ℓ ≥ 1` with one key. -/
def epHeight (eps : ℝ) (p : ℕ → ℝ) (n : ℕ) : ℕ :=
  sInf {ℓ | 1 ≤ ℓ ∧ (epLayer eps p n ℓ).2 = 1}

/-! ## Layers of pair sequences -/

/-- Keys of a pair sequence: partial sums of the gap components. -/
def pairKeys (z : ℕ → ℝ × ℕ) : ℕ → ℝ := fun t => ∑ s ∈ range t, (z s).1

/-- Input ranks of a pair sequence: partial sums of the count components. -/
def pairRank (z : ℕ → ℝ × ℕ) : ℕ → ℕ := fun t => ∑ s ∈ range t, (z s).2

/-- The first ALG-OPT segment length of the layer keys. -/
def pairSegLen (eps : ℝ) (z : ℕ → ℝ × ℕ) : ℕ∞ := segLen eps (pairKeys z)

/-- Restart after the first segment. -/
def pairShift (eps : ℝ) : (ℕ → ℝ × ℕ) → (ℕ → ℝ × ℕ) := shiftBy (pairSegLen eps)

/-- The aggregated pair of the first segment. -/
def firstBlock (eps : ℝ) (z : ℕ → ℝ × ℕ) : ℝ × ℕ :=
  ∑ t ∈ range (pairSegLen eps z).toNat, z t

/-- One layer of the endpoint hierarchy on pair sequences. -/
def layerMap (eps : ℝ) (z : ℕ → ℝ × ℕ) : ℕ → ℝ × ℕ :=
  fun j => firstBlock eps ((pairShift eps)^[j] z)

/-- Layer `ℓ` of the infinite endpoint hierarchy. -/
def pairLayer (eps : ℝ) (ℓ : ℕ) (z : ℕ → ℝ × ℕ) : ℕ → ℝ × ℕ := (layerMap eps)^[ℓ] z

/-- Start of the `j`-th segment of a pair sequence (in layer indices). -/
def blockStart (eps : ℝ) (z : ℕ → ℝ × ℕ) (j : ℕ) : ℕ :=
  ∑ i ∈ range j, (pairSegLen eps ((pairShift eps)^[i] z)).toNat

/-- All segments of the pair sequence are finite. -/
def AllSegmentsFinite (eps : ℝ) (z : ℕ → ℝ × ℕ) : Prop :=
  ∀ j, pairSegLen eps ((pairShift eps)^[j] z) ≠ ⊤

/-- All segments of all layers are finite. -/
def AllLayersFinite (eps : ℝ) (z : ℕ → ℝ × ℕ) : Prop :=
  ∀ ℓ, AllSegmentsFinite eps (pairLayer eps ℓ z)

theorem blockStart_succ (eps : ℝ) (z : ℕ → ℝ × ℕ) (j : ℕ) :
    blockStart eps z (j + 1) =
      blockStart eps z j + (pairSegLen eps ((pairShift eps)^[j] z)).toNat := by
  simp [blockStart, sum_range_succ]

theorem pairShift_iterate (eps : ℝ) (z : ℕ → ℝ × ℕ) :
    ∀ j, (pairShift eps)^[j] z = fun t => z (blockStart eps z j + t)
  | 0 => by funext t; simp [blockStart]
  | j + 1 => by
    have key : ∀ u, (pairShift eps)^[j] z u = z (blockStart eps z j + u) :=
      fun u => congrFun (pairShift_iterate eps z j) u
    rw [Function.iterate_succ_apply']
    funext t
    show (pairShift eps)^[j] z ((pairSegLen eps ((pairShift eps)^[j] z)).toNat + t) = _
    rw [key, blockStart_succ, add_assoc]

theorem blockStart_mono (eps : ℝ) (z : ℕ → ℝ × ℕ) : Monotone (blockStart eps z) :=
  monotone_nat_of_le_succ fun j => by rw [blockStart_succ]; omega

theorem layerMap_apply (eps : ℝ) (z : ℕ → ℝ × ℕ) (j : ℕ) :
    layerMap eps z j = ∑ t ∈ Ico (blockStart eps z j) (blockStart eps z (j + 1)), z t := by
  simp only [layerMap, firstBlock]
  rw [blockStart_succ, sum_Ico_eq_sum_range, Nat.add_sub_cancel_left,
    pairShift_iterate eps z j]

/-- Block sums telescope along monotone block boundaries. -/
theorem sum_blocks {M : Type*} [AddCommMonoid M] (f : ℕ → M) (b : ℕ → ℕ) (hb0 : b 0 = 0)
    (hb : Monotone b) : ∀ j, ∑ i ∈ range j, ∑ t ∈ Ico (b i) (b (i + 1)), f t =
      ∑ t ∈ range (b j), f t
  | 0 => by simp [hb0]
  | j + 1 => by
    rw [sum_range_succ, sum_blocks f b hb0 hb j, sum_range_add_sum_Ico _ (hb (Nat.le_succ j))]

theorem pairRank_layerMap (eps : ℝ) (z : ℕ → ℝ × ℕ) (j : ℕ) :
    pairRank (layerMap eps z) j = pairRank z (blockStart eps z j) := by
  simp only [pairRank, layerMap_apply, Prod.snd_sum]
  exact sum_blocks (fun t => (z t).2) _ (by simp [blockStart]) (blockStart_mono eps z) j

theorem pairKeys_layerMap (eps : ℝ) (z : ℕ → ℝ × ℕ) (j : ℕ) :
    pairKeys (layerMap eps z) j = pairKeys z (blockStart eps z j) := by
  simp only [pairKeys, layerMap_apply, Prod.fst_sum]
  exact sum_blocks (fun t => (z t).1) _ (by simp [blockStart]) (blockStart_mono eps z) j

/-- The keys seen from index `a` are a translate of the keys of the shifted pairs. -/
theorem shiftSeq_pairKeys (z : ℕ → ℝ × ℕ) (c : ℝ) (a : ℕ) :
    shiftSeq (fun t => c + pairKeys z t) a =
      fun i => 1 * pairKeys (fun t => z (a + t)) i + (c + pairKeys z a) := by
  funext i
  simp only [shiftSeq_apply, pairKeys, one_mul]
  rw [sum_range_add]
  ring

theorem segLen_shift_pairKeys (eps : ℝ) (z : ℕ → ℝ × ℕ) (c : ℝ) (a : ℕ) :
    segLen eps (shiftSeq (fun t => c + pairKeys z t) a) =
      pairSegLen eps (fun t => z (a + t)) := by
  rw [shiftSeq_pairKeys, segLen_affine one_ne_zero]
  rfl

/-- On a sequence with finite segments, the infinite ALG-OPT cuts of the keys
    (with any offset) are the block starts. -/
theorem cut_pairKeys (eps : ℝ) {z : ℕ → ℝ × ℕ} (hfin : AllSegmentsFinite eps z) (c : ℝ) :
    ∀ j, cut eps (fun t => c + pairKeys z t) j = (blockStart eps z j : ℕ∞)
  | 0 => by simp [cut, blockStart]
  | j + 1 => by
    rw [cut, cut_pairKeys eps hfin c j, ENat.toNat_natCast, segLen_shift_pairKeys,
      blockStart_succ, ← pairShift_iterate eps z j, Nat.cast_add,
      ENat.natCast_toNat (hfin j)]

/-! ## Monotonicity of block starts and ranks -/

theorem one_le_toNat_pairSegLen {eps : ℝ} (heps : 0 ≤ eps) {z : ℕ → ℝ × ℕ}
    (h : pairSegLen eps z ≠ ⊤) : 1 ≤ (pairSegLen eps z).toNat := by
  have h1 : (1 : ℕ∞) ≤ pairSegLen eps z := one_le_segLen heps _
  rw [← ENat.natCast_toNat h] at h1
  exact_mod_cast h1

theorem le_blockStart {eps : ℝ} (heps : 0 ≤ eps) {z : ℕ → ℝ × ℕ}
    (hfin : AllSegmentsFinite eps z) : ∀ j, j ≤ blockStart eps z j
  | 0 => Nat.zero_le _
  | j + 1 => by
    rw [blockStart_succ]
    have := one_le_toNat_pairSegLen heps (hfin j)
    have := le_blockStart heps hfin j
    omega

theorem blockStart_lt_succ {eps : ℝ} (heps : 0 ≤ eps) {z : ℕ → ℝ × ℕ}
    (hfin : AllSegmentsFinite eps z) (j : ℕ) : blockStart eps z j < blockStart eps z (j + 1) := by
  rw [blockStart_succ]
  have := one_le_toNat_pairSegLen heps (hfin j)
  omega

/-- Counts stay positive through a layer. -/
theorem one_le_layerMap_snd {eps : ℝ} (heps : 0 ≤ eps) {z : ℕ → ℝ × ℕ}
    (hfin : AllSegmentsFinite eps z) (hpos : ∀ t, 1 ≤ (z t).2) (j : ℕ) :
    1 ≤ (layerMap eps z j).2 := by
  rw [layerMap_apply, Prod.snd_sum]
  have hmem : blockStart eps z j ∈ Ico (blockStart eps z j) (blockStart eps z (j + 1)) :=
    mem_Ico.2 ⟨le_rfl, blockStart_lt_succ heps hfin j⟩
  exact (hpos (blockStart eps z j)).trans
    (single_le_sum (f := fun t => (z t).2) (fun t _ => Nat.zero_le _) hmem)

theorem pairRank_zero (z : ℕ → ℝ × ℕ) : pairRank z 0 = 0 := by simp [pairRank]

theorem pairRank_one (z : ℕ → ℝ × ℕ) : pairRank z 1 = (z 0).2 := by simp [pairRank]

theorem pairRank_mono (z : ℕ → ℝ × ℕ) : Monotone (pairRank z) :=
  monotone_nat_of_le_succ fun j => by simp [pairRank, sum_range_succ]

theorem le_pairRank {z : ℕ → ℝ × ℕ} (hpos : ∀ t, 1 ≤ (z t).2) : ∀ j, j ≤ pairRank z j
  | 0 => Nat.zero_le _
  | j + 1 => by
    have := le_pairRank hpos j
    have := hpos j
    simp only [pairRank, sum_range_succ] at *
    omega

/-- Monotone ranks: the first index reaching `n` splits the ranks below/above `n`. -/
theorem le_iff_find_le {R : ℕ → ℕ} (hR : Monotone R) {n : ℕ} (hex : ∃ j, n ≤ R j) (i : ℕ) :
    n ≤ R i ↔ Nat.find hex ≤ i :=
  ⟨fun h => Nat.find_min' hex h, fun h => (Nat.find_spec hex).trans (hR h)⟩

/-! ## The finite run follows the infinite layers -/

section Input

variable {eps : ℝ} {z : ℕ → ℝ × ℕ}

theorem pairLayer_succ (eps : ℝ) (ℓ : ℕ) (z : ℕ → ℝ × ℕ) :
    pairLayer eps (ℓ + 1) z = layerMap eps (pairLayer eps ℓ z) :=
  Function.iterate_succ_apply' _ _ _

theorem pairLayer_pos (heps : 0 ≤ eps) (hfin : AllLayersFinite eps z)
    (hpos : ∀ t, 1 ≤ (z t).2) : ∀ ℓ t, 1 ≤ (pairLayer eps ℓ z t).2
  | 0, t => hpos t
  | ℓ + 1, t => by
    rw [pairLayer_succ]
    exact one_le_layerMap_snd heps (hfin ℓ) (pairLayer_pos heps hfin hpos ℓ) t

theorem exists_le_pairRank (hpos : ∀ t, 1 ≤ (z t).2) (n : ℕ) : ∃ j, n ≤ pairRank z j :=
  ⟨n, le_pairRank hpos n⟩

/-- The finite ALG-PGM layers are read off from the infinite pair layers. -/
theorem epLayer_spec (heps : 0 ≤ eps) (hfin : AllLayersFinite eps z)
    (hpos : ∀ t, 1 ≤ (z t).2) (hrank0 : ∀ j, pairRank z j = j) (x0 : ℝ) (n : ℕ) :
    ∀ ℓ, ∃ hex : ∃ j, n ≤ pairRank (pairLayer eps ℓ z) j,
      (epLayer eps (fun t => x0 + pairKeys z t) n ℓ).2 = Nat.find hex ∧
      ∀ j < Nat.find hex,
        (epLayer eps (fun t => x0 + pairKeys z t) n ℓ).1 j = x0 + pairKeys (pairLayer eps ℓ z) j
  | 0 => by
    have hex : ∃ j, n ≤ pairRank (pairLayer eps 0 z) j := ⟨n, by simp [pairLayer, hrank0]⟩
    refine ⟨hex, ?_, fun j _ => rfl⟩
    show n = Nat.find hex
    have e : ∀ j, pairRank (pairLayer eps 0 z) j = j := fun j => hrank0 j
    apply le_antisymm
    · have := Nat.find_spec hex
      rw [e] at this
      exact this
    · exact Nat.find_min' hex (by rw [e])
  | ℓ + 1 => by
    obtain ⟨hex, hK, hq⟩ := epLayer_spec heps hfin hpos hrank0 x0 n ℓ
    set w := pairLayer eps ℓ z with hw
    set q := (epLayer eps (fun t => x0 + pairKeys z t) n ℓ).1 with hqdef
    set K := (epLayer eps (fun t => x0 + pairKeys z t) n ℓ).2 with hKdef
    have hwpos : ∀ t, 1 ≤ (w t).2 := pairLayer_pos heps hfin hpos ℓ
    have hRmono : Monotone (pairRank w) := pairRank_mono w
    have hsplit : ∀ i, n ≤ pairRank w i ↔ K ≤ i := by
      intro i; rw [hK]; exact le_iff_find_le hRmono hex i
    set b := blockStart eps w with hb
    have hbmono : Monotone b := blockStart_mono eps w
    have hbge : ∀ j, j ≤ b j := le_blockStart heps (hfin ℓ)
    -- the finite cuts are the block starts truncated at `K`
    have hcut : ∀ j, finCut eps q K j = min (b j) K := by
      intro j
      have h1 : finCut eps q K j = finCut eps (fun t => x0 + pairKeys w t) K j :=
        finCut_congr (fun i hi => hq i (by rw [← hK]; exact hi)) j
      have h2 := finCut_eq_min eps (fun t => x0 + pairKeys w t) K j
      rw [cut_pairKeys eps (hfin ℓ) x0 j] at h2
      rw [h1]
      rcases le_total (b j) K with hle | hle
      · rw [min_eq_left (by exact_mod_cast hle)] at h2
        rw [min_eq_left hle]; exact_mod_cast h2
      · rw [min_eq_right (by exact_mod_cast hle)] at h2
        rw [min_eq_right hle]; exact_mod_cast h2
    have hex' : ∃ j, n ≤ pairRank (pairLayer eps (ℓ + 1) z) j :=
      exists_le_pairRank (pairLayer_pos heps hfin hpos (ℓ + 1)) n
    have hRsucc : ∀ j, pairRank (pairLayer eps (ℓ + 1) z) j = pairRank w (b j) := by
      intro j; rw [pairLayer_succ, pairRank_layerMap]
    -- the new count
    have hfind : ∀ j, (n ≤ pairRank (pairLayer eps (ℓ + 1) z) j ↔ K ≤ b j) := by
      intro j; rw [hRsucc, hsplit]
    refine ⟨hex', ?_, ?_⟩
    · show finSegCount eps q K = Nat.find hex'
      unfold finSegCount
      have hpred : (fun j => finCut eps q K j < K) = fun j => b j < K := by
        funext j; rw [hcut]; exact propext ⟨fun h => by omega, fun h => by omega⟩
      simp only [hpred]
      have hnot : ¬ b (K + 1) < K := by have := hbge (K + 1); omega
      rw [count_eq_find_of_downward (fun j hj => lt_of_le_of_lt (hbmono (Nat.le_succ j)) hj) hnot]
      apply le_antisymm
      · exact Nat.find_min' _ (not_lt.mpr ((hfind _).1 (Nat.find_spec hex')))
      · exact Nat.find_min' _ ((hfind _).2 (not_lt.mp (Nat.find_spec
          (⟨K + 1, hnot⟩ : ∃ j, ¬ b j < K))))
    · intro j hj
      have hbj : b j < K := by
        by_contra hc
        exact (not_le.mpr hj) (Nat.find_min' hex' ((hfind j).2 (not_lt.mp hc)))
      show q (finCut eps q K j) = _
      rw [hcut, min_eq_left hbj.le, hq _ (by rw [← hK]; exact hbj), pairLayer_succ,
        pairKeys_layerMap]

/-- **Height identity.**  If every segment of every infinite layer is finite, the
    height of ALG-PGM on the first `n ≥ 1` keys is the first layer `ℓ ≥ 1` whose
    leading hyper-segment spans at least `n` input gaps. -/
theorem epHeight_eq (heps : 0 ≤ eps) (hfin : AllLayersFinite eps z)
    (hpos : ∀ t, 1 ≤ (z t).2) (hrank0 : ∀ j, pairRank z j = j) (x0 : ℝ) {n : ℕ}
    (hn : 1 ≤ n) :
    epHeight eps (fun t => x0 + pairKeys z t) n =
      sInf {ℓ | 1 ≤ ℓ ∧ n ≤ (pairLayer eps ℓ z 0).2} := by
  unfold epHeight
  congr 1
  ext ℓ
  simp only [Set.mem_ofPred_eq]
  obtain ⟨hex, hK, -⟩ := epLayer_spec heps hfin hpos hrank0 x0 n ℓ
  rw [hK, ← pairRank_one]
  have h0 : ¬ n ≤ pairRank (pairLayer eps ℓ z) 0 := by rw [pairRank_zero]; omega
  constructor
  · rintro ⟨h1, hf⟩
    refine ⟨h1, ?_⟩
    have := Nat.find_spec hex
    rwa [hf] at this
  · rintro ⟨h1, hr⟩
    refine ⟨h1, le_antisymm (Nat.find_min' hex hr) ?_⟩
    by_contra hc
    have hf0 : Nat.find hex = 0 := by omega
    have := Nat.find_spec hex
    rw [hf0] at this
    exact h0 this

end Input

end

end PGM
