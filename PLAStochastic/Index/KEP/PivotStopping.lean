import PLAStochastic.Index.Algorithm.EndpointHierarchyBounds
import PLAStochastic.Index.KEP.PrefixStability
import PLAStochastic.Index.KEP.OrderStatisticReset
import PLAStochastic.Index.LocalCount.CyclicTwo
import Mathlib.Probability.Process.Stopping

/-!
# Endpoint pivots are stopping times of the natural filtration

Source: `proofs/proofK_reset.tex`, `lem:Knaturalstop` (every completed endpoint pivot rank
is a stopping time of the natural filtration).

For a base pair sequence `z` (all counts `1`) the layer-`ℓ` base pivots are
`layerPivot eps z ℓ j = pairRank (pairLayer eps ℓ z) j` (`PLAStochastic.Index.KEP.PrefixStability`), the base
rank of the `j`-th layer-`ℓ` key.

* **Causality** (`layerPivot_eq_of_le`, `layerPivot_le_iff`, `layerPivot_causal`).  If the base
  keys of `z` and `z'` agree at the indices `≤ r` and every segment of every layer of `z` is
  finite, then every layer-`ℓ` pivot `j` of `z` with rank `≤ r` has the same rank in `z'`.
  With finiteness on both sides the events `{pivot ≤ r}` agree.  The finiteness is needed: after an
  infinite segment the block starts stop moving (`ENat.toNat ⊤ = 0`), so the later pivots of
  that layer repeat an earlier rank while a sequence that agrees only up to `r` may cut later.
* **Finiteness from a constant tail** (`allLayersFinite_of_fst_eq_zero`).  A pair sequence
  whose gaps vanish eventually has finite segments on every layer, for every `eps`.
* **Stopping times** (`measurableSet_layerPivot_eq`, `isStoppingTime_layerPivot`).  On the
  sample space `Fin N → ℝ` with `coordSigma N r = σ(v 0, …, v r)`, take any base pair sequence
  `ext v` with unit counts, gaps adapted as `(ext v i).1 ∈ coordSigma N (i + 1)`, and all
  layers finite.  Then every `{layerPivot eps (ext v) ℓ j = r}` lies in `coordSigma N r`.
  Successive pivots are ordered, so an event of the stopped σ-algebra of one pivot, in the
  form used by `Renyi.orderLaw_inter_futureKeys_stopping`, stays in the stopped σ-algebra of
  every later pivot (`measurableSet_inter_eq_of_le`, `measurableSet_inter_layerPivot_of_le`,
  `measurableSet_inter_layerPivot_succ_layer`).
* **The sample keys** (`samplePairs`).  For any measurable key map `Q`, the gaps
  `Q (v (i + 1)) - Q (v i)` for `i + 1 < N`, continued by zero gaps, satisfy all hypotheses
  (`measurableSet_layerPivot_samplePairs_eq`, `isStoppingTime_layerPivot_samplePairs`).
-/

namespace PGM

noncomputable section

open Classical Finset

/-! ## Causality of the pivots -/

section Deterministic

variable {eps : ℝ} {z z' : ℕ → ℝ × ℕ}

/-- With all segments of all layers finite and `eps ≥ 0`, the pivot of a key does not
    decrease from one layer to the next. -/
theorem layerPivot_le_succ_layer (heps : 0 ≤ eps) (hfin : AllLayersFinite eps z) (ℓ j : ℕ) :
    layerPivot eps z ℓ j ≤ layerPivot eps z (ℓ + 1) j := by
  rw [layerPivot_succ]
  exact layerPivot_mono eps z ℓ (le_blockStart heps (hfin ℓ) j)

/-- Agreement of the gaps below `r` gives agreement of the keys up to `r`. -/
theorem pairKeys_eq_of_fst_eq {r : ℕ} (h : ∀ i < r, (z i).1 = (z' i).1) :
    ∀ i ≤ r, pairKeys z i = pairKeys z' i := fun i hi =>
  sum_congr rfl fun s hs => h s (by rw [mem_range] at hs; omega)

/-- A finite segment length `s` is decided by the first `s + 1` keys. -/
theorem segLen_eq_of_eq_natCast {p p' : ℕ → ℝ} {s : ℕ} (hs : segLen eps p = s)
    (hpp : ∀ i ≤ s, p i = p' i) : segLen eps p' = s := by
  have h1 : prefixAffineFeasible eps p s ↔ prefixAffineFeasible eps p' s :=
    prefixAffineFeasible_congr fun i hi => hpp i hi.le
  have h2 : prefixAffineFeasible eps p (s + 1) ↔ prefixAffineFeasible eps p' (s + 1) :=
    prefixAffineFeasible_congr fun i hi => hpp i (Nat.lt_succ_iff.1 hi)
  rw [segLen_eq_natCast_iff] at hs ⊢
  exact ⟨h1.1 hs.1, fun h => hs.2 (h2.2 h)⟩

/-- **Blocks are causal.**  If all segments of `w` are finite, the block starts of `w` up to
    block `n` are decided by the keys of `w` up to the start of block `n`. -/
theorem blockStart_eq_of_pairKeys_eq {w w' : ℕ → ℝ × ℕ} (hfin : AllSegmentsFinite eps w)
    {n : ℕ} (hkey : ∀ i ≤ blockStart eps w n, pairKeys w i = pairKeys w' i) :
    ∀ k ≤ n, blockStart eps w' k = blockStart eps w k
  | 0, _ => by simp [blockStart]
  | k + 1, hk => by
    have ih := blockStart_eq_of_pairKeys_eq hfin hkey k (by omega)
    have hmono : blockStart eps w (k + 1) ≤ blockStart eps w n := blockStart_mono eps w hk
    have hsucc := blockStart_succ eps w k
    rw [blockStart_succ, ih, hsucc]
    congr 1
    rw [pairShift_iterate eps w' k, pairShift_iterate eps w k, ih]
    rw [pairShift_iterate eps w k] at hsucc
    have hne := hfin k
    rw [pairShift_iterate eps w k] at hne
    set b := blockStart eps w k with hb
    set s := (pairSegLen eps fun t => w (b + t)).toNat with hs
    have hseg : segLen eps (pairKeys fun t => w (b + t)) = s := (ENat.natCast_toNat hne).symm
    have hseg' : segLen eps (pairKeys fun t => w' (b + t)) = s := by
      refine segLen_eq_of_eq_natCast hseg fun i hi => ?_
      rw [pairKeys_shift, pairKeys_shift, hkey (b + i) (by omega), hkey b (by omega)]
    show (segLen eps (pairKeys fun t => w' (b + t))).toNat = s
    rw [hseg', ENat.toNat_natCast]

/-- **Causality of the pivots.**  Let `z, z'` be base pair sequences (unit counts) whose keys
    agree at the indices `≤ r`, and let every segment of every layer of `z` be finite.  Every
    layer-`ℓ` pivot `j` of `z` with rank `≤ r` has the same rank in `z'`. -/
theorem layerPivot_eq_of_le (hz : ∀ t, (z t).2 = 1) (hz' : ∀ t, (z' t).2 = 1)
    (hfin : AllLayersFinite eps z) {r : ℕ} (hkey : ∀ i ≤ r, pairKeys z i = pairKeys z' i) :
    ∀ ℓ j, layerPivot eps z ℓ j ≤ r → layerPivot eps z' ℓ j = layerPivot eps z ℓ j
  | 0, j, _ => by rw [layerPivot_zero hz, layerPivot_zero hz']
  | ℓ + 1, j, hj => by
    have ih := layerPivot_eq_of_le hz hz' hfin hkey ℓ
    rw [layerPivot_succ] at hj ⊢
    rw [layerPivot_succ]
    have hkw : ∀ i ≤ blockStart eps (pairLayer eps ℓ z) j,
        pairKeys (pairLayer eps ℓ z) i = pairKeys (pairLayer eps ℓ z') i := by
      intro i hi
      have hpi : layerPivot eps z ℓ i ≤ r := (layerPivot_mono eps z ℓ hi).trans hj
      rw [pairKeys_pairLayer hz, pairKeys_pairLayer hz', ih i hpi,
        hkey _ hpi]
    rw [blockStart_eq_of_pairKeys_eq (hfin ℓ) hkw j le_rfl, ih _ hj]

/-- **Causality of the pivots, two-sided.**  With finite segments on both sides, the events
    `{pivot ≤ r}` agree. -/
theorem layerPivot_le_iff (hz : ∀ t, (z t).2 = 1) (hz' : ∀ t, (z' t).2 = 1)
    (hfin : AllLayersFinite eps z) (hfin' : AllLayersFinite eps z') {r : ℕ}
    (hkey : ∀ i ≤ r, pairKeys z i = pairKeys z' i) (ℓ j : ℕ) :
    layerPivot eps z ℓ j ≤ r ↔ layerPivot eps z' ℓ j ≤ r := by
  constructor
  · intro h
    rw [layerPivot_eq_of_le hz hz' hfin hkey ℓ j h]
    exact h
  · intro h
    rw [layerPivot_eq_of_le hz' hz hfin' (fun i hi => (hkey i hi).symm) ℓ j h]
    exact h

/-- **Causality of the pivots** (`lem:Knaturalstop`, deterministic part): for base pair
    sequences with the same keys up to index `r` and finite segments on every layer, a
    layer-`ℓ` pivot has rank `≤ r` for one sequence iff it has for the other, and then the two
    ranks coincide. -/
theorem layerPivot_causal (hz : ∀ t, (z t).2 = 1) (hz' : ∀ t, (z' t).2 = 1)
    (hfin : AllLayersFinite eps z) (hfin' : AllLayersFinite eps z') {r : ℕ}
    (hkey : ∀ i ≤ r, pairKeys z i = pairKeys z' i) (ℓ j : ℕ) :
    (layerPivot eps z ℓ j ≤ r ↔ layerPivot eps z' ℓ j ≤ r) ∧
      (layerPivot eps z ℓ j ≤ r → layerPivot eps z ℓ j = layerPivot eps z' ℓ j) :=
  ⟨layerPivot_le_iff hz hz' hfin hfin' hkey ℓ j,
    fun h => (layerPivot_eq_of_le hz hz' hfin hkey ℓ j h).symm⟩

end Deterministic

/-! ## Finite segments from a constant tail -/

section ConstTail

variable {eps : ℝ}

/-- A key sequence that is eventually constant has a finite first segment. -/
theorem segLen_ne_top_of_eventually_const {p : ℕ → ℝ} {M : ℕ} {c : ℝ}
    (hp : ∀ i, M ≤ i → p i = c) : segLen eps p ≠ ⊤ := by
  intro htop
  obtain ⟨a, b, hab⟩ := segLen_eq_top_iff.1 htop (M + ⌊2 * eps⌋₊ + 2)
  have h1 := hab M (by omega)
  have h2 := hab (M + ⌊2 * eps⌋₊ + 1) (by omega)
  rw [hp M le_rfl] at h1
  rw [hp _ (by omega)] at h2
  have hfl := Nat.lt_floor_add_one (2 * eps)
  push_cast at h2
  rw [abs_le] at h1 h2
  linarith [h1.1, h1.2, h2.1, h2.2]

/-- Eventual constancy survives a monotone reindexing. -/
theorem eventually_const_comp_monotone {p : ℕ → ℝ} {M : ℕ} {c : ℝ}
    (hp : ∀ i, M ≤ i → p i = c) {g : ℕ → ℕ} (hg : Monotone g) :
    ∃ M' c', ∀ j, M' ≤ j → p (g j) = c' := by
  by_cases h : ∃ j₀, M ≤ g j₀
  · obtain ⟨j₀, hj₀⟩ := h
    exact ⟨j₀, c, fun j hj => hp _ (hj₀.trans (hg hj))⟩
  · push Not at h
    have hbdd : BddAbove (Set.range g) := ⟨M, by rintro _ ⟨j, rfl⟩; exact (h j).le⟩
    obtain ⟨j₀, hj₀⟩ := Nat.sSup_mem (Set.range_nonempty g) hbdd
    refine ⟨j₀, p (g j₀), fun j hj => ?_⟩
    have : g j = g j₀ := le_antisymm (hj₀ ▸ le_csSup hbdd ⟨j, rfl⟩) (hg hj)
    rw [this]

theorem eventually_const_pairKeys_layerMap {w : ℕ → ℝ × ℕ}
    (hw : ∃ M c, ∀ i, M ≤ i → pairKeys w i = c) :
    ∃ M c, ∀ i, M ≤ i → pairKeys (layerMap eps w) i = c := by
  obtain ⟨M, c, hMc⟩ := hw
  obtain ⟨M', c', h⟩ := eventually_const_comp_monotone hMc (blockStart_mono eps w)
  exact ⟨M', c', fun j hj => by rw [pairKeys_layerMap]; exact h j hj⟩

theorem allSegmentsFinite_of_eventually_const {w : ℕ → ℝ × ℕ}
    (hw : ∃ M c, ∀ i, M ≤ i → pairKeys w i = c) : AllSegmentsFinite eps w := by
  intro j
  obtain ⟨M, c, hMc⟩ := hw
  rw [pairShift_iterate]
  show segLen eps (pairKeys fun t => w (blockStart eps w j + t)) ≠ ⊤
  refine segLen_ne_top_of_eventually_const (M := M) (c := c - pairKeys w (blockStart eps w j))
    fun i hi => ?_
  rw [pairKeys_shift, hMc _ (by omega)]

/-- Eventually constant base keys give finite segments on every layer. -/
theorem allLayersFinite_of_eventually_const {z : ℕ → ℝ × ℕ}
    (hz : ∃ M c, ∀ i, M ≤ i → pairKeys z i = c) : AllLayersFinite eps z := by
  have h : ∀ ℓ, ∃ M c, ∀ i, M ≤ i → pairKeys (pairLayer eps ℓ z) i = c := by
    intro ℓ
    induction ℓ with
    | zero => exact hz
    | succ ℓ ih =>
      rw [pairLayer_succ]
      exact eventually_const_pairKeys_layerMap ih
  exact fun ℓ => allSegmentsFinite_of_eventually_const (h ℓ)

/-- **Constant tail.**  Eventually vanishing gaps give finite segments on every layer. -/
theorem allLayersFinite_of_fst_eq_zero {z : ℕ → ℝ × ℕ} {M : ℕ}
    (hz : ∀ i, M ≤ i → (z i).1 = 0) : AllLayersFinite eps z := by
  refine allLayersFinite_of_eventually_const ⟨M, pairKeys z M, fun i hi => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
  induction k with
  | zero => rfl
  | succ k ih =>
    have h := ih (by omega)
    simp only [pairKeys, ← add_assoc, sum_range_succ] at h ⊢
    rw [h, hz _ (by omega), add_zero]

end ConstTail

/-! ## Truncation after index `r` -/

/-- The base pair sequence with the gaps of `z` below `r` and zero gaps from `r` on. -/
def truncPairs (z : ℕ → ℝ × ℕ) (r : ℕ) : ℕ → ℝ × ℕ := fun i => (if i < r then (z i).1 else 0, 1)

theorem truncPairs_snd (z : ℕ → ℝ × ℕ) (r i : ℕ) : (truncPairs z r i).2 = 1 := rfl

theorem pairKeys_truncPairs (z : ℕ → ℝ × ℕ) (r : ℕ) :
    ∀ i ≤ r, pairKeys (truncPairs z r) i = pairKeys z i :=
  pairKeys_eq_of_fst_eq fun i hi => by simp [truncPairs, hi]

theorem allLayersFinite_truncPairs (eps : ℝ) (z : ℕ → ℝ × ℕ) (r : ℕ) :
    AllLayersFinite eps (truncPairs z r) :=
  allLayersFinite_of_fst_eq_zero (M := r) fun i hi => by
    simp [truncPairs, not_lt.2 hi]

/-- The event `{pivot = r}` only reads the gaps below `r`. -/
theorem layerPivot_eq_iff_truncPairs {eps : ℝ} {z : ℕ → ℝ × ℕ} (hz : ∀ t, (z t).2 = 1)
    (hfin : AllLayersFinite eps z) (ℓ j r : ℕ) :
    layerPivot eps z ℓ j = r ↔ layerPivot eps (truncPairs z r) ℓ j = r := by
  have hkey : ∀ i ≤ r, pairKeys z i = pairKeys (truncPairs z r) i :=
    fun i hi => (pairKeys_truncPairs z r i hi).symm
  constructor
  · intro h
    rw [layerPivot_eq_of_le hz (truncPairs_snd z r) hfin hkey ℓ j h.le]
    exact h
  · intro h
    rw [layerPivot_eq_of_le (truncPairs_snd z r) hz (allLayersFinite_truncPairs eps z r)
      (fun i hi => (hkey i hi).symm) ℓ j h.le]
    exact h

/-! ## Stopping times of the natural filtration -/

section Stopping

open MeasureTheory

theorem measurable_layerPivot (eps : ℝ) (ℓ j : ℕ) :
    Measurable fun z : ℕ → ℝ × ℕ => layerPivot eps z ℓ j := by
  simp only [layerPivot, pairRank]
  exact Finset.measurable_sum _ fun s _ =>
    measurable_snd.comp ((measurable_pi_apply s).comp (measurable_pairLayer eps ℓ))

variable {N : ℕ}

/-- The coordinate `v k` is `σ(v 0, …, v r)`-measurable for `k ≤ r`. -/
theorem measurable_coord_coordSigma {r : ℕ} (k : Fin N) (hk : (k : ℕ) ≤ r) :
    Measurable[Renyi.coordSigma N r] fun v : Fin N → ℝ => v k := by
  rw [measurable_iff_comap_le]
  exact le_iSup₂_of_le (f := fun (i : Fin N) (_ : (i : ℕ) ≤ r) =>
    MeasurableSpace.comap (fun v : Fin N → ℝ => v i) inferInstance) k hk le_rfl

variable {eps : ℝ} {ext : (Fin N → ℝ) → ℕ → ℝ × ℕ}

theorem measurable_truncPairs_coordSigma
    (hgap : ∀ i, Measurable[Renyi.coordSigma N (i + 1)] fun v => (ext v i).1) (r : ℕ) :
    Measurable[Renyi.coordSigma N r] fun v => truncPairs (ext v) r := by
  refine @measurable_pi_lambda _ _ _ (Renyi.coordSigma N r) _ _ fun i => ?_
  show Measurable[Renyi.coordSigma N r] fun v => ((if i < r then (ext v i).1 else 0), 1)
  refine Measurable.prodMk ?_ measurable_const
  by_cases hi : i < r
  · simp only [if_pos hi]
    exact (hgap i).mono (Renyi.coordSigma_mono N (Nat.succ_le_of_lt hi)) le_rfl
  · simp only [if_neg hi]
    exact measurable_const

/-- **Pivots are stopping times** (`lem:Knaturalstop`).  For a base pair sequence `ext v` on
    the sample space with unit counts, gaps adapted as `(ext v i).1 ∈ σ(v 0, …, v (i + 1))`,
    and finite segments on every layer, `{layerPivot eps (ext v) ℓ j = r} ∈ σ(v 0, …, v r)`. -/
theorem measurableSet_layerPivot_eq (hcount : ∀ v i, (ext v i).2 = 1)
    (hgap : ∀ i, Measurable[Renyi.coordSigma N (i + 1)] fun v => (ext v i).1)
    (hfin : ∀ v, AllLayersFinite eps (ext v)) (ℓ j r : ℕ) :
    MeasurableSet[Renyi.coordSigma N r] {v | layerPivot eps (ext v) ℓ j = r} := by
  have hset : {v | layerPivot eps (ext v) ℓ j = r} =
      (fun v => truncPairs (ext v) r) ⁻¹' ((fun z => layerPivot eps z ℓ j) ⁻¹' {r}) := by
    ext v
    exact layerPivot_eq_iff_truncPairs (hcount v) (hfin v) ℓ j r
  rw [hset]
  exact measurable_truncPairs_coordSigma hgap r
    (measurable_layerPivot eps ℓ j (measurableSet_singleton r))

/-- **Pivots are stopping times**, with Mathlib's notion for the coordinate filtration. -/
theorem isStoppingTime_layerPivot (hcount : ∀ v i, (ext v i).2 = 1)
    (hgap : ∀ i, Measurable[Renyi.coordSigma N (i + 1)] fun v => (ext v i).1)
    (hfin : ∀ v, AllLayersFinite eps (ext v)) (ℓ j : ℕ) :
    IsStoppingTime (Renyi.coordFiltration N)
      fun v => (layerPivot eps (ext v) ℓ j : WithTop ℕ) := by
  refine isStoppingTime_of_measurableSet_eq fun r => ?_
  have hset : {v | layerPivot eps (ext v) ℓ j = r} =
      {v | ((layerPivot eps (ext v) ℓ j : ℕ) : WithTop ℕ) = ((r : ℕ) : WithTop ℕ)} := by
    ext v
    simp only [Set.mem_ofPred_eq, Nat.cast_inj]
  have h := measurableSet_layerPivot_eq hcount hgap hfin ℓ j r
  rw [hset] at h
  exact h

/-- **Stopped σ-algebras increase along ordered stopping times.**  If `ρ ≤ σ`, `σ` is a
    stopping time and `A` belongs to the stopped σ-algebra of `ρ` (in the form used by
    `Renyi.orderLaw_inter_futureKeys_stopping`), then `A` belongs to that of `σ`. -/
theorem measurableSet_inter_eq_of_le {ρ σ : (Fin N → ℝ) → ℕ} (hle : ∀ v, ρ v ≤ σ v)
    (hσ : ∀ r, MeasurableSet[Renyi.coordSigma N r] {v | σ v = r}) {A : Set (Fin N → ℝ)}
    (hA : ∀ r, MeasurableSet[Renyi.coordSigma N r] (A ∩ {v | ρ v = r})) (r : ℕ) :
    MeasurableSet[Renyi.coordSigma N r] (A ∩ {v | σ v = r}) := by
  have hset : A ∩ {v | σ v = r} =
      ⋃ s ∈ Finset.range (r + 1), (A ∩ {v | ρ v = s}) ∩ {v | σ v = r} := by
    ext v
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range,
      exists_prop]
    constructor
    · rintro ⟨hvA, hvσ⟩
      exact ⟨ρ v, by have := hle v; omega, ⟨hvA, rfl⟩, hvσ⟩
    · rintro ⟨s, -, ⟨hvA, -⟩, hvσ⟩
      exact ⟨hvA, hvσ⟩
  rw [hset]
  refine Finset.measurableSet_biUnion _ fun s hs => ?_
  have hsr : s ≤ r := by rw [Finset.mem_range] at hs; omega
  exact (Renyi.coordSigma_mono N hsr _ (hA s)).inter (hσ r)

/-- Successive pivots of one layer: the stopped σ-algebra of pivot `j` is contained in that
    of pivot `k ≥ j`. -/
theorem measurableSet_inter_layerPivot_of_le (hcount : ∀ v i, (ext v i).2 = 1)
    (hgap : ∀ i, Measurable[Renyi.coordSigma N (i + 1)] fun v => (ext v i).1)
    (hfin : ∀ v, AllLayersFinite eps (ext v)) {ℓ j k : ℕ} (hjk : j ≤ k) {A : Set (Fin N → ℝ)}
    (hA : ∀ r, MeasurableSet[Renyi.coordSigma N r] (A ∩ {v | layerPivot eps (ext v) ℓ j = r}))
    (r : ℕ) :
    MeasurableSet[Renyi.coordSigma N r] (A ∩ {v | layerPivot eps (ext v) ℓ k = r}) :=
  measurableSet_inter_eq_of_le (fun v => layerPivot_mono eps (ext v) ℓ hjk)
    (measurableSet_layerPivot_eq hcount hgap hfin ℓ k) hA r

/-- From one layer to the next: the stopped σ-algebra of the layer-`ℓ` pivot `j` is contained
    in that of the layer-`(ℓ + 1)` pivot `j` (`eps ≥ 0`). -/
theorem measurableSet_inter_layerPivot_succ_layer (heps : 0 ≤ eps)
    (hcount : ∀ v i, (ext v i).2 = 1)
    (hgap : ∀ i, Measurable[Renyi.coordSigma N (i + 1)] fun v => (ext v i).1)
    (hfin : ∀ v, AllLayersFinite eps (ext v)) {ℓ j : ℕ} {A : Set (Fin N → ℝ)}
    (hA : ∀ r, MeasurableSet[Renyi.coordSigma N r] (A ∩ {v | layerPivot eps (ext v) ℓ j = r}))
    (r : ℕ) :
    MeasurableSet[Renyi.coordSigma N r] (A ∩ {v | layerPivot eps (ext v) (ℓ + 1) j = r}) :=
  measurableSet_inter_eq_of_le (fun v => layerPivot_le_succ_layer heps (hfin v) ℓ j)
    (measurableSet_layerPivot_eq hcount hgap hfin (ℓ + 1) j) hA r

end Stopping

/-! ## The keys of a sorted sample -/

section Sample

open MeasureTheory

variable {N : ℕ}

/-- The base pair sequence of the keys `Q (v 0), …, Q (v (N - 1))`: gaps
    `Q (v (i + 1)) - Q (v i)` for `i + 1 < N`, zero gaps beyond, all counts `1`. -/
def samplePairs (Q : ℝ → ℝ) (v : Fin N → ℝ) : ℕ → ℝ × ℕ := fun i =>
  (if h : i + 1 < N then Q (v ⟨i + 1, h⟩) - Q (v ⟨i, by omega⟩) else 0, 1)

theorem samplePairs_snd (Q : ℝ → ℝ) (v : Fin N → ℝ) (i : ℕ) : (samplePairs Q v i).2 = 1 := rfl

/-- The keys of `samplePairs` are the sample keys, translated to start at `0`. -/
theorem pairKeys_samplePairs (Q : ℝ → ℝ) (v : Fin N → ℝ) :
    ∀ t (ht : t < N), pairKeys (samplePairs Q v) t = Q (v ⟨t, ht⟩) - Q (v ⟨0, by omega⟩)
  | 0, ht => by simp [pairKeys]
  | t + 1, ht => by
    have h := pairKeys_samplePairs Q v t (by omega)
    simp only [pairKeys, sum_range_succ] at h ⊢
    rw [h]
    simp only [samplePairs, dif_pos ht]
    ring

theorem allLayersFinite_samplePairs (eps : ℝ) (Q : ℝ → ℝ) (v : Fin N → ℝ) :
    AllLayersFinite eps (samplePairs Q v) :=
  allLayersFinite_of_fst_eq_zero (M := N) fun i hi => by
    simp only [samplePairs, dif_neg (show ¬ i + 1 < N by omega)]

theorem measurable_samplePairs_fst {Q : ℝ → ℝ} (hQ : Measurable Q) (i : ℕ) :
    Measurable[Renyi.coordSigma N (i + 1)] fun v : Fin N → ℝ => (samplePairs Q v i).1 := by
  by_cases h : i + 1 < N
  · simp only [samplePairs, dif_pos h]
    exact (hQ.comp (measurable_coord_coordSigma ⟨i + 1, h⟩ le_rfl)).sub
      (hQ.comp (measurable_coord_coordSigma ⟨i, by omega⟩ (by simp)))
  · simp only [samplePairs, dif_neg h]
    exact measurable_const

/-- **Pivots of the sample keys are stopping times.**  For any measurable key map `Q`, every
    `{layerPivot eps (samplePairs Q v) ℓ j = r}` lies in `σ(v 0, …, v r)`. -/
theorem measurableSet_layerPivot_samplePairs_eq {eps : ℝ} {Q : ℝ → ℝ} (hQ : Measurable Q)
    (ℓ j r : ℕ) :
    MeasurableSet[Renyi.coordSigma N r] {v | layerPivot eps (samplePairs Q v) ℓ j = r} :=
  measurableSet_layerPivot_eq (fun v i => samplePairs_snd Q v i) (measurable_samplePairs_fst hQ)
    (allLayersFinite_samplePairs eps Q) ℓ j r

theorem isStoppingTime_layerPivot_samplePairs {eps : ℝ} {Q : ℝ → ℝ} (hQ : Measurable Q)
    (ℓ j : ℕ) :
    IsStoppingTime (Renyi.coordFiltration N)
      fun v => (layerPivot eps (samplePairs Q v) ℓ j : WithTop ℕ) :=
  isStoppingTime_layerPivot (fun v i => samplePairs_snd Q v i) (measurable_samplePairs_fst hQ)
    (allLayersFinite_samplePairs eps Q) ℓ j

end Sample

end

end PGM
