import PLAStochastic.Index.Algorithm.Segmentation
import PLAStochastic.Index.Algorithm.RankPromotion
import PLAStochastic.Index.Algorithm.EndpointHierarchyBounds
import Mathlib.Data.Nat.Log

/-!
# The finite ALG-RE run (complete rank-equispaced promotion)

`reLayer eps p n ℓ = (Δ_ℓ, N_ℓ)` is layer `ℓ` of ALG-RE on the keys
`p 0, …, p (n-1)`: its cumulative rank spacing relative to the input and its
number of keys.  Layer `ℓ` consists of the keys `j ↦ p (j * Δ_ℓ)`, `j < N_ℓ`.
ALG-OPT fits `M_{ℓ+1} = reSegs eps p n ℓ` segments to them, the spacing is
`d_ℓ = ⌊N_ℓ / M_{ℓ+1}⌋`, and the promoted keys are the layer keys of rank
`j * d_ℓ < N_ℓ`, so `N_{ℓ+1} = ⌈N_ℓ / d_ℓ⌉` and `Δ_{ℓ+1} = d_ℓ Δ_ℓ`.
`reHeight` is the first layer `ℓ ≥ 1` with one key.

`reKeys` runs the same rule on explicit key lists; `reKeys_eq` is the pivot
identity `p^{(ℓ)}_j = p^{(0)}_{j Δ_ℓ}` and `reKeys_promote` states the promotion
rule literally.  With `eps ≥ 1` every non-final ALG-OPT segment has at least three
keys, which gives `M ≤ ⌈N/3⌉`, hence `2 M ≤ N` on nontrivial layers and the
deterministic lattice facts of `PLAStochastic.Index.Algorithm.RankPromotion`: `N_ℓ = ⌈n/Δ_ℓ⌉`,
`(N_ℓ - 1) Δ_ℓ < n ≤ N_ℓ Δ_ℓ < 2n`, `M ≤ N' ≤ 2M`, halving, and
`reHeight ≤ m + log₂ N_m + 1` for every `m`.

`PLAcount eps g Δ N` is the ALG-OPT segment count of the block-sum walk
`j ↦ ∑_{i < jΔ} g i`, `j < N`; it reads only `g 0, …, g (NΔ - 1)`, and by
translation invariance `M_{ℓ+1} = PLAcount eps g Δ_ℓ N_ℓ` when the keys are the
partial sums of the gaps `g` (`reSegs_eq_PLAcount`, eq:reduction).
Nothing here is probabilistic.
-/

namespace PGM

noncomputable section

open Classical Finset

/-! ## Segment counts of the finite ALG-OPT run -/

/-- A nonempty list has at least one segment. -/
theorem one_le_finSegCount {eps : ℝ} (P : ℕ → ℝ) {K : ℕ} (hK : 1 ≤ K) :
    1 ≤ finSegCount eps P K := by
  unfold finSegCount
  rw [Nat.count_eq_card_filter_range]
  apply Finset.card_pos.2
  exact ⟨0, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), by simp [finCut]; omega⟩⟩

/-- With `eps ≥ 1` a finite segment has at least three keys unless the list ends first. -/
theorem min_three_le_finSegLen {eps : ℝ} (heps : 1 ≤ eps) (P : ℕ → ℝ) (K a : ℕ) :
    min 3 (K - a) ≤ finSegLen eps P K a := by
  have h := finSegLen_eq_min eps P K a
  have h3 := three_le_segLen heps (shiftSeq P a)
  have hle : ((min 3 (K - a) : ℕ) : ℕ∞) ≤
      min (segLen eps (shiftSeq P a)) ((K - a : ℕ) : ℕ∞) := by
    refine le_min (le_trans ?_ h3) (by exact_mod_cast min_le_right 3 (K - a))
    exact_mod_cast min_le_left 3 (K - a)
  rw [← h] at hle
  exact_mod_cast hle

theorem min_three_mul_le_finCut {eps : ℝ} (heps : 1 ≤ eps) (P : ℕ → ℝ) (K : ℕ) :
    ∀ j, min (3 * j) K ≤ finCut eps P K j
  | 0 => by simp
  | j + 1 => by
    have ih := min_three_mul_le_finCut heps P K j
    have hle := finCut_le eps P K j
    have hs := min_three_le_finSegLen heps P K (finCut eps P K j)
    show min (3 * (j + 1)) K ≤ finCut eps P K j + finSegLen eps P K (finCut eps P K j)
    omega

/-- **Count bound**: with `eps ≥ 1`, ALG-OPT uses at most `⌈K/3⌉` segments. -/
theorem finSegCount_le_ceilDiv_three {eps : ℝ} (heps : 1 ≤ eps) (P : ℕ → ℝ) (K : ℕ) :
    finSegCount eps P K ≤ K ⌈/⌉ 3 := by
  unfold finSegCount
  rw [Nat.count_eq_card_filter_range]
  calc #{j ∈ range (K + 1) | finCut eps P K j < K} ≤ #(range (K ⌈/⌉ 3)) := by
        apply Finset.card_le_card
        intro j hj
        rw [Finset.mem_filter] at hj
        rw [Finset.mem_range, Nat.ceilDiv_eq_add_pred_div]
        have := min_three_mul_le_finCut heps P K j
        omega
    _ = K ⌈/⌉ 3 := Finset.card_range _

theorem finSegCount_le_self {eps : ℝ} (heps : 1 ≤ eps) (P : ℕ → ℝ) (K : ℕ) :
    finSegCount eps P K ≤ K := by
  have := finSegCount_le_ceilDiv_three heps P K
  rw [Nat.ceilDiv_eq_add_pred_div] at this
  omega

/-- The nonterminal hypothesis `2 M ≤ K` of `PLAStochastic.Index.Algorithm.RankPromotion`, from the three-key bound. -/
theorem two_mul_finSegCount_le {eps : ℝ} (heps : 1 ≤ eps) (P : ℕ → ℝ) {K : ℕ}
    (hK : 2 ≤ K) : 2 * finSegCount eps P K ≤ K :=
  nonterminal_of_three_cover hK (finSegCount_le_ceilDiv_three heps P K)

theorem finSegCount_one {eps : ℝ} (heps : 1 ≤ eps) (P : ℕ → ℝ) :
    finSegCount eps P 1 = 1 :=
  le_antisymm (finSegCount_le_self heps P 1) (one_le_finSegCount P le_rfl)

/-! ## Affine invariance of the finite run -/

theorem finSegLen_affine {eps : ℝ} {P : ℕ → ℝ} {s c : ℝ} (hs : s ≠ 0) (K a : ℕ) :
    finSegLen eps (fun i => s * P i + c) K a = finSegLen eps P K a := by
  unfold finSegLen
  apply findGreatest_congr'
  intro len _
  exact prefixAffineFeasible_affine_iff (p := shiftSeq P a) hs

theorem finCut_affine {eps : ℝ} {P : ℕ → ℝ} {s c : ℝ} (hs : s ≠ 0) (K : ℕ) :
    ∀ j, finCut eps (fun i => s * P i + c) K j = finCut eps P K j
  | 0 => rfl
  | j + 1 => by
    simp only [finCut, finCut_affine hs K j, finSegLen_affine hs]

/-- The segment count is invariant under nonzero affine maps of the keys. -/
theorem finSegCount_affine {eps : ℝ} {P : ℕ → ℝ} {s c : ℝ} (hs : s ≠ 0) (K : ℕ) :
    finSegCount eps (fun i => s * P i + c) K = finSegCount eps P K := by
  unfold finSegCount
  simp only [finCut_affine hs]

/-- Translation invariance of the segment count. -/
theorem finSegCount_add_const {eps : ℝ} (P : ℕ → ℝ) (c : ℝ) (K : ℕ) :
    finSegCount eps (fun i => P i + c) K = finSegCount eps P K := by
  have h := finSegCount_affine (eps := eps) (P := P) (s := 1) (c := c) one_ne_zero K
  simpa only [one_mul] using h

/-! ## The block-sum walk and `PLAcount` -/

/-- `PLAcount eps g Δ N`: the ALG-OPT segment count of the block-sum walk
    `W_j = ∑_{i < jΔ} g i`, `j < N` (the TeX `\PLAcount(Δ, N)`, gaps indexed from `0`). -/
def PLAcount (eps : ℝ) (g : ℕ → ℝ) (Δ N : ℕ) : ℕ :=
  finSegCount eps (fun j => ∑ i ∈ range (j * Δ), g i) N

/-- `PLAcount eps g Δ N` reads only the gaps `g 0, …, g (NΔ - 1)`. -/
theorem PLAcount_congr {eps : ℝ} {g g' : ℕ → ℝ} {Δ N : ℕ}
    (hgg : ∀ i < N * Δ, g i = g' i) : PLAcount eps g Δ N = PLAcount eps g' Δ N := by
  unfold PLAcount
  apply finSegCount_congr
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  exact hgg i ((Finset.mem_range.1 hi).trans_le (Nat.mul_le_mul_right _ hj.le))

/-- `PLAcount eps · Δ N` is a deterministic functional of the gap vector
    `(g 0, …, g (NΔ - 1))`. -/
theorem PLAcount_eq_functional (eps : ℝ) (Δ N : ℕ) :
    ∃ F : (Fin (N * Δ) → ℝ) → ℕ, ∀ g : ℕ → ℝ, PLAcount eps g Δ N = F (fun i => g i) := by
  refine ⟨fun v => PLAcount eps (fun i => if h : i < N * Δ then v ⟨i, h⟩ else 0) Δ N,
    fun g => PLAcount_congr fun i hi => ?_⟩
  simp [hi]

/-- **Translation invariance**: on the lattice `j ↦ jΔ`, keys that are partial sums of
    the gaps `g` from the origin `x0` have the segment count of the block-sum walk. -/
theorem finSegCount_lattice_eq_PLAcount {eps : ℝ} {p g : ℕ → ℝ} {x0 : ℝ} {Δ N : ℕ}
    (hp : ∀ j < N, p (j * Δ) = x0 + ∑ i ∈ range (j * Δ), g i) :
    finSegCount eps (fun j => p (j * Δ)) N = PLAcount eps g Δ N := by
  rw [finSegCount_congr (p' := fun j => (∑ i ∈ range (j * Δ), g i) + x0)
    (fun j hj => by rw [hp j hj, add_comm])]
  exact finSegCount_add_const _ x0 N

theorem finSegCount_lattice_eq_PLAcount' {eps : ℝ} {p g : ℕ → ℝ} {x0 : ℝ}
    (hp : ∀ t, p t = x0 + ∑ i ∈ range t, g i) (Δ N : ℕ) :
    finSegCount eps (fun j => p (j * Δ)) N = PLAcount eps g Δ N :=
  finSegCount_lattice_eq_PLAcount fun j _ => hp (j * Δ)

/-! ## Ceiling-division arithmetic -/

theorem one_le_ceilDiv {K d : ℕ} (hK : 1 ≤ K) (hd : 1 ≤ d) : 1 ≤ K ⌈/⌉ d := by
  rw [Nat.ceilDiv_eq_add_pred_div]
  exact Nat.div_pos (by omega) (by omega)

/-- The defining bounds of `⌈K/d⌉`. -/
theorem ceilDiv_lattice {K d : ℕ} (hK : 1 ≤ K) (hd : 1 ≤ d) :
    (K ⌈/⌉ d - 1) * d < K ∧ K ≤ K ⌈/⌉ d * d := by
  have hup : K ≤ d * (K ⌈/⌉ d) := le_smul_ceilDiv (by omega : 0 < d)
  refine ⟨?_, by rw [Nat.mul_comm]; exact hup⟩
  have hq : K ⌈/⌉ d * d ≤ K + d - 1 := by
    rw [Nat.ceilDiv_eq_add_pred_div]
    exact Nat.div_mul_le_self _ _
  have hq1 := one_le_ceilDiv hK hd
  rw [Nat.sub_mul, Nat.one_mul]
  omega

/-- A number of keys satisfying the lattice bounds is the ceiling. -/
theorem eq_ceilDiv_of_lattice {n N Δ : ℕ} (hΔ : 1 ≤ Δ) (h1 : (N - 1) * Δ < n)
    (h2 : n ≤ N * Δ) : N = n ⌈/⌉ Δ := by
  have hΔ' : 0 < Δ := by omega
  have hup : n ⌈/⌉ Δ ≤ N := (ceilDiv_le_iff_le_mul hΔ').2 (by rw [Nat.mul_comm]; exact h2)
  refine le_antisymm ?_ hup
  by_contra hlt
  have hq : n ⌈/⌉ Δ ≤ N - 1 := by omega
  have hn : n ≤ Δ * (N - 1) := (ceilDiv_le_iff_le_mul hΔ').1 hq
  rw [Nat.mul_comm] at hn
  omega

theorem lt_ceilDiv_iff_mul_lt {K d j : ℕ} (hd : 1 ≤ d) : j < K ⌈/⌉ d ↔ j * d < K := by
  rw [← not_le, ← not_le, ceilDiv_le_iff_le_mul (by omega : 0 < d), Nat.mul_comm]

/-! ## The ALG-RE run -/

/-- Layer `ℓ` of ALG-RE on `p 0, …, p (n-1)`: the pair `(Δ_ℓ, N_ℓ)` of the rank
    spacing relative to the input and the number of keys.  The layer keys are
    `j ↦ p (j * Δ_ℓ)`, `j < N_ℓ` (`reKeys_eq`).  ALG-OPT fits
    `M = finSegCount eps (fun j => p (j * Δ_ℓ)) N_ℓ` segments, `d = ⌊N_ℓ / M⌋`, and the
    ranks `j d < N_ℓ` are promoted. -/
def reLayer (eps : ℝ) (p : ℕ → ℝ) (n : ℕ) : ℕ → ℕ × ℕ
  | 0 => (1, n)
  | ℓ + 1 =>
    let Δ := (reLayer eps p n ℓ).1
    let N := (reLayer eps p n ℓ).2
    let M := finSegCount eps (fun j => p (j * Δ)) N
    let d := N / M
    (d * Δ, N ⌈/⌉ d)

/-- The height of ALG-RE: the first layer `ℓ ≥ 1` with one key. -/
def reHeight (eps : ℝ) (p : ℕ → ℝ) (n : ℕ) : ℕ :=
  sInf {ℓ | 1 ≤ ℓ ∧ (reLayer eps p n ℓ).2 = 1}

/-- `Δ_ℓ`, the rank spacing of layer `ℓ` relative to the input. -/
def reDelta (eps : ℝ) (p : ℕ → ℝ) (n ℓ : ℕ) : ℕ := (reLayer eps p n ℓ).1

/-- `N_ℓ`, the number of keys of layer `ℓ`. -/
def reSize (eps : ℝ) (p : ℕ → ℝ) (n ℓ : ℕ) : ℕ := (reLayer eps p n ℓ).2

/-- `M_{ℓ+1}`, the number of ALG-OPT segments fitted to layer `ℓ`. -/
def reSegs (eps : ℝ) (p : ℕ → ℝ) (n ℓ : ℕ) : ℕ :=
  finSegCount eps (fun j => p (j * reDelta eps p n ℓ)) (reSize eps p n ℓ)

/-- `d_ℓ = ⌊N_ℓ / M_{ℓ+1}⌋`, the promotion step of layer `ℓ`. -/
def reStep (eps : ℝ) (p : ℕ → ℝ) (n ℓ : ℕ) : ℕ := reSize eps p n ℓ / reSegs eps p n ℓ

section Run

variable {eps : ℝ} {p : ℕ → ℝ} {n : ℕ}

@[simp] theorem reDelta_zero : reDelta eps p n 0 = 1 := rfl

@[simp] theorem reSize_zero : reSize eps p n 0 = n := rfl

theorem reDelta_succ (ℓ : ℕ) :
    reDelta eps p n (ℓ + 1) = reStep eps p n ℓ * reDelta eps p n ℓ := rfl

theorem reSize_succ (ℓ : ℕ) :
    reSize eps p n (ℓ + 1) = reSize eps p n ℓ ⌈/⌉ reStep eps p n ℓ := rfl

/-- eq:reduction, first half: `M_{ℓ+1}` is the ALG-OPT count of the lattice keys. -/
theorem reSegs_eq (ℓ : ℕ) :
    reSegs eps p n ℓ =
      finSegCount eps (fun j => p (j * reDelta eps p n ℓ)) (reSize eps p n ℓ) := rfl

theorem reStep_eq_rankSpacing (ℓ : ℕ) :
    reStep eps p n ℓ = rankSpacing (reSize eps p n ℓ) (reSegs eps p n ℓ) := rfl

theorem reSize_succ_eq_reNextCount (ℓ : ℕ) :
    reSize eps p n (ℓ + 1) = reNextCount (reSize eps p n ℓ) (reSegs eps p n ℓ) := rfl

theorem reHeight_eq : reHeight eps p n = sInf {ℓ | 1 ≤ ℓ ∧ reSize eps p n ℓ = 1} := rfl

/-! ### The run on explicit key lists and the pivot identity -/

/-- ALG-RE on explicit key lists: layer `ℓ + 1` keeps the layer-`ℓ` keys of rank
    `j * d < N`, where `d = ⌊N / M⌋` and `M` is the ALG-OPT count of layer `ℓ`. -/
def reKeys (eps : ℝ) (p : ℕ → ℝ) (n : ℕ) : ℕ → (ℕ → ℝ) × ℕ
  | 0 => (p, n)
  | ℓ + 1 =>
    let P := (reKeys eps p n ℓ).1
    let N := (reKeys eps p n ℓ).2
    let d := N / finSegCount eps P N
    (fun j => P (j * d), N ⌈/⌉ d)

/-- **Pivot identity** `p^{(ℓ)}_j = p^{(0)}_{j Δ_ℓ}` (lem:pivotid), and `N_ℓ` is the
    length of the layer-`ℓ` key list. -/
theorem reKeys_eq (eps : ℝ) (p : ℕ → ℝ) (n : ℕ) :
    ∀ ℓ, reKeys eps p n ℓ = (fun j => p (j * reDelta eps p n ℓ), reSize eps p n ℓ)
  | 0 => by simp [reKeys]
  | ℓ + 1 => by
    rw [reKeys, reKeys_eq eps p n ℓ]
    refine Prod.ext (funext fun j => ?_) rfl
    show p (j * reStep eps p n ℓ * reDelta eps p n ℓ) =
      p (j * (reStep eps p n ℓ * reDelta eps p n ℓ))
    rw [Nat.mul_assoc]

theorem reKeys_fst (ℓ j : ℕ) : (reKeys eps p n ℓ).1 j = p (j * reDelta eps p n ℓ) := by
  rw [reKeys_eq]

theorem reKeys_snd (ℓ : ℕ) : (reKeys eps p n ℓ).2 = reSize eps p n ℓ := by
  rw [reKeys_eq]

/-- The step of the key-list run is `d_ℓ`. -/
theorem reStep_eq_keys (ℓ : ℕ) :
    reStep eps p n ℓ =
      (reKeys eps p n ℓ).2 / finSegCount eps (reKeys eps p n ℓ).1 (reKeys eps p n ℓ).2 := by
  rw [reKeys_eq]; rfl

/-! ### Segment counts and steps of the layers -/

variable (heps : 1 ≤ eps) (hn : 1 ≤ n)
include heps

theorem reSegs_le_ceilDiv_three (ℓ : ℕ) :
    reSegs eps p n ℓ ≤ reSize eps p n ℓ ⌈/⌉ 3 :=
  finSegCount_le_ceilDiv_three heps _ _

theorem reSegs_le_reSize (ℓ : ℕ) : reSegs eps p n ℓ ≤ reSize eps p n ℓ :=
  finSegCount_le_self heps _ _

/-- On a nontrivial layer `2 M_{ℓ+1} ≤ N_ℓ`. -/
theorem two_mul_reSegs_le {ℓ : ℕ} (h2 : 2 ≤ reSize eps p n ℓ) :
    2 * reSegs eps p n ℓ ≤ reSize eps p n ℓ :=
  two_mul_finSegCount_le heps _ h2

theorem reSegs_of_reSize_eq_one {ℓ : ℕ} (h1 : reSize eps p n ℓ = 1) :
    reSegs eps p n ℓ = 1 := by
  rw [reSegs, h1]; exact finSegCount_one heps _

theorem reStep_of_reSize_eq_one {ℓ : ℕ} (h1 : reSize eps p n ℓ = 1) :
    reStep eps p n ℓ = 1 := by
  rw [reStep, reSegs_of_reSize_eq_one heps h1, h1]

/-- A singleton layer is absorbing: `N_{ℓ+1} = 1` and `Δ_{ℓ+1} = Δ_ℓ`. -/
theorem reSize_succ_of_eq_one {ℓ : ℕ} (h1 : reSize eps p n ℓ = 1) :
    reSize eps p n (ℓ + 1) = 1 := by
  rw [reSize_succ, reStep_of_reSize_eq_one heps h1, h1]; rfl

theorem reDelta_succ_of_eq_one {ℓ : ℕ} (h1 : reSize eps p n ℓ = 1) :
    reDelta eps p n (ℓ + 1) = reDelta eps p n ℓ := by
  rw [reDelta_succ, reStep_of_reSize_eq_one heps h1, Nat.one_mul]

omit heps in
theorem one_le_reSegs_of_one_le {ℓ : ℕ} (h1 : 1 ≤ reSize eps p n ℓ) :
    1 ≤ reSegs eps p n ℓ :=
  one_le_finSegCount _ h1

/-- The `RELayer` certificate of `PLAStochastic.Index.Algorithm.RankPromotion` for a nontrivial layer. -/
def reRELayer {ℓ : ℕ} (h2 : 2 ≤ reSize eps p n ℓ) :
    RELayer (reSize eps p n ℓ) (reSegs eps p n ℓ) where
  segments_pos := one_le_reSegs_of_one_le (by omega)
  nonterminal := two_mul_reSegs_le heps h2
  next_eq := rfl

theorem two_le_reStep {ℓ : ℕ} (h2 : 2 ≤ reSize eps p n ℓ) : 2 ≤ reStep eps p n ℓ :=
  rankSpacing_two_le (one_le_reSegs_of_one_le (by omega)) (two_mul_reSegs_le heps h2)

omit heps in
theorem reStep_le_reSize (ℓ : ℕ) : reStep eps p n ℓ ≤ reSize eps p n ℓ :=
  Nat.div_le_self _ _

theorem one_le_reStep_of_one_le {ℓ : ℕ} (h1 : 1 ≤ reSize eps p n ℓ) :
    1 ≤ reStep eps p n ℓ :=
  Nat.div_pos (reSegs_le_reSize heps ℓ) (one_le_reSegs_of_one_le h1)

include hn

/-- Every layer is nonempty. -/
theorem one_le_reSize : ∀ ℓ, 1 ≤ reSize eps p n ℓ
  | 0 => hn
  | ℓ + 1 => by
    have h := one_le_reSize ℓ
    rw [reSize_succ]
    exact one_le_ceilDiv h (one_le_reStep_of_one_le heps h)

/-- `M_{ℓ+1} ≥ 1`. -/
theorem one_le_reSegs (ℓ : ℕ) : 1 ≤ reSegs eps p n ℓ :=
  one_le_reSegs_of_one_le (one_le_reSize heps hn ℓ)

/-- `d_ℓ ≥ 1`. -/
theorem one_le_reStep (ℓ : ℕ) : 1 ≤ reStep eps p n ℓ :=
  one_le_reStep_of_one_le heps (one_le_reSize heps hn ℓ)

theorem one_le_reDelta : ∀ ℓ, 1 ≤ reDelta eps p n ℓ
  | 0 => le_rfl
  | ℓ + 1 => by
    rw [reDelta_succ]
    exact Nat.one_le_iff_ne_zero.2
      (Nat.mul_ne_zero (by have := one_le_reStep (p := p) heps hn ℓ; omega)
        (by have := one_le_reDelta ℓ; omega))

/-- The promotion rule, literally: layer `ℓ + 1` keeps the layer-`ℓ` keys of rank
    `j * d_ℓ`, exactly for the ranks `j * d_ℓ < N_ℓ`. -/
theorem reKeys_promote (ℓ : ℕ) :
    (∀ j, (reKeys eps p n (ℓ + 1)).1 j = (reKeys eps p n ℓ).1 (j * reStep eps p n ℓ)) ∧
      (∀ j, j < (reKeys eps p n (ℓ + 1)).2 ↔ j * reStep eps p n ℓ < (reKeys eps p n ℓ).2) := by
  refine ⟨fun j => ?_, fun j => ?_⟩
  · rw [reStep_eq_keys]; rfl
  · rw [reKeys_snd, reKeys_snd, reSize_succ]
    exact lt_ceilDiv_iff_mul_lt (one_le_reStep heps hn ℓ)

/-- The one-step lattice bounds `(N_{ℓ+1} - 1) d_ℓ < N_ℓ ≤ N_{ℓ+1} d_ℓ`. -/
theorem re_step_lattice (ℓ : ℕ) :
    (reSize eps p n (ℓ + 1) - 1) * reStep eps p n ℓ < reSize eps p n ℓ ∧
      reSize eps p n ℓ ≤ reSize eps p n (ℓ + 1) * reStep eps p n ℓ := by
  rw [reSize_succ]
  exact ceilDiv_lattice (one_le_reSize heps hn ℓ) (one_le_reStep heps hn ℓ)

/-- `M_{ℓ+1} ≤ N_{ℓ+1} ≤ 2 M_{ℓ+1}` (eq:re-count-bracket), on every layer. -/
theorem reSize_succ_bounds (ℓ : ℕ) :
    reSegs eps p n ℓ ≤ reSize eps p n (ℓ + 1) ∧
      reSize eps p n (ℓ + 1) ≤ 2 * reSegs eps p n ℓ := by
  rcases Nat.lt_or_ge (reSize eps p n ℓ) 2 with h | h2
  · have h1 : reSize eps p n ℓ = 1 := by have := one_le_reSize (p := p) heps hn ℓ; omega
    rw [reSize_succ_of_eq_one heps h1, reSegs_of_reSize_eq_one heps h1]
    omega
  · exact (reRELayer heps h2).card_bounds

/-- Halving `N_{ℓ+1} ≤ ⌈N_ℓ / 2⌉`, on every layer. -/
theorem reSize_succ_le_half (ℓ : ℕ) :
    reSize eps p n (ℓ + 1) ≤ (reSize eps p n ℓ + 1) / 2 := by
  rcases Nat.lt_or_ge (reSize eps p n ℓ) 2 with h | h2
  · have h1 : reSize eps p n ℓ = 1 := by have := one_le_reSize (p := p) heps hn ℓ; omega
    rw [reSize_succ_of_eq_one heps h1, h1]
  · exact (reRELayer heps h2).halving

omit hn in
theorem reSize_succ_lt {ℓ : ℕ} (h2 : 2 ≤ reSize eps p n ℓ) :
    reSize eps p n (ℓ + 1) < reSize eps p n ℓ :=
  re_strict_contraction (one_le_reSegs_of_one_le (by omega)) (two_mul_reSegs_le heps h2) h2

/-! ### The rank lattice -/

/-- `(N_ℓ - 1) Δ_ℓ < n ≤ N_ℓ Δ_ℓ` (eq:re-lattice-size). -/
theorem re_cover : ∀ ℓ,
    (reSize eps p n ℓ - 1) * reDelta eps p n ℓ < n ∧ n ≤ reSize eps p n ℓ * reDelta eps p n ℓ
  | 0 => by simp; omega
  | ℓ + 1 => by
    obtain ⟨ih1, ih2⟩ := re_cover ℓ
    obtain ⟨h1, h2⟩ := re_step_lattice (p := p) heps hn ℓ
    rw [reDelta_succ, ← Nat.mul_assoc, ← Nat.mul_assoc]
    constructor
    · calc (reSize eps p n (ℓ + 1) - 1) * reStep eps p n ℓ * reDelta eps p n ℓ
          ≤ (reSize eps p n ℓ - 1) * reDelta eps p n ℓ :=
            Nat.mul_le_mul_right _ (by omega)
        _ < n := ih1
    · exact ih2.trans (Nat.mul_le_mul_right _ h2)

/-- `N_ℓ = ⌈n / Δ_ℓ⌉`. -/
theorem reSize_eq_ceilDiv (ℓ : ℕ) : reSize eps p n ℓ = n ⌈/⌉ reDelta eps p n ℓ :=
  eq_ceilDiv_of_lattice (one_le_reDelta heps hn ℓ) (re_cover heps hn ℓ).1 (re_cover heps hn ℓ).2

/-- On a nontrivial layer `Δ_ℓ < n`. -/
theorem reDelta_lt {ℓ : ℕ} (h2 : 2 ≤ reSize eps p n ℓ) : reDelta eps p n ℓ < n := by
  have h := (re_cover (p := p) heps hn ℓ).1
  have : reDelta eps p n ℓ ≤ (reSize eps p n ℓ - 1) * reDelta eps p n ℓ :=
    Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- `N_ℓ Δ_ℓ < 2n`, on every layer (including the singleton continuation). -/
theorem reSize_mul_reDelta_lt : ∀ ℓ, reSize eps p n ℓ * reDelta eps p n ℓ < 2 * n
  | 0 => by simp; omega
  | ℓ + 1 => by
    have ih := reSize_mul_reDelta_lt ℓ
    have hΔ : reDelta eps p n (ℓ + 1) < 2 * n := by
      rw [reDelta_succ]
      exact (Nat.mul_le_mul_right _ (reStep_le_reSize ℓ)).trans_lt ih
    rcases Nat.lt_or_ge (reSize eps p n (ℓ + 1)) 2 with h | h2
    · have h1 : reSize eps p n (ℓ + 1) = 1 := by
        have := one_le_reSize (p := p) heps hn (ℓ + 1); omega
      rw [h1, Nat.one_mul]; exact hΔ
    · have hc := (re_cover (p := p) heps hn (ℓ + 1)).1
      have hlt := reDelta_lt heps hn h2
      have heq : reSize eps p n (ℓ + 1) * reDelta eps p n (ℓ + 1) =
          (reSize eps p n (ℓ + 1) - 1) * reDelta eps p n (ℓ + 1) + reDelta eps p n (ℓ + 1) := by
        rw [Nat.sub_mul, Nat.one_mul, Nat.sub_add_cancel]
        exact Nat.le_mul_of_pos_left _ (by omega)
      omega

theorem reDelta_lt_two_mul (ℓ : ℕ) : reDelta eps p n ℓ < 2 * n :=
  (Nat.le_mul_of_pos_left _ (one_le_reSize heps hn ℓ)).trans_lt
    (reSize_mul_reDelta_lt heps hn ℓ)

/-- Every layer-`ℓ` key is an input key: `j Δ_ℓ < n` for `j < N_ℓ`. -/
theorem mul_reDelta_lt {ℓ j : ℕ} (hj : j < reSize eps p n ℓ) : j * reDelta eps p n ℓ < n :=
  (Nat.mul_le_mul_right _ (Nat.le_pred_of_lt hj)).trans_lt (re_cover heps hn ℓ).1

/-! ### eq:reduction -/

/-- **eq:reduction** `M_{ℓ+1} = PLAcount(Δ_ℓ, N_ℓ)`: if the input keys are the partial sums
    of the gaps `g` from `x0`, the layer-`ℓ` segment count is the segment count of the
    block-sum walk with block length `Δ_ℓ`. -/
theorem reSegs_eq_PLAcount {g : ℕ → ℝ} {x0 : ℝ}
    (hp : ∀ t < n, p t = x0 + ∑ i ∈ range t, g i) (ℓ : ℕ) :
    reSegs eps p n ℓ = PLAcount eps g (reDelta eps p n ℓ) (reSize eps p n ℓ) :=
  finSegCount_lattice_eq_PLAcount fun _ hj => hp _ (mul_reDelta_lt heps hn hj)

/-! ### The height -/

/-- Halving over `k` layers: `(N_{m+k} - 1) 2^k ≤ N_m - 1`. -/
theorem reSize_pred_mul_pow_le (m : ℕ) :
    ∀ k, (reSize eps p n (m + k) - 1) * 2 ^ k ≤ reSize eps p n m - 1
  | 0 => by simp
  | k + 1 => by
    have ih := reSize_pred_mul_pow_le m k
    have hh := reSize_succ_le_half (p := p) heps hn (m + k)
    have h1 := one_le_reSize (p := p) heps hn (m + k + 1)
    have h2 : 2 * (reSize eps p n (m + k + 1) - 1) ≤ reSize eps p n (m + k) - 1 := by omega
    rw [← Nat.add_assoc, pow_succ]
    calc (reSize eps p n (m + k + 1) - 1) * (2 ^ k * 2)
        = (2 * (reSize eps p n (m + k + 1) - 1)) * 2 ^ k := by ring
      _ ≤ (reSize eps p n (m + k) - 1) * 2 ^ k := Nat.mul_le_mul_right _ h2
      _ ≤ reSize eps p n m - 1 := ih

/-- From any layer `m`, the run reaches one key within `⌊log₂ N_m⌋ + 1` layers. -/
theorem reSize_add_log_eq_one (m : ℕ) :
    reSize eps p n (m + (Nat.log 2 (reSize eps p n m) + 1)) = 1 := by
  set k := Nat.log 2 (reSize eps p n m) + 1 with hk
  have hpow : reSize eps p n m < 2 ^ k := Nat.lt_pow_succ_log_self (by norm_num) _
  have h := reSize_pred_mul_pow_le (p := p) heps hn m k
  have h1 := one_le_reSize (p := p) heps hn (m + k)
  by_contra hne
  have : 2 ^ k ≤ (reSize eps p n (m + k) - 1) * 2 ^ k := Nat.le_mul_of_pos_left _ (by omega)
  omega

omit heps hn in
theorem reHeight_le {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (h : reSize eps p n ℓ = 1) :
    reHeight eps p n ≤ ℓ :=
  Nat.sInf_le ⟨hℓ, h⟩

/-- Existence of the terminal layer. -/
theorem exists_reSize_eq_one : ∃ ℓ, 1 ≤ ℓ ∧ (reLayer eps p n ℓ).2 = 1 :=
  ⟨0 + (Nat.log 2 (reSize eps p n 0) + 1), by omega, reSize_add_log_eq_one heps hn 0⟩

theorem reHeight_mem : 1 ≤ reHeight eps p n ∧ reSize eps p n (reHeight eps p n) = 1 :=
  Nat.sInf_mem (exists_reSize_eq_one heps hn)

theorem one_le_reHeight : 1 ≤ reHeight eps p n := (reHeight_mem heps hn).1

theorem reSize_reHeight : reSize eps p n (reHeight eps p n) = 1 := (reHeight_mem heps hn).2

/-- From the height on, every layer is the same singleton. -/
theorem reSize_eq_one_of_reHeight_le {ℓ : ℕ} (h : reHeight eps p n ≤ ℓ) :
    reSize eps p n ℓ = 1 := by
  induction ℓ, h using Nat.le_induction with
  | base => exact reSize_reHeight heps hn
  | succ ℓ _ ih => exact reSize_succ_of_eq_one heps ih

/-- Every layer `1 ≤ ℓ < H` is nontrivial. -/
theorem two_le_reSize_of_lt_reHeight {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (h : ℓ < reHeight eps p n) :
    2 ≤ reSize eps p n ℓ := by
  have hne : reSize eps p n ℓ ≠ 1 := fun h1 => absurd (reHeight_le hℓ h1) (not_le.2 h)
  have := one_le_reSize (p := p) heps hn ℓ
  omega

/-- For `n ≥ 2` every layer `ℓ < H` is nontrivial (for `n = 1`, `H = 1` and `N_0 = 1`). -/
theorem two_le_reSize_of_lt_reHeight' (hn2 : 2 ≤ n) {ℓ : ℕ} (h : ℓ < reHeight eps p n) :
    2 ≤ reSize eps p n ℓ := by
  rcases Nat.eq_zero_or_pos ℓ with h0 | hpos
  · subst h0; simpa using hn2
  · exact two_le_reSize_of_lt_reHeight heps hn hpos h

theorem lt_reHeight_iff {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    ℓ < reHeight eps p n ↔ 2 ≤ reSize eps p n ℓ := by
  refine ⟨two_le_reSize_of_lt_reHeight heps hn hℓ, fun h2 => ?_⟩
  by_contra hle
  have := reSize_eq_one_of_reHeight_le heps hn (not_lt.1 hle)
  omega

/-- **Height after a cutoff**: `H ≤ m + ⌊log₂ N_m⌋ + 1` for every layer `m`. -/
theorem reHeight_le_add_log (m : ℕ) :
    reHeight eps p n ≤ m + Nat.log 2 (reSize eps p n m) + 1 :=
  reHeight_le (by omega) (by rw [Nat.add_assoc]; exact reSize_add_log_eq_one heps hn m)

/-- The TeX form: after the cutoff layer `L`, halving finishes in
    `⌊log₂ N_{L+1}⌋ + 1` layers. -/
theorem reHeight_le_cutoff (L : ℕ) :
    reHeight eps p n ≤ L + 1 + Nat.log 2 (reSize eps p n (L + 1)) + 1 :=
  reHeight_le_add_log heps hn (L + 1)

/-- The deterministic bound `H ≤ ⌊log₂ n⌋ + 1`. -/
theorem reHeight_le_log : reHeight eps p n ≤ Nat.log 2 n + 1 := by
  simpa using reHeight_le_add_log heps hn 0

omit hn in
theorem reHeight_of_eq_one (h1 : n = 1) : reHeight eps p n = 1 := by
  have h := reHeight_le_log (p := p) (n := n) heps (by omega)
  have h' := one_le_reHeight (p := p) (n := n) heps (by omega)
  subst h1
  simp at h
  omega

end Run

/-- The actual ALG-RE run as a `REHierarchy` certificate of `PLAStochastic.Index.Algorithm.RankPromotion`
    (input `n ≥ 2`, layers below the height). -/
def reHierarchy {eps : ℝ} (heps : 1 ≤ eps) (p : ℕ → ℝ) {n : ℕ} (hn2 : 2 ≤ n) :
    REHierarchy n (reHeight eps p n) where
  size := reSize eps p n
  segments := reSegs eps p n
  delta := reDelta eps p n
  step := reStep eps p n
  base_pos := by omega
  size_zero := rfl
  delta_zero := rfl
  segments_pos := fun _ => one_le_reSegs heps (by omega) _
  nonterminal := fun hl =>
    two_mul_reSegs_le heps (two_le_reSize_of_lt_reHeight' heps (by omega) hn2 hl)
  step_eq := fun _ => rfl
  next_eq := fun _ => rfl
  delta_eq := fun _ => rfl

end

end PGM
