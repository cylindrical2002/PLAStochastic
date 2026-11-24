import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Real.Basic

/-!
# Deterministic rank-equispaced promotion

This file isolates the finite arithmetic used by the complete-coverage RE
rule.  No distributional or asymptotic assumption occurs here.  A layer with
`k` keys and `m` fitted segments uses `d = k / m`, promotes every rank `j*d`
that is below `k`, and has `ceil(k/d)` promoted keys.  The hypotheses
`0 < m` and `2*m ≤ k` are the non-terminal-layer assumptions under which the
paper invokes the rule.

The proofs deliberately keep the final partial bucket.  In particular,
`re_lattice` gives both sides of the exact ceiling identity and
`promotedRanks_mem_lt` shows that every index in the finite promoted list is
an actual input rank.  A hierarchy additionally exposes the exact
`size = ceil(n / delta)` formula and the `< 2*n` cover bound.  The
nonterminal inequality `2*m ≤ k` is an explicit input here; the separate
optimal-PLA argument that supplies it is not part of this arithmetic module.
The elementary implications from `m ≤ k / 2` or `m ≤ ceil(k / 3)` to
`2*m ≤ k` are included separately for that future bridge.
-/

namespace PGM

/-! ## One-layer definitions -/

/-- Rank spacing used by the complete rank-equispaced promotion rule. -/
def rankSpacing (k m : ℕ) : ℕ := k / m

/-- Number of promoted pivots, written using the order-theoretic ceiling
    division from Mathlib.  The definition is total; all structural lemmas
    below assume a positive spacing. -/
def reNextCount (k m : ℕ) : ℕ := k ⌈/⌉ rankSpacing k m

/-- The promoted input ranks, including the possibly shorter final bucket. -/
def promotedRanks (k m : ℕ) : Finset ℕ :=
  (Finset.range (reNextCount k m)).image (fun j => j * rankSpacing k m)

/-- The rank bucket containing an input rank. -/
def reBucket (k m i : ℕ) : ℕ := i / rankSpacing k m

/-! ## Spacing and ceiling arithmetic -/

theorem rankSpacing_pos {k m : ℕ} (hm : 0 < m) (h2 : 2 * m ≤ k) :
    0 < rankSpacing k m := by
  unfold rankSpacing
  exact Nat.div_pos (by omega) hm

theorem rankSpacing_two_le {k m : ℕ} (hm : 0 < m) (h2 : 2 * m ≤ k) :
    2 ≤ rankSpacing k m := by
  apply (Nat.le_div_iff_mul_le hm).2
  omega

theorem re_lattice {k m : ℕ} (hm : 0 < m) (h2 : 2 * m ≤ k) :
    (reNextCount k m - 1) * rankSpacing k m < k ∧
      k ≤ reNextCount k m * rankSpacing k m := by
  let d := rankSpacing k m
  have hd : 0 < d := rankSpacing_pos hm h2
  have hceil : k ≤ d * (k ⌈/⌉ d) := le_smul_ceilDiv hd
  have hleft : (k ⌈/⌉ d - 1) * d < k := by
    by_contra h
    have hle : k ≤ (k ⌈/⌉ d - 1) * d := Nat.le_of_not_gt h
    have hc : k ⌈/⌉ d ≤ k ⌈/⌉ d - 1 :=
      (ceilDiv_le_iff_le_mul hd).2 (by simpa [Nat.mul_comm] using hle)
    have hq : 0 < k ⌈/⌉ d := by
      by_contra hz
      have hz0 : k ⌈/⌉ d = 0 := Nat.eq_zero_of_not_pos hz
      have hk0 : k ≤ 0 := by simpa [hz0] using hceil
      omega
    exact (Nat.not_le_of_gt (Nat.sub_lt hq Nat.zero_lt_one)) hc
  exact ⟨by simpa [reNextCount, d, Nat.mul_comm] using hleft,
    by simpa [reNextCount, d, Nat.mul_comm] using hceil⟩

theorem re_next_lower {k m : ℕ} (hm : 0 < m) (h2 : 2 * m ≤ k) :
    m ≤ reNextCount k m := by
  let d := rankSpacing k m
  have hd : 0 < d := rankSpacing_pos hm h2
  have hfloor : m ≤ k / d := (Nat.le_div_iff_mul_le hd).2 (by
    have h := Nat.div_mul_le_self k m
    simpa [d, rankSpacing, Nat.mul_comm] using h)
  have hfc : k / d ≤ k ⌈/⌉ d := by
    simpa [Nat.floorDiv_eq_div] using
      (floorDiv_le_ceilDiv (a := d) (b := k))
  simpa [reNextCount, d] using hfloor.trans hfc

theorem re_next_upper {k m : ℕ} (hm : 0 < m) (h2 : 2 * m ≤ k) :
    reNextCount k m ≤ 2 * m := by
  let d := rankSpacing k m
  have hd : 0 < d := rankSpacing_pos hm h2
  have hd1 : 1 ≤ d := by omega
  have hlt : k < (d + 1) * m := by
    apply (Nat.div_lt_iff_lt_mul hm).mp
    exact Nat.lt_succ_self d
  have hdd : d + 1 ≤ 2 * d := by omega
  have hbound : (d + 1) * m ≤ (2 * m) * d := by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      (Nat.mul_le_mul_right m hdd)
  have hk : k ≤ d * (2 * m) := by
    exact (hlt.trans_le (by simpa [Nat.mul_comm] using hbound)).le
  exact (ceilDiv_le_iff_le_mul hd).2 hk

/-!
The denominator is at least two on every non-terminal layer.  Comparing the
ceiling divisions by `d` and by `2` gives the clean deterministic contraction
used by both RE height proofs.
-/
theorem re_halving {k m : ℕ} (hm : 0 < m) (h2 : 2 * m ≤ k) :
    reNextCount k m ≤ (k + 1) / 2 := by
  let d := rankSpacing k m
  have hd : 0 < d := rankSpacing_pos hm h2
  have hd2 : 2 ≤ d := rankSpacing_two_le hm h2
  have ht : k ≤ d * (k ⌈/⌉ 2) := by
    have hbase : k ≤ 2 * (k ⌈/⌉ 2) :=
      le_smul_ceilDiv (by omega : 0 < (2 : ℕ))
    have hmul : 2 * (k ⌈/⌉ 2) ≤ d * (k ⌈/⌉ 2) := by
      exact Nat.mul_le_mul_right _ hd2
    exact hbase.trans hmul
  have hceil : k ⌈/⌉ d ≤ k ⌈/⌉ 2 :=
    (ceilDiv_le_iff_le_mul hd).2 (by simpa [Nat.mul_comm] using ht)
  have hrewrite : k ⌈/⌉ 2 = (k + 1) / 2 := by
    rw [Nat.ceilDiv_eq_add_pred_div]
    omega
  simpa [reNextCount, d] using hceil.trans_eq hrewrite

theorem re_strict_contraction {k m : ℕ} (hm : 0 < m) (h2 : 2 * m ≤ k)
    (hk : 2 ≤ k) :
    reNextCount k m < k := by
  have hh := re_halving hm h2
  have hceil : (k + 1) / 2 < k := by
    apply (Nat.div_lt_iff_lt_mul (by omega : 0 < (2 : ℕ))).2
    omega
  exact hh.trans_lt hceil

/-! ## Promoted lattice and the tail bucket -/

theorem promotedRanks_card {k m : ℕ} (hm : 0 < m) (h2 : 2 * m ≤ k) :
    (promotedRanks k m).card = reNextCount k m := by
  unfold promotedRanks
  calc
    (Finset.image (fun j => j * rankSpacing k m)
        (Finset.range (reNextCount k m))).card =
        (Finset.range (reNextCount k m)).card := by
      apply Finset.card_image_iff.mpr
      intro a ha b hb hab
      exact Nat.mul_right_cancel (rankSpacing_pos hm h2) (by simpa using hab)
    _ = reNextCount k m := Finset.card_range _

theorem promotedRanks_mem_lt {k m j : ℕ} (hm : 0 < m) (h2 : 2 * m ≤ k)
    (hj : j ∈ Finset.range (reNextCount k m)) :
    j * rankSpacing k m < k := by
  have hd : 0 < rankSpacing k m := rankSpacing_pos hm h2
  have hq : j < reNextCount k m := Finset.mem_range.mp hj
  have hleft : (reNextCount k m - 1) * rankSpacing k m < k :=
    (re_lattice hm h2).1
  have hjpred : j ≤ reNextCount k m - 1 := Nat.le_pred_of_lt hq
  have hmono : j * rankSpacing k m ≤
      (reNextCount k m - 1) * rankSpacing k m := by
    exact Nat.mul_le_mul_right _ hjpred
  exact hmono.trans_lt hleft

theorem promotedRanks_complete {k m : ℕ} (hm : 0 < m) (h2 : 2 * m ≤ k) :
    ∀ j ∈ Finset.range (reNextCount k m),
      j * rankSpacing k m < k := by
  intro j hj
  exact promotedRanks_mem_lt hm h2 hj

theorem promoted_rank_iff {k m j : ℕ} (hm : 0 < m) (h2 : 2 * m ≤ k) :
    j * rankSpacing k m < k ↔ j < reNextCount k m := by
  constructor
  · intro hj
    by_contra hnot
    have hqj : reNextCount k m ≤ j := Nat.le_of_not_gt hnot
    have hmono : reNextCount k m * rankSpacing k m ≤
        j * rankSpacing k m := by
      exact Nat.mul_le_mul_right _ hqj
    exact (Nat.not_lt_of_ge (re_lattice hm h2).2) (hmono.trans_lt hj)
  · intro hj
    exact promotedRanks_mem_lt hm h2 (Finset.mem_range.mpr hj)

theorem re_bucket_bounds {k m i : ℕ} (hm : 0 < m) (h2 : 2 * m ≤ k)
    (_hi : i < k) :
    reBucket k m i * rankSpacing k m ≤ i ∧
      i < (reBucket k m i + 1) * rankSpacing k m := by
  let d := rankSpacing k m
  have hd : 0 < d := rankSpacing_pos hm h2
  have hlo : i / d * d ≤ i := Nat.div_mul_le_self i d
  have hhi : i < (i / d + 1) * d := by
    apply (Nat.div_lt_iff_lt_mul hd).mp
    exact Nat.lt_succ_self (i / d)
  simpa [reBucket, d] using And.intro hlo hhi

theorem reBucket_lt_next {k m i : ℕ} (hm : 0 < m) (h2 : 2 * m ≤ k)
    (hi : i < k) :
    reBucket k m i < reNextCount k m := by
  let d := rankSpacing k m
  have hd : 0 < d := rankSpacing_pos hm h2
  have hupper : k ≤ reNextCount k m * d := (re_lattice hm h2).2
  have hil : i < reNextCount k m * d :=
    hi.trans_le (by simpa [reNextCount, d, Nat.mul_comm] using hupper)
  have hdiv : i / d < reNextCount k m :=
    (Nat.div_lt_iff_lt_mul hd).2 (by simpa [Nat.mul_comm] using hil)
  simpa [reBucket, d] using hdiv

/-! ## A finite layer certificate -/

/-- A one-step RE layer certificate.  Keeping the equalities as fields makes
    it convenient to chain certificates while preserving the exact tail
    convention. -/
structure RELayer (k m : ℕ) where
  segments_pos : 0 < m
  nonterminal : 2 * m ≤ k
  next : ℕ := reNextCount k m
  next_eq : next = reNextCount k m

theorem nonterminal_of_half_count {k m : ℕ} (hhalf : m ≤ k / 2) :
    2 * m ≤ k := by
  have h := (Nat.le_div_iff_mul_le (by decide : 0 < (2 : ℕ))).mp hhalf
  simpa [Nat.mul_comm] using h

theorem ceil_div_three_le_floor_half {k : ℕ} (h2 : 2 ≤ k) :
    k ⌈/⌉ 3 ≤ k / 2 := by
  rw [Nat.ceilDiv_eq_add_pred_div]
  apply (Nat.div_le_iff_le_mul (by decide : 0 < (3 : ℕ))).2
  omega

theorem nonterminal_of_three_cover {k m : ℕ} (h2 : 2 ≤ k)
    (hcount : m ≤ k ⌈/⌉ 3) : 2 * m ≤ k := by
  have hhalf : m ≤ k / 2 := hcount.trans (ceil_div_three_le_floor_half h2)
  exact nonterminal_of_half_count hhalf

def RELayer.of_half_count {k m : ℕ} (hm : 0 < m)
    (hhalf : m ≤ k / 2) : RELayer k m := by
  have h2 := nonterminal_of_half_count hhalf
  exact { segments_pos := hm, nonterminal := h2, next_eq := rfl }

def RELayer.of_three_cover {k m : ℕ} (hm : 0 < m) (h2 : 2 ≤ k)
    (hcount : m ≤ k ⌈/⌉ 3) : RELayer k m := by
  exact RELayer.of_half_count hm (hcount.trans (ceil_div_three_le_floor_half h2))

theorem RELayer.lattice {k m : ℕ} (L : RELayer k m) :
    (L.next - 1) * rankSpacing k m < k ∧
      k ≤ L.next * rankSpacing k m := by
  simpa [L.next_eq] using re_lattice L.segments_pos L.nonterminal

theorem RELayer.card_bounds {k m : ℕ} (L : RELayer k m) :
    m ≤ L.next ∧ L.next ≤ 2 * m := by
  simpa [L.next_eq] using
    (And.intro (re_next_lower L.segments_pos L.nonterminal)
      (re_next_upper L.segments_pos L.nonterminal))

theorem RELayer.halving {k m : ℕ} (L : RELayer k m) :
    L.next ≤ (k + 1) / 2 := by
  simpa [L.next_eq] using re_halving L.segments_pos L.nonterminal

/-! ## Finite hierarchies -/

/--
A finite prefix of the complete RE hierarchy.  `size l` is the number of
keys at layer `l`, `segments l` is the number of PLA segments fitted there,
and `delta l` is the cumulative rank spacing from the original input.  The
fields intentionally expose the update equalities instead of hiding them in a
recursive executable definition.  This makes the object suitable as a
certificate supplied by a probabilistic development later on.
-/
structure REHierarchy (n h : ℕ) where
  size : ℕ → ℕ
  segments : ℕ → ℕ
  delta : ℕ → ℕ
  step : ℕ → ℕ
  base_pos : 0 < n
  size_zero : size 0 = n
  delta_zero : delta 0 = 1
  segments_pos : ∀ {l}, l < h → 0 < segments l
  nonterminal : ∀ {l}, l < h → 2 * segments l ≤ size l
  step_eq : ∀ {l}, l < h → step l = rankSpacing (size l) (segments l)
  next_eq : ∀ {l}, l < h → size (l + 1) = reNextCount (size l) (segments l)
  delta_eq : ∀ {l}, l < h → delta (l + 1) = step l * delta l

/-- The original-input rank represented by a pivot at a finite layer. -/
def pivotRank {n h : ℕ} (H : REHierarchy n h) (l j : ℕ) : ℕ :=
  j * H.delta l

namespace REHierarchy

theorem layer_spacing_pos {n h : ℕ} (H : REHierarchy n h) {l : ℕ}
    (hl : l < h) : 0 < H.step l := by
  rw [H.step_eq hl]
  exact rankSpacing_pos (H.segments_pos hl) (H.nonterminal hl)

theorem layer_spacing_two_le {n h : ℕ} (H : REHierarchy n h) {l : ℕ}
    (hl : l < h) : 2 ≤ H.step l := by
  rw [H.step_eq hl]
  exact rankSpacing_two_le (H.segments_pos hl) (H.nonterminal hl)

theorem layer_next_bounds {n h : ℕ} (H : REHierarchy n h) {l : ℕ}
    (hl : l < h) :
    H.segments l ≤ H.size (l + 1) ∧ H.size (l + 1) ≤ 2 * H.segments l := by
  rw [H.next_eq hl]
  exact And.intro (re_next_lower (H.segments_pos hl) (H.nonterminal hl))
    (re_next_upper (H.segments_pos hl) (H.nonterminal hl))

theorem layer_lattice {n h : ℕ} (H : REHierarchy n h) {l : ℕ}
    (hl : l < h) :
    (H.size (l + 1) - 1) * H.step l < H.size l ∧
      H.size l ≤ H.size (l + 1) * H.step l := by
  have hlat := re_lattice (H.segments_pos hl) (H.nonterminal hl)
  rw [H.next_eq hl, H.step_eq hl]
  simpa [Nat.mul_comm] using hlat

theorem step_le_pred_of_next_ge_two {n h : ℕ} (H : REHierarchy n h)
    {l : ℕ} (hl : l < h) (hnext : 2 ≤ H.size (l + 1)) :
    H.step l ≤ H.size l - 1 := by
  have hlat := H.layer_lattice hl
  have hfactor : H.step l ≤ (H.size (l + 1) - 1) * H.step l := by
    simpa using
      (Nat.mul_le_mul_right (H.step l)
        (by omega : 1 ≤ H.size (l + 1) - 1))
  have hlt : H.step l < H.size l := hfactor.trans_lt hlat.1
  exact Nat.le_pred_of_lt hlt

theorem layer_promoted_complete {n h : ℕ} (H : REHierarchy n h) {l : ℕ}
    (hl : l < h) :
    ∀ j ∈ Finset.range (H.size (l + 1)), j * H.step l < H.size l := by
  intro j hj
  rw [H.step_eq hl]
  apply promotedRanks_mem_lt (H.segments_pos hl) (H.nonterminal hl)
  simpa [H.next_eq hl] using hj

theorem layer_halving {n h : ℕ} (H : REHierarchy n h) {l : ℕ}
    (hl : l < h) : H.size (l + 1) ≤ (H.size l + 1) / 2 := by
  rw [H.next_eq hl]
  exact re_halving (H.segments_pos hl) (H.nonterminal hl)

theorem layer_strict_contraction {n h : ℕ} (H : REHierarchy n h) {l : ℕ}
    (hl : l < h) : H.size (l + 1) < H.size l := by
  have hm := H.segments_pos hl
  have h2 := H.nonterminal hl
  have hs : 1 ≤ H.segments l := by omega
  have hk : 2 ≤ H.size l := by
    exact le_trans (by omega) h2
  rw [H.next_eq hl]
  exact re_strict_contraction (H.segments_pos hl) (H.nonterminal hl) hk

theorem size_pos {n h : ℕ} (H : REHierarchy n h) :
    ∀ {l}, l ≤ h → 0 < H.size l := by
  intro l hl
  induction l with
  | zero => simpa [H.size_zero] using H.base_pos
  | succ l ih =>
      have hlh : l < h := by omega
      rw [H.next_eq hlh]
      have hm := H.segments_pos hlh
      have hlow := re_next_lower (H.segments_pos hlh) (H.nonterminal hlh)
      exact lt_of_lt_of_le hm hlow

theorem delta_pos {n h : ℕ} (H : REHierarchy n h) :
    ∀ {l}, l ≤ h → 0 < H.delta l := by
  intro l hl
  induction l with
  | zero => simp [H.delta_zero]
  | succ l ih =>
      have hlh : l < h := by omega
      rw [H.delta_eq hlh]
      exact Nat.mul_pos (H.layer_spacing_pos hlh) (ih (by omega))

theorem last_pivot_lt {n h : ℕ} (H : REHierarchy n h) :
    ∀ {l}, l ≤ h → (H.size l - 1) * H.delta l < n := by
  intro l hl
  induction l with
  | zero =>
      simpa [H.size_zero, H.delta_zero] using Nat.pred_lt_self H.base_pos
  | succ l ih =>
      have hlh : l < h := by omega
      have hprev := ih (by omega)
      have hlat := (re_lattice (H.segments_pos hlh) (H.nonterminal hlh)).1
      have hstep : (H.size (l + 1) - 1) * H.step l ≤ H.size l - 1 := by
        have hlt : (H.size (l + 1) - 1) * H.step l < H.size l := by
          simpa [H.next_eq hlh, H.step_eq hlh] using hlat
        exact Nat.le_pred_of_lt hlt
      have hmul : (H.size (l + 1) - 1) * H.delta (l + 1) ≤
          (H.size l - 1) * H.delta l := by
        rw [H.delta_eq hlh]
        calc
          (H.size (l + 1) - 1) * (H.step l * H.delta l) =
              ((H.size (l + 1) - 1) * H.step l) * H.delta l := by
                simp [Nat.mul_assoc]
          _ ≤ (H.size l - 1) * H.delta l :=
            Nat.mul_le_mul_right _ hstep
      exact hmul.trans_lt hprev

theorem delta_lt_base_of_nonterminal {n h : ℕ} (H : REHierarchy n h) :
    ∀ {l}, l < h → H.delta l < n := by
  intro l hl
  induction l with
  | zero =>
      rw [H.delta_zero]
      have hs : 0 < H.segments 0 := H.segments_pos hl
      have hn := H.nonterminal hl
      rw [H.size_zero] at hn
      omega
  | succ l ih =>
      have hlprev : l < h := by omega
      have htarget : 2 ≤ H.size (l + 1) := by
        have hs : 0 < H.segments (l + 1) := H.segments_pos hl
        have hn := H.nonterminal hl
        omega
      have hstep := H.step_le_pred_of_next_ge_two hlprev htarget
      rw [H.delta_eq hlprev]
      have hmul : H.step l * H.delta l ≤
          (H.size l - 1) * H.delta l :=
        Nat.mul_le_mul_right _ hstep
      exact hmul.trans_lt (H.last_pivot_lt (by omega))

theorem delta_lt_two_base {n h : ℕ} (H : REHierarchy n h) :
    ∀ {l}, l ≤ h → H.delta l < 2 * n := by
  intro l hl
  induction l with
  | zero =>
      rw [H.delta_zero]
      have hn := H.base_pos
      omega
  | succ l ih =>
      have hlprev : l < h := by omega
      have hdelta : H.delta l < n := H.delta_lt_base_of_nonterminal hlprev
      have hstep : H.step l ≤ H.size l := by
        rw [H.step_eq hlprev]
        exact Nat.div_le_self _ _
      have hmul : H.step l * H.delta l ≤ H.size l * H.delta l :=
        Nat.mul_le_mul_right _ hstep
      have hspos : 0 < H.size l := H.size_pos (by omega)
      have heq : H.size l * H.delta l =
          (H.size l - 1) * H.delta l + H.delta l := by
        calc
          H.size l * H.delta l = (H.size l - 1 + 1) * H.delta l := by
            rw [Nat.sub_add_cancel hspos]
          _ = (H.size l - 1) * H.delta l + H.delta l := by
            simp [Nat.add_mul]
      have hsum : H.size l * H.delta l < n + H.delta l := by
        rw [heq]
        exact Nat.add_lt_add_right (H.last_pivot_lt (by omega)) _
      rw [H.delta_eq hlprev]
      have hnext : H.step l * H.delta l < 2 * n := by
        exact hmul.trans_lt (hsum.trans (by omega))
      exact hnext

theorem cover_lt_two_base {n h : ℕ} (H : REHierarchy n h) :
    ∀ {l}, l ≤ h → H.size l * H.delta l < 2 * n := by
  intro l hl
  by_cases hsone : H.size l = 1
  · rw [hsone, Nat.one_mul]
    exact H.delta_lt_two_base hl
  · have hsizepos : 0 < H.size l := H.size_pos hl
    have hs : 2 ≤ H.size l := by omega
    have hdelta : H.delta l < n := by
      cases l with
      | zero =>
          rw [H.delta_zero]
          rw [H.size_zero] at hs
          omega
      | succ p =>
          have hp : p < h := Nat.lt_of_succ_le hl
          have hstep := H.step_le_pred_of_next_ge_two hp (by simpa using hs)
          rw [H.delta_eq hp]
          have hmul : H.step p * H.delta p ≤
              (H.size p - 1) * H.delta p :=
            Nat.mul_le_mul_right _ hstep
          exact hmul.trans_lt (H.last_pivot_lt (by omega))
    have hspos : 0 < H.size l := by omega
    have heq : H.size l * H.delta l =
        (H.size l - 1) * H.delta l + H.delta l := by
      calc
        H.size l * H.delta l = (H.size l - 1 + 1) * H.delta l := by
          rw [Nat.sub_add_cancel hspos]
        _ = (H.size l - 1) * H.delta l + H.delta l := by
          simp [Nat.add_mul]
    rw [heq]
    exact (Nat.add_lt_add_right (H.last_pivot_lt hl) _).trans (by omega)

theorem first_pivot_cover {n h : ℕ} (H : REHierarchy n h) :
    ∀ {l}, l ≤ h → n ≤ H.size l * H.delta l := by
  intro l hl
  induction l with
  | zero =>
      rw [H.size_zero, H.delta_zero]
      simp
  | succ l ih =>
      have hlh : l < h := by omega
      have hprev := ih (by omega)
      have hlat := (re_lattice (H.segments_pos hlh) (H.nonterminal hlh)).2
      have hlat' : H.size l ≤ H.size (l + 1) * H.step l := by
        rw [H.next_eq hlh, H.step_eq hlh]
        simpa [Nat.mul_comm] using hlat
      have hmul : H.size l * H.delta l ≤
          (H.size (l + 1) * H.step l) * H.delta l := by
        exact Nat.mul_le_mul_right _ hlat'
      calc
        n ≤ H.size l * H.delta l := hprev
        _ ≤ (H.size (l + 1) * H.step l) * H.delta l := hmul
        _ = H.size (l + 1) * H.delta (l + 1) := by
          rw [H.delta_eq hlh]
          simp [Nat.mul_left_comm, Nat.mul_comm]

theorem layer_cover_bounds {n h : ℕ} (H : REHierarchy n h) :
    ∀ {l}, l ≤ h →
      (H.size l - 1) * H.delta l < n ∧
        n ≤ H.size l * H.delta l := by
  intro l hl
  exact ⟨H.last_pivot_lt hl, H.first_pivot_cover hl⟩

theorem layer_cover_bounds_real {n h : ℕ} (H : REHierarchy n h) :
    ∀ {l}, l ≤ h →
      (((H.size l - 1 : ℕ) : ℝ) * (H.delta l : ℝ)) < (n : ℝ) ∧
        (n : ℝ) ≤ ((H.size l : ℝ) * (H.delta l : ℝ)) := by
  intro l hl
  have hnat := H.layer_cover_bounds hl
  constructor
  · exact_mod_cast hnat.1
  · exact_mod_cast hnat.2

theorem size_eq_ceilDiv_delta {n h : ℕ} (H : REHierarchy n h) :
    ∀ {l}, l ≤ h → H.size l = n ⌈/⌉ H.delta l := by
  intro l hl
  have hd : 0 < H.delta l := H.delta_pos hl
  have hcover := H.layer_cover_bounds hl
  have hupper : n ⌈/⌉ H.delta l ≤ H.size l := by
    apply (ceilDiv_le_iff_le_mul hd).2
    simpa [Nat.mul_comm] using hcover.2
  have hlower : H.size l ≤ n ⌈/⌉ H.delta l := by
    by_contra hnot
    have hq : n ⌈/⌉ H.delta l ≤ H.size l - 1 := by
      exact Nat.le_pred_of_lt (Nat.lt_of_not_ge hnot)
    have hmul : H.delta l * (n ⌈/⌉ H.delta l) ≤
        H.delta l * (H.size l - 1) :=
      Nat.mul_le_mul_left _ hq
    have hnle : n ≤ H.delta l * (n ⌈/⌉ H.delta l) := by
      simpa [Nat.mul_comm] using (le_smul_ceilDiv hd : n ≤ H.delta l * (n ⌈/⌉ H.delta l))
    have hcontra : n ≤ (H.size l - 1) * H.delta l := by
      exact hnle.trans (by simpa [Nat.mul_comm] using hmul)
    exact (Nat.not_lt_of_ge hcontra) hcover.1
  exact Nat.le_antisymm hlower hupper

theorem pivot_rank_lt {n h : ℕ} (H : REHierarchy n h) {l j : ℕ}
    (hl : l ≤ h) (hj : j < H.size l) : pivotRank H l j < n := by
  have hpred : j ≤ H.size l - 1 := Nat.le_pred_of_lt hj
  have hmul : pivotRank H l j ≤ (H.size l - 1) * H.delta l := by
    exact Nat.mul_le_mul_right _ hpred
  exact hmul.trans_lt (H.last_pivot_lt hl)

theorem pivot_rank_formula {n h : ℕ} (H : REHierarchy n h) (l j : ℕ) :
    pivotRank H l j = j * H.delta l := rfl

end REHierarchy

end PGM
