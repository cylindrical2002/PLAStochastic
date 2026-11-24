import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! # The combinatorial Sparre Andersen theorem (roadmap 1.2, target A)

For a list `p` of indices with weights `x : ι → ℝ` let `S_j = x(p₁)+⋯+x(p_j)`,
`N(p) = #{1 ≤ j ≤ |p| : S_j > 0}` and `T(p) = k` iff `k` is the **first** argmax of
`S_0, …, S_{|p|}`.  Then for every `k` and every finite set `P` of lists closed under
permutation (`p ∈ P ↔ p ~ l`),

  `#{p ∈ P : N(p) = k} = #{p ∈ P : T(p) = k}`.

No genericity assumption and no induction on `n` is used.  The proof is a chain of
three bijections:

1. `p ↦ (α, β)` with `α` the elements at positive times and `β` the others (in order);
   `α` has all partial sums `> 0`, `β` all partial sums `≤ 0`, and `p` is recovered from
   `(α, β)` because the last element is determined by the sign of the total sum
   (`posSplit_eq_of_perm`, `exists_posSplit_eq`).
2. `p ↦ (p.take k, p.drop k)`: `T(p) = k` iff `T(p.take k) = k` and `p.drop k` has all
   partial sums `≤ 0` (`isFirstArgmax_iff_split`).
3. reversal: `α` has all partial sums `> 0` iff `α.reverse` has its first argmax at the
   end (`isFirstArgmax_reverse_iff`).

(The cyclic-shift version of the lemma is false; see `ROADMAP-I1-44.md`.)
-/
noncomputable section
open Classical
open scoped List
namespace SwingRepair
namespace Fluctuation

variable {ι : Type*} (x : ι → ℝ)

/-- Partial sum of the first `j` increments. -/
def psum (p : List ι) (j : ℕ) : ℝ := ((p.take j).map x).sum

/-- All partial sums `S_1, …, S_{|p|}` are positive. -/
def AllPos (p : List ι) : Prop := ∀ j, 1 ≤ j → j ≤ p.length → 0 < psum x p j

/-- All partial sums are `≤ 0`. -/
def AllNonpos (p : List ι) : Prop := ∀ j, psum x p j ≤ 0

/-- `k` is the first argmax of `S_0, …, S_{|p|}`. -/
def IsFirstArgmax (p : List ι) (k : ℕ) : Prop :=
  k ≤ p.length ∧ (∀ i < k, psum x p i < psum x p k) ∧ ∀ i, psum x p i ≤ psum x p k

/-- Number of positive partial sums. -/
def posCount (p : List ι) : ℕ :=
  ((Finset.range p.length).filter fun j => 0 < psum x p (j + 1)).card

/-! ### Partial sums -/

@[simp] theorem psum_zero (p : List ι) : psum x p 0 = 0 := by simp [psum]

@[simp] theorem psum_nil (j : ℕ) : psum x ([] : List ι) j = 0 := by simp [psum]

theorem psum_of_length_le {p : List ι} {j : ℕ} (h : p.length ≤ j) :
    psum x p j = (p.map x).sum := by
  simp [psum, List.take_of_length_le h]

theorem psum_length (p : List ι) : psum x p p.length = (p.map x).sum :=
  psum_of_length_le x le_rfl

theorem psum_append_of_le {q r : List ι} {j : ℕ} (h : j ≤ q.length) :
    psum x (q ++ r) j = psum x q j := by
  simp [psum, List.take_append_of_le_length h]

theorem psum_append_add (q r : List ι) (j : ℕ) :
    psum x (q ++ r) (q.length + j) = (q.map x).sum + psum x r j := by
  simp [psum, List.take_append, List.take_of_length_le]

theorem psum_append_of_length_le {q r : List ι} {i : ℕ} (h : q.length ≤ i) :
    psum x (q ++ r) i = (q.map x).sum + psum x r (i - q.length) := by
  have : i = q.length + (i - q.length) := by omega
  rw [this, psum_append_add]
  simp

theorem psum_append_singleton_of_le {q : List ι} {i : ι} {j : ℕ} (h : j ≤ q.length) :
    psum x (q ++ [i]) j = psum x q j := psum_append_of_le x h

theorem psum_append_singleton_of_lt {q : List ι} {i : ι} {j : ℕ} (h : q.length < j) :
    psum x (q ++ [i]) j = (q.map x).sum + x i := by
  rw [psum_of_length_le x (by simp; omega)]
  simp

theorem psum_reverse (p : List ι) (j : ℕ) :
    psum x p.reverse j = (p.map x).sum - psum x p (p.length - j) := by
  unfold psum
  rw [List.take_reverse, List.map_reverse, List.sum_reverse]
  have := List.take_append_drop (p.length - j) p
  have hsum : ((p.take (p.length - j)).map x).sum + ((p.drop (p.length - j)).map x).sum
      = (p.map x).sum := by
    rw [← List.sum_append, ← List.map_append, this]
  linarith

theorem psum_le_sum_of_allPos {p : List ι} (h : AllPos x p) : 0 ≤ (p.map x).sum := by
  rcases p.eq_nil_or_concat with rfl | ⟨q, i, rfl⟩
  · simp
  · rw [List.concat_eq_append] at h ⊢
    have := h (q ++ [i]).length (by simp) le_rfl
    rw [psum_length] at this
    exact this.le

theorem sum_nonpos_of_allNonpos {p : List ι} (h : AllNonpos x p) : (p.map x).sum ≤ 0 := by
  have := h p.length
  rwa [psum_length] at this

theorem allPos_append_singleton (q : List ι) (i : ι) :
    AllPos x (q ++ [i]) ↔ AllPos x q ∧ 0 < (q.map x).sum + x i := by
  constructor
  · intro h
    refine ⟨fun j hj1 hj2 => ?_, ?_⟩
    · have := h j hj1 (by simp; omega)
      rwa [psum_append_singleton_of_le x hj2] at this
    · have := h (q.length + 1) (by omega) (by simp)
      rwa [psum_append_singleton_of_lt x (by omega)] at this
  · rintro ⟨h, hs⟩ j hj1 hj2
    simp at hj2
    rcases Nat.lt_or_ge q.length j with hlt | hle
    · rw [psum_append_singleton_of_lt x hlt]; exact hs
    · rw [psum_append_singleton_of_le x hle]; exact h j hj1 hle

theorem allNonpos_append_singleton (q : List ι) (i : ι) :
    AllNonpos x (q ++ [i]) ↔ AllNonpos x q ∧ (q.map x).sum + x i ≤ 0 := by
  constructor
  · intro h
    refine ⟨fun j => ?_, ?_⟩
    · rcases Nat.lt_or_ge q.length j with hlt | hle
      · rw [psum_of_length_le x hlt.le]
        have := h q.length
        rwa [psum_append_singleton_of_le x le_rfl, psum_length] at this
      · have := h j
        rwa [psum_append_singleton_of_le x hle] at this
    · have := h (q.length + 1)
      rwa [psum_append_singleton_of_lt x (by omega)] at this
  · rintro ⟨h, hs⟩ j
    rcases Nat.lt_or_ge q.length j with hlt | hle
    · rw [psum_append_singleton_of_lt x hlt]; exact hs
    · rw [psum_append_singleton_of_le x hle]; exact h j

theorem posCount_append_singleton (q : List ι) (i : ι) :
    posCount x (q ++ [i]) = posCount x q + if 0 < (q.map x).sum + x i then 1 else 0 := by
  unfold posCount
  rw [List.length_append, List.length_singleton, Finset.range_add_one, Finset.filter_insert]
  have hcongr : (Finset.range q.length).filter (fun j => 0 < psum x (q ++ [i]) (j + 1)) =
      (Finset.range q.length).filter (fun j => 0 < psum x q (j + 1)) := by
    apply Finset.filter_congr
    intro j hj
    rw [Finset.mem_range] at hj
    rw [psum_append_singleton_of_le x (by omega)]
  rw [psum_append_singleton_of_lt x (by omega)]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp), hcongr]
  · rw [hcongr, add_zero]

theorem posCount_le_length (p : List ι) : posCount x p ≤ p.length := by
  unfold posCount
  exact (Finset.card_filter_le _ _).trans (by simp)

/-! ### The positive/nonpositive split -/

/-- Processes the reversed list: the last element goes to the positive part iff the
total sum is positive. -/
def posSplitRev : List ι → List ι × List ι
  | [] => ([], [])
  | i :: r =>
      let s := posSplitRev r
      if 0 < (r.map x).sum + x i then (s.1 ++ [i], s.2) else (s.1, s.2 ++ [i])

/-- `(α, β)`: the elements at positive times and at nonpositive times, in order. -/
def posSplit (p : List ι) : List ι × List ι := posSplitRev x p.reverse

@[simp] theorem posSplit_nil : posSplit x ([] : List ι) = ([], []) := rfl

theorem posSplit_append_singleton (q : List ι) (i : ι) :
    posSplit x (q ++ [i]) =
      if 0 < (q.map x).sum + x i then ((posSplit x q).1 ++ [i], (posSplit x q).2)
      else ((posSplit x q).1, (posSplit x q).2 ++ [i]) := by
  simp only [posSplit, List.reverse_append, List.reverse_singleton, List.singleton_append,
    posSplitRev, List.map_reverse, List.sum_reverse]

theorem posSplit_perm (p : List ι) : (posSplit x p).1 ++ (posSplit x p).2 ~ p := by
  induction p using List.reverseRecOn with
  | nil => simp
  | append_singleton q i ih =>
    rw [posSplit_append_singleton]
    split_ifs with h
    · simp only
      calc (posSplit x q).1 ++ [i] ++ (posSplit x q).2
          ~ (posSplit x q).1 ++ ((posSplit x q).2 ++ [i]) := by
            rw [List.append_assoc]
            exact (List.perm_append_comm.append_left _)
        _ = ((posSplit x q).1 ++ (posSplit x q).2) ++ [i] := by simp
        _ ~ q ++ [i] := ih.append_right _
    · simp only
      rw [← List.append_assoc]
      exact ih.append_right _

theorem posSplit_sum (p : List ι) :
    ((posSplit x p).1.map x).sum + ((posSplit x p).2.map x).sum = (p.map x).sum := by
  have := ((posSplit_perm x p).map x).sum_eq
  rw [← List.sum_append, ← List.map_append]
  exact this

theorem posSplit_allPos_allNonpos (p : List ι) :
    AllPos x (posSplit x p).1 ∧ AllNonpos x (posSplit x p).2 := by
  induction p using List.reverseRecOn with
  | nil => exact ⟨fun j hj1 hj2 => by simp at hj2; omega, fun j => by simp⟩
  | append_singleton q i ih =>
    obtain ⟨hα, hβ⟩ := ih
    have hαs := psum_le_sum_of_allPos x hα
    have hβs := sum_nonpos_of_allNonpos x hβ
    have hsum := posSplit_sum x q
    rw [posSplit_append_singleton]
    split_ifs with h
    · refine ⟨(allPos_append_singleton x _ _).mpr ⟨hα, ?_⟩, hβ⟩
      linarith
    · refine ⟨hα, (allNonpos_append_singleton x _ _).mpr ⟨hβ, ?_⟩⟩
      push Not at h
      linarith

theorem posSplit_length (p : List ι) : (posSplit x p).1.length = posCount x p := by
  induction p using List.reverseRecOn with
  | nil => simp [posCount]
  | append_singleton q i ih =>
    rw [posSplit_append_singleton, posCount_append_singleton]
    split_ifs with h <;> simp [ih]

/-- **Uniqueness**: a list is determined by its split and its multiset. -/
theorem posSplit_eq_of_perm {p p' : List ι} (hperm : p ~ p')
    (hsplit : posSplit x p = posSplit x p') : p = p' := by
  induction p using List.reverseRecOn generalizing p' with
  | nil => exact (List.perm_nil.mp hperm.symm).symm ▸ rfl
  | append_singleton q i ih =>
    rcases p'.eq_nil_or_concat with rfl | ⟨q', i', rfl⟩
    · exact absurd (List.perm_nil.mp hperm) (by simp)
    rw [List.concat_eq_append] at hperm hsplit ⊢
    have hsum : (q.map x).sum + x i = (q'.map x).sum + x i' := by
      have := (hperm.map x).sum_eq
      simpa using this
    rw [posSplit_append_singleton, posSplit_append_singleton, ← hsum] at hsplit
    split_ifs at hsplit with h
    · simp only [Prod.mk.injEq] at hsplit
      obtain ⟨h1, h2⟩ := hsplit
      obtain ⟨hα, hi⟩ := List.append_inj' h1 (by simp)
      simp only [List.cons.injEq, and_true] at hi
      subst hi
      have hq : q ~ q' := (List.perm_append_right_iff _).mp hperm
      rw [ih hq (Prod.ext hα h2)]
    · simp only [Prod.mk.injEq] at hsplit
      obtain ⟨h1, h2⟩ := hsplit
      obtain ⟨hβ, hi⟩ := List.append_inj' h2 (by simp)
      simp only [List.cons.injEq, and_true] at hi
      subst hi
      have hq : q ~ q' := (List.perm_append_right_iff _).mp hperm
      rw [ih hq (Prod.ext h1 hβ)]

/-- **Existence**: every admissible pair `(α, β)` is the split of some interleaving. -/
theorem exists_posSplit_eq :
    ∀ (n : ℕ) (α β : List ι), α.length + β.length = n → AllPos x α → AllNonpos x β →
      ∃ p : List ι, p ~ α ++ β ∧ posSplit x p = (α, β) := by
  intro n
  induction n with
  | zero =>
    intro α β hn _ _
    have hα : α = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hβ : β = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hα; subst hβ
    exact ⟨[], by simp, by simp⟩
  | succ n ih =>
    intro α β hn hα hβ
    by_cases ht : 0 < (α.map x).sum + (β.map x).sum
    · -- `α` is nonempty
      rcases α.eq_nil_or_concat with rfl | ⟨α', a, rfl⟩
      · have := sum_nonpos_of_allNonpos x hβ
        simp at ht
        linarith
      rw [List.concat_eq_append] at hn hα ⊢
      obtain ⟨hα', _⟩ := (allPos_append_singleton x _ _).mp hα
      obtain ⟨p', hp'perm, hp'split⟩ := ih α' β (by simp at hn; omega) hα' hβ
      refine ⟨p' ++ [a], ?_, ?_⟩
      · calc p' ++ [a] ~ (α' ++ β) ++ [a] := hp'perm.append_right _
          _ ~ α' ++ ([a] ++ β) := by
              rw [List.append_assoc]
              exact (List.perm_append_comm.append_left _)
          _ = α' ++ [a] ++ β := by simp
      · rw [posSplit_append_singleton, hp'split]
        have hs : (p'.map x).sum = (α'.map x).sum + (β.map x).sum := by
          have := (hp'perm.map x).sum_eq
          simpa using this
        have : 0 < (p'.map x).sum + x a := by
          rw [hs]; simp at ht; linarith
        rw [if_pos this]
    · -- `β` is nonempty (or both empty, excluded by `n + 1 > 0`)
      rcases β.eq_nil_or_concat with rfl | ⟨β', b, rfl⟩
      · rcases α.eq_nil_or_concat with rfl | ⟨α', a, rfl⟩
        · simp at hn
        · rw [List.concat_eq_append] at hα ht
          obtain ⟨_, hpos⟩ := (allPos_append_singleton x _ _).mp hα
          simp at ht
          linarith
      rw [List.concat_eq_append] at hn hβ ⊢
      obtain ⟨hβ', _⟩ := (allNonpos_append_singleton x _ _).mp hβ
      obtain ⟨p', hp'perm, hp'split⟩ := ih α β' (by simp at hn; omega) hα hβ'
      refine ⟨p' ++ [b], ?_, ?_⟩
      · calc p' ++ [b] ~ (α ++ β') ++ [b] := hp'perm.append_right _
          _ = α ++ (β' ++ [b]) := by simp
      · rw [posSplit_append_singleton, hp'split]
        have hs : (p'.map x).sum = (α.map x).sum + (β'.map x).sum := by
          have := (hp'perm.map x).sum_eq
          simpa using this
        have : ¬ 0 < (p'.map x).sum + x b := by
          rw [hs]; simp at ht; linarith
        rw [if_neg this]

/-! ### Reversal and prefix/suffix characterisations of the first argmax -/

theorem isFirstArgmax_reverse_iff (α : List ι) :
    IsFirstArgmax x α.reverse α.length ↔ AllPos x α := by
  have hlen : α.reverse.length = α.length := List.length_reverse
  have htot : psum x α.reverse α.length = (α.map x).sum := by
    rw [← hlen, psum_length, List.map_reverse, List.sum_reverse]
  constructor
  · rintro ⟨_, h1, _⟩ j hj1 hj2
    have := h1 (α.length - j) (by omega)
    rw [htot, psum_reverse x α _] at this
    have hjj : α.length - (α.length - j) = j := by omega
    rw [hjj] at this
    linarith
  · intro h
    refine ⟨hlen.ge, fun i hi => ?_, fun i => ?_⟩
    · rw [htot, psum_reverse x α _]
      have := h (α.length - i) (by omega) (by omega)
      linarith
    · rw [htot]
      rcases Nat.lt_or_ge i α.length with hi | hi
      · rw [psum_reverse x α _]
        have := h (α.length - i) (by omega) (by omega)
        linarith
      · rw [psum_of_length_le x (by rw [hlen]; exact hi), List.map_reverse, List.sum_reverse]

theorem isFirstArgmax_append_iff (α β : List ι) :
    IsFirstArgmax x (α ++ β) α.length ↔ IsFirstArgmax x α α.length ∧ AllNonpos x β := by
  have hm : psum x (α ++ β) α.length = (α.map x).sum := by
    rw [psum_append_of_le x le_rfl, psum_length]
  constructor
  · rintro ⟨_, h1, h2⟩
    refine ⟨⟨le_rfl, fun i hi => ?_, fun i => ?_⟩, fun j => ?_⟩
    · have := h1 i hi
      rwa [psum_append_of_le x hi.le, psum_append_of_le x le_rfl] at this
    · rcases Nat.lt_or_ge i α.length with hi | hi
      · have := h1 i hi
        rw [psum_append_of_le x hi.le, psum_append_of_le x le_rfl] at this
        exact this.le
      · rw [psum_of_length_le x hi, psum_length]
    · have := h2 (α.length + j)
      rw [psum_append_add, hm] at this
      linarith
  · rintro ⟨⟨_, h1, _⟩, h3⟩
    refine ⟨by simp, fun i hi => ?_, fun i => ?_⟩
    · rw [psum_append_of_le x hi.le, psum_append_of_le x le_rfl]
      exact h1 i hi
    · rw [hm]
      rcases Nat.lt_or_ge i α.length with hi | hi
      · rw [psum_append_of_le x hi.le]
        have := h1 i hi
        rw [psum_length] at this
        exact this.le
      · rw [psum_append_of_length_le x hi]
        have := h3 (i - α.length)
        linarith

theorem isFirstArgmax_iff_split (r : List ι) (k : ℕ) :
    IsFirstArgmax x r k ↔
      k ≤ r.length ∧ IsFirstArgmax x (r.take k) k ∧ AllNonpos x (r.drop k) := by
  constructor
  · intro h
    have hk : k ≤ r.length := h.1
    have hlen : (r.take k).length = k := List.length_take_of_le hk
    have := isFirstArgmax_append_iff x (r.take k) (r.drop k)
    rw [hlen, List.take_append_drop] at this
    exact ⟨hk, this.mp h⟩
  · rintro ⟨hk, h⟩
    have hlen : (r.take k).length = k := List.length_take_of_le hk
    have := isFirstArgmax_append_iff x (r.take k) (r.drop k)
    rw [hlen, List.take_append_drop] at this
    exact this.mpr h

/-! ### The counting theorem -/

variable {P : Finset (List ι)} {l : List ι}

/-- Step 1: `#{N = k} = #{r : take k r all positive, drop k r all nonpositive}`. -/
theorem card_posCount_eq_card_split (hP : ∀ p, p ∈ P ↔ p ~ l) (k : ℕ) :
    (P.filter fun p => posCount x p = k).card =
      (P.filter fun r => k ≤ r.length ∧ AllPos x (r.take k) ∧ AllNonpos x (r.drop k)).card := by
  refine Finset.card_nbij (fun p => (posSplit x p).1 ++ (posSplit x p).2) ?_ ?_ ?_
  · intro p hp
    dsimp only
    rw [Finset.mem_coe, Finset.mem_filter] at hp ⊢
    obtain ⟨hpP, hpk⟩ := hp
    have hlen : (posSplit x p).1.length = k := by rw [posSplit_length, hpk]
    obtain ⟨hα, hβ⟩ := posSplit_allPos_allNonpos x p
    refine ⟨(hP _).mpr ((posSplit_perm x p).trans ((hP _).mp hpP)), ?_, ?_, ?_⟩
    · simp; omega
    · rw [List.take_left' hlen]; exact hα
    · rw [List.drop_left' hlen]; exact hβ
  · intro p hp p' hp' heq
    rw [Finset.mem_coe, Finset.mem_filter] at hp hp'
    have hlen : (posSplit x p).1.length = (posSplit x p').1.length := by
      rw [posSplit_length, posSplit_length, hp.2, hp'.2]
    obtain ⟨h1, h2⟩ := List.append_inj heq hlen
    exact posSplit_eq_of_perm x (((hP _).mp hp.1).trans ((hP _).mp hp'.1).symm) (Prod.ext h1 h2)
  · intro r hr
    rw [Finset.mem_coe, Finset.mem_filter] at hr
    obtain ⟨hrP, hk, hα, hβ⟩ := hr
    obtain ⟨p, hpperm, hpsplit⟩ := exists_posSplit_eq x _ (r.take k) (r.drop k) rfl hα hβ
    rw [List.take_append_drop] at hpperm
    refine ⟨p, ?_, ?_⟩
    · rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨(hP _).mpr (hpperm.trans ((hP _).mp hrP)), ?_⟩
      rw [← posSplit_length, hpsplit]
      exact List.length_take_of_le hk
    · show (posSplit x p).1 ++ (posSplit x p).2 = r
      rw [hpsplit]
      exact List.take_append_drop k r

/-- Step 2: reversing the prefix. -/
theorem card_split_eq_card_argmax_split (hP : ∀ p, p ∈ P ↔ p ~ l) (k : ℕ) :
    (P.filter fun r => k ≤ r.length ∧ AllPos x (r.take k) ∧ AllNonpos x (r.drop k)).card =
      (P.filter fun r => k ≤ r.length ∧ IsFirstArgmax x (r.take k) k ∧
        AllNonpos x (r.drop k)).card := by
  refine Finset.card_nbij (fun r => (r.take k).reverse ++ r.drop k) ?_ ?_ ?_
  · intro r hr
    dsimp only
    rw [Finset.mem_coe, Finset.mem_filter] at hr ⊢
    obtain ⟨hrP, hk, hα, hβ⟩ := hr
    have hlen : (r.take k).reverse.length = k := by
      rw [List.length_reverse]; exact List.length_take_of_le hk
    have hperm : (r.take k).reverse ++ r.drop k ~ r := by
      calc (r.take k).reverse ++ r.drop k ~ r.take k ++ r.drop k :=
            (List.reverse_perm _).append_right _
        _ = r := List.take_append_drop k r
    refine ⟨(hP _).mpr (hperm.trans ((hP _).mp hrP)), ?_, ?_, ?_⟩
    · simp; omega
    · rw [List.take_left' hlen]
      have := (isFirstArgmax_reverse_iff x (r.take k)).mpr hα
      rwa [List.length_take_of_le hk] at this
    · rw [List.drop_left' hlen]; exact hβ
  · intro r hr r' hr' heq
    rw [Finset.mem_coe, Finset.mem_filter] at hr hr'
    have hlen : (r.take k).reverse.length = (r'.take k).reverse.length := by
      rw [List.length_reverse, List.length_reverse, List.length_take_of_le hr.2.1,
        List.length_take_of_le hr'.2.1]
    obtain ⟨h1, h2⟩ := List.append_inj heq hlen
    have h1' : r.take k = r'.take k := List.reverse_injective h1
    rw [← List.take_append_drop k r, ← List.take_append_drop k r', h1', h2]
  · intro r' hr'
    rw [Finset.mem_coe, Finset.mem_filter] at hr'
    obtain ⟨hrP, hk, hT, hβ⟩ := hr'
    refine ⟨(r'.take k).reverse ++ r'.drop k, ?_, ?_⟩
    · rw [Finset.mem_coe, Finset.mem_filter]
      have hlen : (r'.take k).reverse.length = k := by
        rw [List.length_reverse]; exact List.length_take_of_le hk
      have hperm : (r'.take k).reverse ++ r'.drop k ~ r' := by
        calc (r'.take k).reverse ++ r'.drop k ~ r'.take k ++ r'.drop k :=
              (List.reverse_perm _).append_right _
          _ = r' := List.take_append_drop k r'
      refine ⟨(hP _).mpr (hperm.trans ((hP _).mp hrP)), ?_, ?_, ?_⟩
      · simp; omega
      · rw [List.take_left' hlen, ← isFirstArgmax_reverse_iff, List.reverse_reverse, hlen]
        exact hT
      · rw [List.drop_left' hlen]; exact hβ
    · have hlen : (r'.take k).reverse.length = k := by
        rw [List.length_reverse]; exact List.length_take_of_le hk
      dsimp only
      rw [List.take_left' hlen, List.drop_left' hlen, List.reverse_reverse, List.take_append_drop]

/-- **Combinatorial Sparre Andersen**: `#{p ∈ P : N(p) = k} = #{p ∈ P : T(p) = k}`. -/
theorem card_posCount_eq_card_isFirstArgmax (hP : ∀ p, p ∈ P ↔ p ~ l) (k : ℕ) :
    (P.filter fun p => posCount x p = k).card =
      (P.filter fun p => IsFirstArgmax x p k).card := by
  rw [card_posCount_eq_card_split x hP k, card_split_eq_card_argmax_split x hP k]
  congr 1
  apply Finset.filter_congr
  intro r _
  exact (isFirstArgmax_iff_split x r k).symm

end Fluctuation
end SwingRepair
