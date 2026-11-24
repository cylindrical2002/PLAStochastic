import PLAStochastic.Index.Algorithm.SegmentLength
import Mathlib.Data.Nat.Count

/-!
# ALG-OPT on a finite key list and on an infinite key sequence

`finSegLen eps p K a` is the length of the ALG-OPT segment that starts at index
`a` when the algorithm runs on the finite key list `p 0, …, p (K-1)`: the
longest feasible prefix of the remaining keys, i.e. the scan accepts keys while
the prefix stays feasible and cuts before the first failure (or at the end of
the list).  `finCut` iterates it and `finSegCount` counts the segments.

`cut eps p j : ℕ∞` is the start of the `j`-th segment when ALG-OPT runs on the
infinite sequence `p`; it becomes `⊤` after an infinite segment.  The exact
bridge between the two runs is `finCut_eq_min`: the finite cuts are the
infinite cuts truncated at `K`.  No probabilistic hypothesis is used.
-/

namespace PGM

noncomputable section

open Classical

/-- The key sequence seen from index `a` on. -/
def shiftSeq (p : ℕ → ℝ) (a : ℕ) : ℕ → ℝ := fun i => p (a + i)

@[simp] theorem shiftSeq_apply (p : ℕ → ℝ) (a i : ℕ) : shiftSeq p a i = p (a + i) := rfl

theorem prefixAffineFeasible_one {eps : ℝ} (heps : 0 ≤ eps) (p : ℕ → ℝ) :
    prefixAffineFeasible eps p 1 :=
  ⟨0, 0, fun i hi => by
    have : i = 0 := by omega
    subst this; simpa using heps⟩

theorem one_le_segLen {eps : ℝ} (heps : 0 ≤ eps) (p : ℕ → ℝ) : 1 ≤ segLen eps p := by
  have h := (lt_segLen_iff (eps := eps) (p := p) 0).2 (prefixAffineFeasible_one heps p)
  exact (ENat.add_one_le_iff (ENat.natCast_ne_top 0)).2 h |>.trans_eq' (by simp)

/-! ## The finite run -/

/-- ALG-OPT on the finite list `p 0, …, p (K-1)`: the number of keys in the
    segment starting at `a`, namely the longest feasible prefix of the remaining
    `K - a` keys. -/
def finSegLen (eps : ℝ) (p : ℕ → ℝ) (K a : ℕ) : ℕ :=
  Nat.findGreatest (fun len => prefixAffineFeasible eps (shiftSeq p a) len) (K - a)

/-- Segment starts of the finite run; once the list is exhausted they stay at `K`. -/
def finCut (eps : ℝ) (p : ℕ → ℝ) (K : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => finCut eps p K j + finSegLen eps p K (finCut eps p K j)

/-- Number of segments produced by ALG-OPT on `p 0, …, p (K-1)`. -/
def finSegCount (eps : ℝ) (p : ℕ → ℝ) (K : ℕ) : ℕ :=
  Nat.count (fun j => finCut eps p K j < K) (K + 1)

/-- The finite segment length is the infinite one truncated by the list end. -/
theorem finSegLen_eq_min (eps : ℝ) (p : ℕ → ℝ) (K a : ℕ) :
    (finSegLen eps p K a : ℕ∞) = min (segLen eps (shiftSeq p a)) ((K - a : ℕ) : ℕ∞) := by
  set P : ℕ → Prop := fun len => prefixAffineFeasible eps (shiftSeq p a) len with hP
  have hP0 : P 0 := prefixAffineFeasible_zero eps _
  have hPle : ∀ m : ℕ, (m : ℕ∞) ≤ segLen eps (shiftSeq p a) → P m := by
    intro m hm
    cases m with
    | zero => exact hP0
    | succ k =>
      apply (lt_segLen_iff k).1
      exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self k) hm
  unfold finSegLen
  by_cases hs : ((K - a : ℕ) : ℕ∞) ≤ segLen eps (shiftSeq p a)
  · rw [min_eq_right hs]
    rw [Nat.findGreatest_eq (hPle _ hs)]
  · have hs' : segLen eps (shiftSeq p a) < ((K - a : ℕ) : ℕ∞) := not_le.mp hs
    rw [min_eq_left hs'.le]
    obtain ⟨k, hk⟩ : ∃ k : ℕ, segLen eps (shiftSeq p a) = k :=
      ⟨(segLen eps (shiftSeq p a)).toNat, (ENat.natCast_toNat (ne_top_of_lt hs')).symm⟩
    rw [hk] at hs' ⊢
    have hkK : k ≤ K - a := by exact_mod_cast hs'.le
    congr 1
    apply (Nat.findGreatest_eq_iff).2
    refine ⟨hkK, fun _ => hPle k (le_of_eq hk.symm), fun n hkn hnK => ?_⟩
    intro hPn
    have hk1 : P (k + 1) := prefixAffineFeasible_mono hPn (by omega)
    have := (lt_segLen_iff (eps := eps) (p := shiftSeq p a) k).2 hk1
    rw [hk] at this
    exact lt_irrefl _ this

theorem finSegLen_le (eps : ℝ) (p : ℕ → ℝ) (K a : ℕ) : finSegLen eps p K a ≤ K - a :=
  Nat.findGreatest_le _

theorem one_le_finSegLen {eps : ℝ} (heps : 0 ≤ eps) (p : ℕ → ℝ) {K a : ℕ} (ha : a < K) :
    1 ≤ finSegLen eps p K a := by
  have h := finSegLen_eq_min eps p K a
  have h1 : (1 : ℕ∞) ≤ min (segLen eps (shiftSeq p a)) ((K - a : ℕ) : ℕ∞) :=
    le_min (one_le_segLen heps _) (by exact_mod_cast (by omega : 1 ≤ K - a))
  rw [← h] at h1
  exact_mod_cast h1

theorem finCut_le (eps : ℝ) (p : ℕ → ℝ) (K : ℕ) : ∀ j, finCut eps p K j ≤ K
  | 0 => Nat.zero_le K
  | j + 1 => by
    have := finSegLen_le eps p K (finCut eps p K j)
    have := finCut_le eps p K j
    simp only [finCut]
    omega

theorem finCut_mono (eps : ℝ) (p : ℕ → ℝ) (K : ℕ) : Monotone (finCut eps p K) :=
  monotone_nat_of_le_succ fun j => by simp only [finCut]; omega

theorem finCut_lt_succ {eps : ℝ} (heps : 0 ≤ eps) (p : ℕ → ℝ) {K j : ℕ}
    (hj : finCut eps p K j < K) : finCut eps p K j < finCut eps p K (j + 1) := by
  have := one_le_finSegLen heps p hj
  simp only [finCut]
  omega

theorem finCut_ge_min {eps : ℝ} (heps : 0 ≤ eps) (p : ℕ → ℝ) (K : ℕ) :
    ∀ j, min j K ≤ finCut eps p K j
  | 0 => by simp
  | j + 1 => by
    have ih := finCut_ge_min heps p K j
    by_cases hj : finCut eps p K j < K
    · have := finCut_lt_succ heps p hj
      omega
    · have hK : finCut eps p K j = K := le_antisymm (finCut_le eps p K j) (not_lt.mp hj)
      have h1 : finCut eps p K j ≤ finCut eps p K (j + 1) := finCut_mono eps p K (Nat.le_succ j)
      omega

theorem findGreatest_congr' {P Q : ℕ → Prop} [DecidablePred P] [DecidablePred Q] :
    ∀ {m : ℕ}, (∀ n ≤ m, (P n ↔ Q n)) → Nat.findGreatest P m = Nat.findGreatest Q m
  | 0, _ => by simp
  | m + 1, h => by
    rw [Nat.findGreatest_succ, Nat.findGreatest_succ,
      findGreatest_congr' (fun n hn => h n (Nat.le_succ_of_le hn))]
    by_cases hP : P (m + 1)
    · simp [hP, (h (m + 1) le_rfl).1 hP]
    · simp [hP, show ¬ Q (m + 1) from fun hq => hP ((h (m + 1) le_rfl).2 hq)]

/-- The finite run only reads the keys of the list. -/
theorem finSegLen_congr {eps : ℝ} {p p' : ℕ → ℝ} {K : ℕ} (hpp : ∀ i < K, p i = p' i)
    (a : ℕ) : finSegLen eps p K a = finSegLen eps p' K a := by
  unfold finSegLen
  apply findGreatest_congr'
  intro len hlen
  exact prefixAffineFeasible_congr (fun i hi => by
    simp only [shiftSeq_apply]; exact hpp _ (by omega))

theorem finCut_congr {eps : ℝ} {p p' : ℕ → ℝ} {K : ℕ} (hpp : ∀ i < K, p i = p' i) :
    ∀ j, finCut eps p K j = finCut eps p' K j
  | 0 => rfl
  | j + 1 => by
    simp only [finCut, finCut_congr hpp j, finSegLen_congr hpp]

theorem finSegCount_congr {eps : ℝ} {p p' : ℕ → ℝ} {K : ℕ} (hpp : ∀ i < K, p i = p' i) :
    finSegCount eps p K = finSegCount eps p' K := by
  unfold finSegCount
  simp only [finCut_congr hpp]

/-! ## The infinite run -/

/-- Segment starts of ALG-OPT on an infinite key sequence (`⊤` after an
    infinite segment). -/
def cut (eps : ℝ) (p : ℕ → ℝ) : ℕ → ℕ∞
  | 0 => 0
  | j + 1 => cut eps p j + segLen eps (shiftSeq p (cut eps p j).toNat)

/-- The finite cuts are the infinite cuts truncated at the list end. -/
theorem finCut_eq_min (eps : ℝ) (p : ℕ → ℝ) (K : ℕ) :
    ∀ j, (finCut eps p K j : ℕ∞) = min (cut eps p j) K
  | 0 => by simp [finCut, cut]
  | j + 1 => by
    have ih := finCut_eq_min eps p K j
    set f := finCut eps p K j with hf
    by_cases hfK : f < K
    · have hcj : cut eps p j = f := by
        rcases le_total (cut eps p j) K with hle | hle
        · rw [min_eq_left hle] at ih; exact ih.symm
        · rw [min_eq_right hle] at ih
          exact absurd (by exact_mod_cast ih : f = K) (by omega)
      have hstep : finCut eps p K (j + 1) = f + finSegLen eps p K f := rfl
      have hcut : cut eps p (j + 1) = (f : ℕ∞) + segLen eps (shiftSeq p f) := by
        simp only [cut, hcj, ENat.toNat_natCast]
      rw [hstep, hcut, Nat.cast_add, finSegLen_eq_min]
      have hKf : ((K - f : ℕ) : ℕ∞) = (K : ℕ∞) - f := ENat.natCast_sub K f
      rw [hKf]
      have hfK' : (f : ℕ∞) ≤ K := by exact_mod_cast hfK.le
      rcases le_total (segLen eps (shiftSeq p f)) ((K : ℕ∞) - f) with hle | hle
      · rw [min_eq_left hle, min_eq_left]
        calc (f : ℕ∞) + segLen eps (shiftSeq p f) ≤ f + ((K : ℕ∞) - f) := add_le_add_right hle _
          _ = K := add_tsub_cancel_of_le hfK'
      · rw [min_eq_right hle, add_tsub_cancel_of_le hfK', min_eq_right]
        calc (K : ℕ∞) = f + ((K : ℕ∞) - f) := (add_tsub_cancel_of_le hfK').symm
          _ ≤ f + segLen eps (shiftSeq p f) := add_le_add_right hle _
    · have hfK' : f = K := le_antisymm (finCut_le eps p K j) (not_lt.mp hfK)
      have hcj : (K : ℕ∞) ≤ cut eps p j := by
        rcases le_total (cut eps p j) K with hle | hle
        · rw [min_eq_left hle] at ih
          rw [← ih, hfK']
        · exact hle
      have hfin : finCut eps p K (j + 1) = K := by
        simp only [finCut, ← hf, hfK']
        have := finSegLen_le eps p K K
        omega
      rw [hfin, min_eq_right]
      exact hcj.trans le_self_add

end

end PGM
