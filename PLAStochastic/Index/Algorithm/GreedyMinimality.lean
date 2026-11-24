import PLAStochastic.Index.Algorithm.Segmentation
import Mathlib.Algebra.Order.Floor.Div

/-!
# Greedy minimality of ALG-OPT and monotonicity in the feasibility notion

A window `[a, b)` of the key list `p 0, …, p (K-1)` is `eps`-feasible when
`prefixAffineFeasible eps (shiftSeq p a) (b - a)` (`windowFeasible`).  Sub-windows
of feasible windows are feasible (`windowFeasible_sub`).

For a general window predicate `F`, `greedyCut F K` iterates "jump to the largest
right end `b ≤ K` with `F a b`" and `greedyCount F K` counts its windows; for
window feasibility these are `finCut` and `finSegCount` (`greedyCut_windowFeasible`,
`greedyCount_windowFeasible`).  The results:

* cut monotonicity: a weaker hereditary predicate never cuts earlier and needs at
  most as many windows (`greedyCut_le_greedyCut`, `greedyCount_le_greedyCount`),
  specialised to a larger tolerance (`finSegCount_anti_eps`) and to two key lists
  (`finSegCount_le_of_windowFeasible`);
* greedy minimality: every partition of `[0, K)` into admissible windows has at
  least `greedyCount F K` windows, and the greedy cuts attain it
  (`greedyCount_le_of_partition`, `greedyCount_isLeast`, `finSegCount_isLeast`);
* splitting: refining into windows of length at most `τ` costs at most `K / τ`
  extra windows (`exists_refinement`, `exists_short_windowPartition`);
* long segments: if all windows of length at most `τ` are feasible, every segment
  but the last has at least `τ` keys and there are at most `⌈K/τ⌉` segments
  (`le_finSegLen_of_short`, `finSegCount_le_ceilDiv_of_short`).
-/

namespace PGM

noncomputable section

open Classical Finset

/-! ## Feasible windows -/

/-- The window `[a, b)` of the key list is `eps`-feasible. -/
def windowFeasible (eps : ℝ) (p : ℕ → ℝ) (a b : ℕ) : Prop :=
  prefixAffineFeasible eps (shiftSeq p a) (b - a)

/-- A window predicate is hereditary when it passes to sub-windows. -/
def WindowHereditary (F : ℕ → ℕ → Prop) : Prop :=
  ∀ ⦃a b a' b' : ℕ⦄, F a b → a ≤ a' → a' ≤ b' → b' ≤ b → F a' b'

/-- Sub-windows of feasible windows are feasible. -/
theorem windowFeasible_sub {eps : ℝ} {p : ℕ → ℝ} {a b a' b' : ℕ}
    (h : windowFeasible eps p a b) (ha : a ≤ a') (hab : a' ≤ b') (hb : b' ≤ b) :
    windowFeasible eps p a' b' := by
  have hw := prefixAffineFeasible_window (r := a' - a) (w := b' - a') h (by omega)
  have hfun : (fun i => shiftSeq p a (a' - a + i)) = shiftSeq p a' := by
    funext i
    simp only [shiftSeq_apply]
    congr 1
    omega
  unfold windowFeasible
  rwa [hfun] at hw

/-- Sub-windows of feasible windows are feasible (spelled out). -/
theorem prefixAffineFeasible_shiftSeq_sub {eps : ℝ} {p : ℕ → ℝ} {a b a' b' : ℕ}
    (h : prefixAffineFeasible eps (shiftSeq p a) (b - a)) (ha : a ≤ a') (hab : a' ≤ b')
    (hb : b' ≤ b) : prefixAffineFeasible eps (shiftSeq p a') (b' - a') :=
  windowFeasible_sub h ha hab hb

theorem windowFeasible_hereditary (eps : ℝ) (p : ℕ → ℝ) :
    WindowHereditary (windowFeasible eps p) :=
  fun _ _ _ _ h ha hab hb => windowFeasible_sub h ha hab hb

/-! ## The greedy run for a general window predicate -/

/-- Length of the greedy window starting at `a`: the largest `len ≤ K - a` with
    `F a (a + len)` (zero if there is none). -/
def greedyLen (F : ℕ → ℕ → Prop) (K a : ℕ) : ℕ :=
  Nat.findGreatest (fun len => F a (a + len)) (K - a)

/-- Cuts of the greedy run: each step jumps to the largest admissible right end `≤ K`. -/
def greedyCut (F : ℕ → ℕ → Prop) (K : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => greedyCut F K j + greedyLen F K (greedyCut F K j)

/-- Number of windows of the greedy run on `[0, K)`. -/
def greedyCount (F : ℕ → ℕ → Prop) (K : ℕ) : ℕ :=
  Nat.count (fun j => greedyCut F K j < K) (K + 1)

theorem greedyCut_zero (F : ℕ → ℕ → Prop) (K : ℕ) : greedyCut F K 0 = 0 := rfl

theorem greedyCut_succ (F : ℕ → ℕ → Prop) (K j : ℕ) :
    greedyCut F K (j + 1) = greedyCut F K j + greedyLen F K (greedyCut F K j) := rfl

theorem greedyLen_le (F : ℕ → ℕ → Prop) (K a : ℕ) : greedyLen F K a ≤ K - a :=
  Nat.findGreatest_le _

theorem le_greedyLen {F : ℕ → ℕ → Prop} {K a b : ℕ} (hab : a ≤ b) (hbK : b ≤ K)
    (h : F a b) : b - a ≤ greedyLen F K a :=
  Nat.le_findGreatest (by omega) (by rwa [Nat.add_sub_cancel' hab])

theorem greedyCut_le (F : ℕ → ℕ → Prop) (K : ℕ) : ∀ j, greedyCut F K j ≤ K
  | 0 => Nat.zero_le K
  | j + 1 => by
    have := greedyLen_le F K (greedyCut F K j)
    have := greedyCut_le F K j
    rw [greedyCut_succ]
    omega

theorem greedyCut_mono (F : ℕ → ℕ → Prop) (K : ℕ) : Monotone (greedyCut F K) :=
  monotone_nat_of_le_succ fun j => by rw [greedyCut_succ]; omega

/-- The greedy step reaches every admissible right end. -/
theorem le_greedyCut_succ {F : ℕ → ℕ → Prop} {K j b : ℕ} (hab : greedyCut F K j ≤ b)
    (hbK : b ≤ K) (h : F (greedyCut F K j) b) : b ≤ greedyCut F K (j + 1) := by
  have := le_greedyLen hab hbK h
  rw [greedyCut_succ]
  omega

/-- A nonempty greedy window satisfies the predicate. -/
theorem greedyCut_feasible {F : ℕ → ℕ → Prop} {K j : ℕ}
    (hne : greedyCut F K j < greedyCut F K (j + 1)) :
    F (greedyCut F K j) (greedyCut F K (j + 1)) := by
  rw [greedyCut_succ] at hne ⊢
  exact Nat.findGreatest_of_ne_zero (P := fun len => F (greedyCut F K j) (greedyCut F K j + len))
    rfl (by omega)

/-- With one-key windows admissible, the greedy run advances while keys remain. -/
theorem greedyCut_lt_succ {F : ℕ → ℕ → Prop} {K : ℕ} (hbase : ∀ a < K, F a (a + 1))
    {j : ℕ} (hj : greedyCut F K j < K) : greedyCut F K j < greedyCut F K (j + 1) :=
  lt_of_lt_of_le (Nat.lt_succ_self _)
    (le_greedyCut_succ (Nat.le_succ _) hj (hbase _ hj))

theorem greedyCut_ge_min {F : ℕ → ℕ → Prop} {K : ℕ} (hbase : ∀ a < K, F a (a + 1)) :
    ∀ j, min j K ≤ greedyCut F K j
  | 0 => by simp [greedyCut_zero]
  | j + 1 => by
    have ih := greedyCut_ge_min hbase j
    have hle := greedyCut_le F K j
    have hmono := greedyCut_mono F K (Nat.le_add_right j 1)
    by_cases hj : greedyCut F K j < K
    · have := greedyCut_lt_succ hbase hj
      omega
    · omega

/-! ## Cut monotonicity in the window predicate -/

/-- **Cut monotonicity.**  A weaker hereditary predicate never cuts earlier. -/
theorem greedyCut_le_greedyCut {F₁ F₂ : ℕ → ℕ → Prop} {K : ℕ} (h₂ : WindowHereditary F₂)
    (h12 : ∀ a b, a < b → b ≤ K → F₁ a b → F₂ a b) :
    ∀ j, greedyCut F₁ K j ≤ greedyCut F₂ K j
  | 0 => le_rfl
  | j + 1 => by
    have ih := greedyCut_le_greedyCut h₂ h12 j
    set a₁ := greedyCut F₁ K j with ha₁
    set a₂ := greedyCut F₂ K j with ha₂
    set b₁ := greedyCut F₁ K (j + 1) with hb₁
    have hmono₁ : a₁ ≤ b₁ := greedyCut_mono F₁ K (Nat.le_add_right j 1)
    have hmono₂ : a₂ ≤ greedyCut F₂ K (j + 1) := greedyCut_mono F₂ K (Nat.le_add_right j 1)
    by_cases hb : b₁ ≤ a₂
    · exact hb.trans hmono₂
    · have hlt : a₂ < b₁ := not_le.mp hb
      have hK : b₁ ≤ K := greedyCut_le F₁ K (j + 1)
      have hF₁ : F₁ a₁ b₁ := greedyCut_feasible (by omega)
      have hF₂ : F₂ a₁ b₁ := h12 a₁ b₁ (by omega) hK hF₁
      exact le_greedyCut_succ hlt.le hK (h₂ hF₂ ih hlt.le le_rfl)

/-- A weaker hereditary predicate needs at most as many windows. -/
theorem greedyCount_le_greedyCount {F₁ F₂ : ℕ → ℕ → Prop} {K : ℕ} (h₂ : WindowHereditary F₂)
    (h12 : ∀ a b, a < b → b ≤ K → F₁ a b → F₂ a b) :
    greedyCount F₂ K ≤ greedyCount F₁ K :=
  Nat.count_mono_left fun j _ hj => lt_of_le_of_lt (greedyCut_le_greedyCut h₂ h12 j) hj

/-! ## ALG-OPT is the greedy run of window feasibility -/

theorem greedyLen_windowFeasible (eps : ℝ) (p : ℕ → ℝ) (K a : ℕ) :
    greedyLen (windowFeasible eps p) K a = finSegLen eps p K a := by
  unfold greedyLen finSegLen windowFeasible
  apply findGreatest_congr'
  intro n _
  rw [Nat.add_sub_cancel_left]

theorem greedyCut_windowFeasible (eps : ℝ) (p : ℕ → ℝ) (K : ℕ) :
    greedyCut (windowFeasible eps p) K = finCut eps p K := by
  funext j
  induction j with
  | zero => rfl
  | succ j ih => rw [greedyCut_succ, ih, greedyLen_windowFeasible]; rfl

theorem greedyCount_windowFeasible (eps : ℝ) (p : ℕ → ℝ) (K : ℕ) :
    greedyCount (windowFeasible eps p) K = finSegCount eps p K := by
  unfold greedyCount finSegCount
  rw [greedyCut_windowFeasible]

theorem prefixAffineFeasible_mono_eps {eps eps' : ℝ} (h : eps ≤ eps') {p : ℕ → ℝ} {len : ℕ}
    (hf : prefixAffineFeasible eps p len) : prefixAffineFeasible eps' p len := by
  rcases hf with ⟨a, b, hab⟩
  exact ⟨a, b, fun i hi => (hab i hi).trans h⟩

/-- **Comparison of two key lists.**  If every `eps`-feasible window of `p` is
    `eps'`-feasible for `p'`, the ALG-OPT run on `p'` never cuts earlier. -/
theorem finCut_le_finCut_of_windowFeasible {eps eps' : ℝ} {p p' : ℕ → ℝ} {K : ℕ}
    (h : ∀ a b, a < b → b ≤ K → windowFeasible eps p a b → windowFeasible eps' p' a b)
    (j : ℕ) : finCut eps p K j ≤ finCut eps' p' K j := by
  rw [← greedyCut_windowFeasible, ← greedyCut_windowFeasible]
  exact greedyCut_le_greedyCut (windowFeasible_hereditary eps' p') h j

/-- **Comparison of two key lists.**  If every `eps`-feasible window of `p` is
    `eps'`-feasible for `p'`, ALG-OPT uses at most as many segments on `p'`. -/
theorem finSegCount_le_of_windowFeasible {eps eps' : ℝ} {p p' : ℕ → ℝ} {K : ℕ}
    (h : ∀ a b, a < b → b ≤ K → windowFeasible eps p a b → windowFeasible eps' p' a b) :
    finSegCount eps' p' K ≤ finSegCount eps p K := by
  rw [← greedyCount_windowFeasible, ← greedyCount_windowFeasible]
  exact greedyCount_le_greedyCount (windowFeasible_hereditary eps' p') h

theorem finCut_mono_eps {eps eps' : ℝ} (h : eps ≤ eps') (p : ℕ → ℝ) (K j : ℕ) :
    finCut eps p K j ≤ finCut eps' p K j :=
  finCut_le_finCut_of_windowFeasible (fun _ _ _ _ hf => prefixAffineFeasible_mono_eps h hf) j

/-- A larger tolerance never needs more segments. -/
theorem finSegCount_anti_eps {eps eps' : ℝ} (h : eps ≤ eps') (p : ℕ → ℝ) (K : ℕ) :
    finSegCount eps' p K ≤ finSegCount eps p K :=
  finSegCount_le_of_windowFeasible fun _ _ _ _ hf => prefixAffineFeasible_mono_eps h hf

/-! ## Greedy minimality -/

/-- `c 0 = 0 < c 1 < ⋯ < c m = K`: a partition of `[0, K)` into `m` windows,
    each satisfying `F`. -/
structure WindowPartition (F : ℕ → ℕ → Prop) (K m : ℕ) (c : ℕ → ℕ) : Prop where
  start : c 0 = 0
  finish : c m = K
  lt_succ : ∀ i < m, c i < c (i + 1)
  window : ∀ i < m, F (c i) (c (i + 1))

theorem WindowPartition.le_finish {F : ℕ → ℕ → Prop} {K m : ℕ} {c : ℕ → ℕ}
    (hc : WindowPartition F K m c) {i : ℕ} (hi : i ≤ m) : c i ≤ K := by
  have key : ∀ k i, i + k = m → c i ≤ K := by
    intro k
    induction k with
    | zero => intro i hi; rw [← hc.finish, ← hi]; rfl
    | succ k ih =>
      intro i hi
      have h1 := hc.lt_succ i (by omega)
      have h2 := ih (i + 1) (by omega)
      omega
  exact key (m - i) i (by omega)

/-- The greedy cuts dominate the cuts of every feasible partition. -/
theorem le_greedyCut_of_partition {F : ℕ → ℕ → Prop} {K m : ℕ} {c : ℕ → ℕ}
    (hF : WindowHereditary F) (hc : WindowPartition F K m c) :
    ∀ j ≤ m, c j ≤ greedyCut F K j
  | 0, _ => by rw [hc.start]; exact Nat.zero_le _
  | j + 1, hj => by
    have ih := le_greedyCut_of_partition hF hc j (by omega)
    have hmono := greedyCut_mono F K (Nat.le_add_right j 1)
    by_cases hlt : greedyCut F K j < c (j + 1)
    · exact le_greedyCut_succ hlt.le (hc.le_finish hj)
        (hF (hc.window j (by omega)) ih hlt.le le_rfl)
    · omega

/-- **Greedy minimality.**  Every partition of `[0, K)` into windows satisfying a
    hereditary predicate has at least `greedyCount F K` windows. -/
theorem greedyCount_le_of_partition {F : ℕ → ℕ → Prop} {K m : ℕ} {c : ℕ → ℕ}
    (hF : WindowHereditary F) (hc : WindowPartition F K m c) : greedyCount F K ≤ m := by
  have hm : K ≤ greedyCut F K m := hc.finish ▸ le_greedyCut_of_partition hF hc m le_rfl
  unfold greedyCount
  rw [Nat.count_eq_card_filter_range]
  calc #{j ∈ range (K + 1) | greedyCut F K j < K} ≤ #(range m) := by
        apply Finset.card_le_card
        intro j hj
        rw [Finset.mem_filter] at hj
        rw [Finset.mem_range]
        by_contra hjm
        have := greedyCut_mono F K (not_lt.mp hjm)
        omega
    _ = m := Finset.card_range _

/-- With one-key windows admissible, the `j`-th greedy cut lies before the list end
    exactly for the first `greedyCount F K` indices. -/
theorem greedyCut_lt_iff {F : ℕ → ℕ → Prop} {K : ℕ} (hbase : ∀ a < K, F a (a + 1)) (j : ℕ) :
    greedyCut F K j < K ↔ j < greedyCount F K := by
  unfold greedyCount
  rw [Nat.count_eq_card_filter_range]
  constructor
  · intro hj
    have hjK : j < K := by
      have := greedyCut_ge_min hbase j
      omega
    calc j < #(range (j + 1)) := by rw [Finset.card_range]; omega
      _ ≤ #{i ∈ range (K + 1) | greedyCut F K i < K} := by
        apply Finset.card_le_card
        intro i hi
        rw [Finset.mem_range] at hi
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, lt_of_le_of_lt (greedyCut_mono F K (by omega : i ≤ j)) hj⟩
  · intro hj
    by_contra hnot
    have : #{i ∈ range (K + 1) | greedyCut F K i < K} ≤ #(range j) := by
      apply Finset.card_le_card
      intro i hi
      rw [Finset.mem_filter] at hi
      rw [Finset.mem_range]
      by_contra hij
      have := greedyCut_mono F K (not_lt.mp hij)
      omega
    rw [Finset.card_range] at this
    omega

theorem greedyCut_greedyCount {F : ℕ → ℕ → Prop} {K : ℕ} (hbase : ∀ a < K, F a (a + 1)) :
    greedyCut F K (greedyCount F K) = K := by
  have h := (greedyCut_lt_iff hbase (greedyCount F K)).not.mpr (lt_irrefl _)
  have := greedyCut_le F K (greedyCount F K)
  omega

/-- The greedy cuts form a partition with `greedyCount F K` windows. -/
theorem greedyCut_windowPartition {F : ℕ → ℕ → Prop} {K : ℕ} (hbase : ∀ a < K, F a (a + 1)) :
    WindowPartition F K (greedyCount F K) (greedyCut F K) where
  start := rfl
  finish := greedyCut_greedyCount hbase
  lt_succ i hi := greedyCut_lt_succ hbase ((greedyCut_lt_iff hbase i).2 hi)
  window i hi := greedyCut_feasible (greedyCut_lt_succ hbase ((greedyCut_lt_iff hbase i).2 hi))

/-- **Greedy optimality.**  For a hereditary predicate admitting one-key windows,
    the greedy run uses the least possible number of windows. -/
theorem greedyCount_isLeast {F : ℕ → ℕ → Prop} {K : ℕ} (hF : WindowHereditary F)
    (hbase : ∀ a < K, F a (a + 1)) :
    IsLeast {m | ∃ c, WindowPartition F K m c} (greedyCount F K) :=
  ⟨⟨greedyCut F K, greedyCut_windowPartition hbase⟩,
    fun _ ⟨_, hc⟩ => greedyCount_le_of_partition hF hc⟩

theorem windowFeasible_succ {eps : ℝ} (heps : 0 ≤ eps) (p : ℕ → ℝ) (a : ℕ) :
    windowFeasible eps p a (a + 1) := by
  unfold windowFeasible
  rw [Nat.add_sub_cancel_left]
  exact prefixAffineFeasible_one heps _

/-- **ALG-OPT minimality.**  Every partition of the key list into `eps`-feasible
    windows has at least `finSegCount eps p K` windows. -/
theorem finSegCount_le_of_partition {eps : ℝ} {p : ℕ → ℝ} {K m : ℕ} {c : ℕ → ℕ}
    (hc : WindowPartition (windowFeasible eps p) K m c) : finSegCount eps p K ≤ m := by
  rw [← greedyCount_windowFeasible]
  exact greedyCount_le_of_partition (windowFeasible_hereditary eps p) hc

/-- The ALG-OPT cuts partition the key list into `finSegCount eps p K` feasible windows. -/
theorem finCut_windowPartition {eps : ℝ} (heps : 0 ≤ eps) (p : ℕ → ℝ) (K : ℕ) :
    WindowPartition (windowFeasible eps p) K (finSegCount eps p K) (finCut eps p K) := by
  rw [← greedyCount_windowFeasible, ← greedyCut_windowFeasible]
  exact greedyCut_windowPartition fun a _ => windowFeasible_succ heps p a

/-- **ALG-OPT optimality.**  `finSegCount eps p K` is the least number of
    `eps`-feasible windows partitioning the key list. -/
theorem finSegCount_isLeast {eps : ℝ} (heps : 0 ≤ eps) (p : ℕ → ℝ) (K : ℕ) :
    IsLeast {m | ∃ c, WindowPartition (windowFeasible eps p) K m c} (finSegCount eps p K) :=
  ⟨⟨finCut eps p K, finCut_windowPartition heps p K⟩,
    fun _ ⟨_, hc⟩ => finSegCount_le_of_partition hc⟩

/-! ## Splitting into short windows -/

/-- `⌈L/τ⌉` blocks of length `τ` cover `L`. -/
theorem le_ceilDiv_mul {τ : ℕ} (hτ : 0 < τ) (L : ℕ) : L ≤ (L + τ - 1) / τ * τ := by
  have := Nat.lt_div_mul_add (a := L + τ - 1) hτ
  omega

/-- Before the last of the `⌈L/τ⌉` blocks the length `L` is not yet covered. -/
theorem mul_lt_of_lt_ceilDiv {τ L k : ℕ} (hτ : 0 < τ) (hk : k < (L + τ - 1) / τ) :
    k * τ < L := by
  have h1 : (k + 1) * τ ≤ L + τ - 1 := (Nat.le_div_iff_mul_le hτ).1 hk
  have h2 : (k + 1) * τ = k * τ + τ := by ring
  omega

theorem ceilDiv_le_div_add_one {τ : ℕ} (hτ : 0 < τ) (L : ℕ) :
    (L + τ - 1) / τ ≤ L / τ + 1 := by
  calc (L + τ - 1) / τ ≤ (L + τ) / τ := Nat.div_le_div_right (by omega)
    _ = L / τ + 1 := Nat.add_div_right L hτ

/-- Splitting the windows of a partition into pieces of length at most `τ`. -/
theorem exists_refinement_aux {F : ℕ → ℕ → Prop} (hF : WindowHereditary F) {τ : ℕ}
    (hτ : 1 ≤ τ) {c : ℕ → ℕ} (h0 : c 0 = 0) :
    ∀ m, (∀ i < m, c i < c (i + 1) ∧ F (c i) (c (i + 1))) →
      ∃ m' c', WindowPartition (fun a b => F a b ∧ b - a ≤ τ) (c m) m' c' ∧
        m' ≤ m + c m / τ
  | 0, _ => ⟨0, c, ⟨h0, rfl, fun i hi => absurd hi (Nat.not_lt_zero i),
      fun i hi => absurd hi (Nat.not_lt_zero i)⟩, Nat.zero_le _⟩
  | m + 1, hm => by
    obtain ⟨m', c', hc', hm'⟩ := exists_refinement_aux hF hτ h0 m (fun i hi => hm i (by omega))
    obtain ⟨hAB, hFAB⟩ := hm m (by omega)
    set A := c m with hA
    set B := c (m + 1) with hB
    have hτ0 : 0 < τ := hτ
    set n := (B - A + τ - 1) / τ with hn
    set d : ℕ → ℕ := fun k => min (A + k * τ) B with hd
    have hd_lt : ∀ k < n, d k = A + k * τ := by
      intro k hk
      have := mul_lt_of_lt_ceilDiv hτ0 hk
      simp only [hd]
      omega
    have hd_le : ∀ k, A ≤ d k ∧ d k ≤ B := by
      intro k
      simp only [hd]
      omega
    have hd_succ : ∀ k, d (k + 1) ≤ A + k * τ + τ := by
      intro k
      have h2 : (k + 1) * τ = k * τ + τ := by ring
      simp only [hd]
      omega
    have hd_succ' : ∀ k < n, A + k * τ < d (k + 1) := by
      intro k hk
      have := mul_lt_of_lt_ceilDiv hτ0 hk
      have h2 : (k + 1) * τ = k * τ + τ := by ring
      simp only [hd]
      omega
    have hd_end : d n = B := by
      have : B - A ≤ n * τ := le_ceilDiv_mul hτ0 (B - A)
      simp only [hd]
      omega
    have hn1 : 1 ≤ n := by
      rw [hn, Nat.le_div_iff_mul_le hτ0]
      omega
    set c'' : ℕ → ℕ := fun i => if i ≤ m' then c' i else d (i - m') with hc''
    have hc''_lo : ∀ i ≤ m', c'' i = c' i := fun i hi => by simp only [hc'', if_pos hi]
    have hc''_hi : ∀ i, m' ≤ i → c'' i = d (i - m') := by
      intro i hi
      rcases Nat.eq_or_lt_of_le hi with h | h
      · subst h
        rw [hc''_lo _ le_rfl, hc'.finish, Nat.sub_self]
        have : d 0 = min A B := by simp only [hd, zero_mul, add_zero]
        rw [this]
        omega
      · simp only [hc'', if_neg (not_le.mpr h)]
    refine ⟨m' + n, c'', ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [hc''_lo 0 (Nat.zero_le _)]
      exact hc'.start
    · rw [hc''_hi _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left, hd_end]
    · intro i hi
      by_cases him : i < m'
      · rw [hc''_lo i him.le, hc''_lo (i + 1) him]
        exact hc'.lt_succ i him
      · have him' : m' ≤ i := not_lt.mp him
        rw [hc''_hi i him', hc''_hi (i + 1) (by omega),
          show i + 1 - m' = i - m' + 1 by omega, hd_lt _ (by omega)]
        exact hd_succ' _ (by omega)
    · intro i hi
      by_cases him : i < m'
      · rw [hc''_lo i him.le, hc''_lo (i + 1) him]
        exact hc'.window i him
      · have him' : m' ≤ i := not_lt.mp him
        rw [hc''_hi i him', hc''_hi (i + 1) (by omega),
          show i + 1 - m' = i - m' + 1 by omega]
        have hk : i - m' < n := by omega
        have e1 := hd_lt _ hk
        have e2 := hd_succ (i - m')
        have e3 := hd_succ' _ hk
        have l1 := hd_le (i - m')
        have l2 := hd_le (i - m' + 1)
        refine ⟨hF hFAB l1.1 (by omega) l2.2, by omega⟩
    · have h1 := ceilDiv_le_div_add_one hτ0 (B - A)
      have h2 := Nat.div_add_div_le_add_div (x := A) (y := B - A) (z := τ)
      rw [Nat.add_sub_cancel' hAB.le] at h2
      omega

/-- **Splitting.**  Refining a partition into windows of length at most `τ` costs at
    most `K / τ` extra windows. -/
theorem exists_refinement {F : ℕ → ℕ → Prop} (hF : WindowHereditary F) {τ K m : ℕ}
    (hτ : 1 ≤ τ) {c : ℕ → ℕ} (hc : WindowPartition F K m c) :
    ∃ m' c', WindowPartition (fun a b => F a b ∧ b - a ≤ τ) K m' c' ∧ m' ≤ m + K / τ := by
  have := exists_refinement_aux hF hτ hc.start m (fun i hi => ⟨hc.lt_succ i hi, hc.window i hi⟩)
  rwa [hc.finish] at this

/-- **Splitting the ALG-OPT segments.**  The key list has a partition into
    `eps`-feasible windows of length at most `τ` with at most
    `finSegCount eps p K + K / τ` windows. -/
theorem exists_short_windowPartition {eps : ℝ} (heps : 0 ≤ eps) (p : ℕ → ℝ) (K : ℕ)
    {τ : ℕ} (hτ : 1 ≤ τ) :
    ∃ m c, WindowPartition (fun a b => windowFeasible eps p a b ∧ b - a ≤ τ) K m c ∧
      m ≤ finSegCount eps p K + K / τ :=
  exists_refinement (windowFeasible_hereditary eps p) hτ (finCut_windowPartition heps p K)

/-! ## Long segments when short windows are feasible -/

section ShortWindows

variable {F : ℕ → ℕ → Prop} {K τ : ℕ}

theorem min_le_greedyLen (hτF : ∀ a b, a ≤ b → b ≤ K → b - a ≤ τ → F a b) (a : ℕ) :
    min τ (K - a) ≤ greedyLen F K a := by
  by_cases ha : a ≤ K
  · have := le_greedyLen (F := F) (K := K) (Nat.le_add_right a (min τ (K - a))) (by omega)
      (hτF _ _ (Nat.le_add_right _ _) (by omega) (by omega))
    rwa [Nat.add_sub_cancel_left] at this
  · omega

/-- Every greedy window except possibly the last has length at least `τ`. -/
theorem le_greedyLen_of_succ_lt (hτF : ∀ a b, a ≤ b → b ≤ K → b - a ≤ τ → F a b) {j : ℕ}
    (hj : greedyCut F K (j + 1) < K) : τ ≤ greedyLen F K (greedyCut F K j) := by
  have := min_le_greedyLen hτF (greedyCut F K j)
  rw [greedyCut_succ] at hj
  omega

theorem min_mul_le_greedyCut (hτF : ∀ a b, a ≤ b → b ≤ K → b - a ≤ τ → F a b) :
    ∀ j, min (τ * j) K ≤ greedyCut F K j
  | 0 => by simp [greedyCut_zero]
  | j + 1 => by
    have ih := min_mul_le_greedyCut hτF j
    have hle := greedyCut_le F K j
    have hs := min_le_greedyLen hτF (greedyCut F K j)
    have h2 : τ * (j + 1) = τ * j + τ := by ring
    rw [greedyCut_succ]
    omega

/-- **Count bound.**  If all windows of length at most `τ ≥ 1` are admissible, the
    greedy run uses at most `⌈K/τ⌉` windows. -/
theorem greedyCount_le_ceilDiv (hτ : 1 ≤ τ)
    (hτF : ∀ a b, a ≤ b → b ≤ K → b - a ≤ τ → F a b) : greedyCount F K ≤ K ⌈/⌉ τ := by
  unfold greedyCount
  rw [Nat.count_eq_card_filter_range]
  calc #{j ∈ range (K + 1) | greedyCut F K j < K} ≤ #(range (K ⌈/⌉ τ)) := by
        apply Finset.card_le_card
        intro j hj
        rw [Finset.mem_filter] at hj
        rw [Finset.mem_range, Nat.ceilDiv_eq_add_pred_div]
        have := min_mul_le_greedyCut hτF j
        have h1 : j + 1 ≤ (K + τ - 1) / τ := by
          rw [Nat.le_div_iff_mul_le (by omega)]
          have h2 : (j + 1) * τ = τ * j + τ := by ring
          omega
        omega
    _ = K ⌈/⌉ τ := Finset.card_range _

theorem greedyCount_le_div_add_one (hτ : 1 ≤ τ)
    (hτF : ∀ a b, a ≤ b → b ≤ K → b - a ≤ τ → F a b) : greedyCount F K ≤ K / τ + 1 := by
  have := greedyCount_le_ceilDiv hτ hτF
  rw [Nat.ceilDiv_eq_add_pred_div] at this
  exact this.trans (ceilDiv_le_div_add_one (by omega) K)

end ShortWindows

section ShortWindowsFin

variable {eps : ℝ} {p : ℕ → ℝ} {K τ : ℕ}

theorem windowFeasible_of_short
    (hτF : ∀ a len, a + len ≤ K → len ≤ τ → prefixAffineFeasible eps (shiftSeq p a) len) :
    ∀ a b, a ≤ b → b ≤ K → b - a ≤ τ → windowFeasible eps p a b :=
  fun a b hab hb hlen => hτF a (b - a) (by omega) hlen

/-- If every window of at most `τ` keys is `eps`-feasible, every ALG-OPT segment
    except possibly the last has at least `τ` keys. -/
theorem le_finSegLen_of_short
    (hτF : ∀ a len, a + len ≤ K → len ≤ τ → prefixAffineFeasible eps (shiftSeq p a) len)
    {j : ℕ} (hj : finCut eps p K (j + 1) < K) : τ ≤ finSegLen eps p K (finCut eps p K j) := by
  rw [← greedyCut_windowFeasible] at hj
  rw [← greedyLen_windowFeasible, ← greedyCut_windowFeasible]
  exact le_greedyLen_of_succ_lt (windowFeasible_of_short hτF) hj

/-- If every window of at most `τ ≥ 1` keys is `eps`-feasible, ALG-OPT uses at most
    `⌈K/τ⌉` segments. -/
theorem finSegCount_le_ceilDiv_of_short (hτ : 1 ≤ τ)
    (hτF : ∀ a len, a + len ≤ K → len ≤ τ → prefixAffineFeasible eps (shiftSeq p a) len) :
    finSegCount eps p K ≤ K ⌈/⌉ τ := by
  rw [← greedyCount_windowFeasible]
  exact greedyCount_le_ceilDiv hτ (windowFeasible_of_short hτF)

theorem finSegCount_le_div_add_one_of_short (hτ : 1 ≤ τ)
    (hτF : ∀ a len, a + len ≤ K → len ≤ τ → prefixAffineFeasible eps (shiftSeq p a) len) :
    finSegCount eps p K ≤ K / τ + 1 := by
  rw [← greedyCount_windowFeasible]
  exact greedyCount_le_div_add_one hτ (windowFeasible_of_short hτF)

end ShortWindowsFin

end

end PGM
