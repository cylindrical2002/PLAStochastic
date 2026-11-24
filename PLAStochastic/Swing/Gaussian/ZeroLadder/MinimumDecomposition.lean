import PLAStochastic.Swing.Gaussian.ZeroLadder.StrictLadderLaw

/-! # Finite-path minimum decomposition for symmetric ladder moments

The minimum of a path with distinct positions is unique. Before this minimum,
reverse and negate the increments; after it, retain the forward increments.
Both pieces then have strictly positive noninitial partial sums. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def ladderReverseIndex (k j : ℕ) : ℕ := if j < k then k-1-j else j

theorem ladderReverseIndex_involutive (k : ℕ) : Function.Involutive (ladderReverseIndex k) := by
  intro j
  unfold ladderReverseIndex
  by_cases hj : j < k
  · simp only [if_pos hj, if_pos (show k-1-j < k by omega)]
    omega
  · simp only [if_neg hj]

def ladderReverseNeg (X : ℕ → Ω → ℝ) (k : ℕ) (j : ℕ) (ω : Ω) : ℝ :=
  -X (ladderReverseIndex k j) ω

def ladderPositivePrefix (X : ℕ → Ω → ℝ) (n : ℕ) : Set Ω :=
  {ω | ∀ j : ℕ, 0 < j → j ≤ n → 0 < cumulativeSamples X j ω}

def ladderMinimumAt (S : ℕ → ℝ) (n k : ℕ) : Prop :=
  k ≤ n ∧ ∀ j : ℕ, j ≤ n → j ≠ k → S k < S j

theorem ladderMinimumAt_unique {S : ℕ → ℝ} {n k l : ℕ}
    (hk : ladderMinimumAt S n k) (hl : ladderMinimumAt S n l) : k = l := by
  by_contra hn
  exact (lt_asymm (hk.2 l hl.1 (fun h => hn h.symm)) (hl.2 k hk.1 hn)).elim

theorem exists_ladderMinimumAt (S : ℕ → ℝ) (n : ℕ)
    (hd : ∀ i ≤ n, ∀ j ≤ n, i ≠ j → S i ≠ S j) : ∃ k, ladderMinimumAt S n k := by
  obtain ⟨k, hk, hm⟩ := (Finset.range (n+1)).exists_min_image S (by simp)
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  refine ⟨k, hkn, ?_⟩
  intro j hj hjk
  exact lt_of_le_of_ne (hm j (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj)))
    (hd k hkn j hj hjk.symm)

theorem ladderMinimumAt_partition {A : Type*} [AddCommMonoid A]
    (S : ℕ → ℝ) (n : ℕ) (F : ℕ → A)
    {k : ℕ} (hk : ladderMinimumAt S n k) :
    (∑ j ∈ Finset.range (n+1), if ladderMinimumAt S n j then F j else 0) = F k := by
  rw [Finset.sum_eq_single k]
  · exact if_pos hk
  · intro j _ hjk
    exact if_neg (fun hj => hjk (ladderMinimumAt_unique hj hk))
  · intro h
    exact (h (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk.1))).elim

theorem cumulativeSamples_ladderReverseNeg (X : ℕ → Ω → ℝ) (k j : ℕ) (hj : j ≤ k)
    (ω : Ω) :
    cumulativeSamples (ladderReverseNeg X k) j ω =
      cumulativeSamples X (k-j) ω - cumulativeSamples X k ω := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hjk : j < k := by omega
    rw [cumulativeSamples_succ, ih (by omega)]
    have hind : k-j = (k-(j+1))+1 := by omega
    rw [hind, cumulativeSamples_succ]
    simp only [ladderReverseNeg, ladderReverseIndex, if_pos hjk]
    rw [show k-1-j = k-(j+1) by omega]
    ring

/-- The exact split at the unique minimum, in terms of the actual input
increments. -/
theorem ladderMinimumAt_iff_positive_pieces (X : ℕ → Ω → ℝ) (n k : ℕ) (hk : k ≤ n)
    (ω : Ω) :
    ladderMinimumAt (fun j => cumulativeSamples X j ω) n k ↔
      ω ∈ ladderPositivePrefix (ladderReverseNeg X k) k ∧
      ω ∈ ladderPositivePrefix (fun j => X (k+j)) (n-k) := by
  constructor
  · intro hm
    constructor
    · intro j hj hjk
      rw [cumulativeSamples_ladderReverseNeg X k j hjk ω]
      exact sub_pos.mpr (hm.2 (k-j) (by omega) (by omega))
    · intro j hj hjn
      have hh := hm.2 (k+j) (by omega) (by omega)
      dsimp only at hh
      rw [cumulativeSamples_add_shift] at hh
      linarith
  · rintro ⟨hleft, hright⟩
    refine ⟨hk, ?_⟩
    intro j hj hjk
    by_cases hjlt : j < k
    · have hh := hleft (k-j) (by omega) (by omega)
      rw [cumulativeSamples_ladderReverseNeg X k (k-j) (by omega) ω,
        show k-(k-j) = j by omega] at hh
      linarith
    · have hh := hright (j-k) (by omega) (by omega)
      have he := cumulativeSamples_add_shift X k (j-k) ω
      rw [show k+(j-k) = j by omega] at he
      linarith

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- Every pair of distinct positions in the actual zero-drift Gaussian walk is
distinct on one common probability-one event. -/
theorem cumulativeSamples_distinct_ae (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    ∀ᵐ ω ∂μ, Function.Injective (fun n => cumulativeSamples X n ω) := by
  have hall : ∀ᵐ ω ∂μ, ∀ k : ℕ, ∀ j : ℕ, 0 < j →
      cumulativeSamples (fun i => X (k+i)) j ω ≠ 0 := by
    apply ae_all_iff.mpr
    intro k
    have hc := gaussianDriftWalk_nonzero_ae (fun i => hX (k+i))
      (hi.precomp (g := fun i => k+i) (by intro i j he; dsimp at he; omega)) (fun i => hG (k+i)) 0 0
    simpa only [gaussianDriftWalk, zero_add, zero_mul, add_zero] using hc
  filter_upwards [hall] with ω hω
  intro i j he
  dsimp only at he
  wlog hij : i < j generalizing i j
  · by_cases hji : j < i
    · exact (this (i := j) (j := i) he.symm hji).symm
    · omega
  have hn := hω i (j-i) (by omega)
  have hh := cumulativeSamples_add_shift X i (j-i) ω
  rw [show i+(j-i) = j by omega, ← he] at hh
  exact (hn (by linarith)).elim

/-- Reversing a finite prefix and reflecting the increments preserves the
genuine iid Gaussian assumptions. -/
theorem ladderReverseNeg_gaussian (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (k : ℕ) :
    (∀ j, Measurable (ladderReverseNeg X k j)) ∧ iIndepFun (ladderReverseNeg X k) μ ∧
      ∀ j, μ.map (ladderReverseNeg X k j) = gaussianReal 0 1 := by
  refine ⟨fun j => (hX _).neg, ?_, ?_⟩
  · exact (hi.precomp (ladderReverseIndex_involutive k).injective).comp
      (fun _ x => -x) (fun _ => measurable_neg)
  · intro j
    exact gaussianIncrement_reflected_law hX hG (ladderReverseIndex k j)

end SwingRepair
