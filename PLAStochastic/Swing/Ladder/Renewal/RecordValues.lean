import PLAStochastic.Swing.Ladder.Renewal.OvershootIdentity

/-! # The ladder levels are the record values of the actual walk

The ladder epochs of the increment sequence are defined by iterating the
restart map.  The drift walk shifted at a restart is the original walk measured
from the current ladder level, so the `n`-th ladder level is the walk evaluated
at the `n`-th ladder epoch.  This is the step that identifies the abstract
renewal sequence with the actual positive-drift Gaussian walk.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical MeasureTheory
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- The number of increments consumed by the first ladder step. -/
def ladderSequenceStep (a : ℝ) (w : ℕ → ℝ) : ℕ :=
  (gaussianAscendingLadderIndex (fun n (v : ℕ → ℝ) => v n) a w).untopD 0 + 1

theorem ladderSequenceRestart_eq_shift (a : ℝ) (w : ℕ → ℝ) (j : ℕ) :
    ladderSequenceRestart a w j = w (ladderSequenceStep a w + j) := by
  rw [ladderSequenceRestart, ladderSequenceStep]

/-- The drift walk after a restart is the original walk measured from the
current level. -/
theorem gaussianDriftWalk_restart (a : ℝ) (w : ℕ → ℝ) (m : ℕ) :
    gaussianDriftWalk (fun n (v : ℕ → ℝ) => v n) 0 a m (ladderSequenceRestart a w) =
      gaussianDriftWalk (fun n (v : ℕ → ℝ) => v n) 0 a (ladderSequenceStep a w + m) w -
        gaussianDriftWalk (fun n (v : ℕ → ℝ) => v n) 0 a (ladderSequenceStep a w) w := by
  have hcum : cumulativeSamples (fun n (v : ℕ → ℝ) => v n) m (ladderSequenceRestart a w) =
      cumulativeSamples (fun j => (fun n (v : ℕ → ℝ) => v n) (ladderSequenceStep a w + j)) m w := by
    unfold cumulativeSamples
    refine Finset.sum_congr rfl fun j _ => ?_
    exact ladderSequenceRestart_eq_shift a w j
  have hshift := cumulativeSamples_add_shift (fun n (v : ℕ → ℝ) => v n)
    (ladderSequenceStep a w) m w
  simp only [gaussianDriftWalk, hcum, hshift]
  push_cast
  ring

/-- The `n`-th ladder epoch of an increment sequence. -/
def ladderSequenceEpoch (a : ℝ) : ℕ → (ℕ → ℝ) → ℕ
  | 0, _ => 0
  | (n+1), w => ladderSequenceStep a w + ladderSequenceEpoch a n (ladderSequenceRestart a w)

@[simp] theorem ladderSequenceEpoch_zero (a : ℝ) (w : ℕ → ℝ) :
    ladderSequenceEpoch a 0 w = 0 := rfl

theorem ladderSequenceEpoch_succ (a : ℝ) (n : ℕ) (w : ℕ → ℝ) :
    ladderSequenceEpoch a (n+1) w =
      ladderSequenceStep a w + ladderSequenceEpoch a n (ladderSequenceRestart a w) := rfl

/-- The `n`-th ladder level of an increment sequence. -/
def ladderSequenceSum (a : ℝ) (n : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, ladderSequenceHeight a ((ladderSequenceRestart a)^[k] w)

@[simp] theorem ladderSequenceSum_zero (a : ℝ) (w : ℕ → ℝ) :
    ladderSequenceSum a 0 w = 0 := by simp [ladderSequenceSum]

theorem ladderSequenceSum_nonneg (a : ℝ) (n : ℕ) (w : ℕ → ℝ) :
    0 ≤ ladderSequenceSum a n w := by
  unfold ladderSequenceSum
  exact Finset.sum_nonneg fun k _ =>
    gaussianAscendingLadderHeight_nonneg (X := fun j (v : ℕ → ℝ) => v j) a _

theorem ladderSequenceSum_succ_left (a : ℝ) (n : ℕ) (w : ℕ → ℝ) :
    ladderSequenceSum a (n+1) w =
      ladderSequenceHeight a w + ladderSequenceSum a n (ladderSequenceRestart a w) := by
  unfold ladderSequenceSum
  rw [Finset.sum_range_succ']
  simp only [Function.iterate_zero, id_eq]
  rw [add_comm]
  congr 1

omit mΩ in
theorem gaussianLadderSum_eq_sequence (X : ℕ → Ω → ℝ) (a : ℝ) (n : ℕ) (ω : Ω) :
    gaussianLadderSum X a n ω = ladderSequenceSum a n (fun k => X k ω) := rfl

/-- On a sequence whose first ladder time is finite, the walk at the first
ladder step is the first ladder height. -/
theorem gaussianDriftWalk_step_eq_height (a : ℝ) {w : ℕ → ℝ}
    (hfin : gaussianAscendingLadderTime (fun n (v : ℕ → ℝ) => v n) a w ≠ ⊤) :
    gaussianDriftWalk (fun n (v : ℕ → ℝ) => v n) 0 a (ladderSequenceStep a w) w =
      ladderSequenceHeight a w := by
  have hnat := gaussianAscendingLadderTimeNat_eq_index_succ
    (fun n (v : ℕ → ℝ) => v n) a hfin
  have hpos := gaussianAscendingLadderHeight_eq_position (X := fun n (v : ℕ → ℝ) => v n)
    (a := a) (ω := w) hfin
  rw [ladderSequenceStep, ← hnat]
  exact (hpos.symm).trans rfl

/-! ### Almost sure finiteness along the whole iteration -/

theorem ladderSequence_iterate_finite_ae [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) :
    ∀ᵐ ω ∂μ, ∀ n : ℕ,
      gaussianAscendingLadderTime (fun k (v : ℕ → ℝ) => v k) a
        ((ladderSequenceRestart a)^[n] (fun k => X k ω)) ≠ ⊤ := by
  rw [ae_all_iff]
  intro n
  have hmeas : MeasurableSet {w : ℕ → ℝ |
      gaussianAscendingLadderTime (fun k (v : ℕ → ℝ) => v k) a w ≠ ⊤} :=
    (measurableSet_eq_fun
      (gaussianAscendingLadderTime_measurable (fun k => measurable_pi_apply k) a)
      measurable_const).compl
  have hstate := regenerativeState_identDistrib (ladderSequenceRestart_measurable a)
    (measurable_pi_lambda _ hX) (ladderSequenceRestart_identDistrib hX hi hG ha) n
  exact hstate.symm.ae_snd hmeas (gaussianAscendingLadderTime_finite_ae hX hi hG ha)

/-! ### The ladder level is the walk at the ladder epoch -/

theorem ladderSequence_walk_epoch_eq (a : ℝ) :
    ∀ (n : ℕ) (w : ℕ → ℝ),
      (∀ k : ℕ, gaussianAscendingLadderTime (fun j (v : ℕ → ℝ) => v j) a
        ((ladderSequenceRestart a)^[k] w) ≠ ⊤) →
      gaussianDriftWalk (fun j (v : ℕ → ℝ) => v j) 0 a (ladderSequenceEpoch a n w) w =
        ladderSequenceSum a n w := by
  intro n
  induction n with
  | zero =>
    intro w _
    simp [gaussianDriftWalk]
  | succ n ih =>
    intro w hfin
    have hrest : ∀ k : ℕ, gaussianAscendingLadderTime (fun j (v : ℕ → ℝ) => v j) a
        ((ladderSequenceRestart a)^[k] (ladderSequenceRestart a w)) ≠ ⊤ := by
      intro k
      have := hfin (k+1)
      rwa [Function.iterate_succ_apply] at this
    have hfin0 : gaussianAscendingLadderTime (fun j (v : ℕ → ℝ) => v j) a w ≠ ⊤ := hfin 0
    have hih := ih (ladderSequenceRestart a w) hrest
    have hshift := gaussianDriftWalk_restart a w
      (ladderSequenceEpoch a n (ladderSequenceRestart a w))
    have hstep := gaussianDriftWalk_step_eq_height a hfin0
    rw [ladderSequenceEpoch_succ, ladderSequenceSum_succ_left]
    linarith

/-! ### The walk stays below the current ladder level -/

theorem gaussianDriftWalk_nonpos_before_step (a : ℝ) {v : ℕ → ℝ}
    (hfin : gaussianAscendingLadderTime (fun j (u : ℕ → ℝ) => u j) a v ≠ ⊤)
    {j : ℕ} (hj : j < ladderSequenceStep a v) :
    gaussianDriftWalk (fun j (u : ℕ → ℝ) => u j) 0 a j v ≤ 0 := by
  have hnat := gaussianAscendingLadderTimeNat_eq_index_succ
    (fun j (u : ℕ → ℝ) => u j) a hfin
  have hjt : (j : WithTop ℕ) <
      gaussianAscendingLadderTime (fun j (u : ℕ → ℝ) => u j) a v := by
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hfin
    have hknat : gaussianAscendingLadderTimeNat (fun j (u : ℕ → ℝ) => u j) a v = k := by
      rw [gaussianAscendingLadderTimeNat, ← hk, WithTop.untopD_coe]
    rw [← hk]
    refine WithTop.coe_lt_coe.mpr ?_
    rw [ladderSequenceStep, ← hnat, hknat] at hj
    exact hj
  rw [gaussianAscendingLadderTime_eq_hittingAfter] at hjt
  have hnot := notMem_of_lt_hittingAfter hjt (Nat.zero_le j)
  simpa using hnot

theorem ladderSequence_walk_le_level (a : ℝ) :
    ∀ (n : ℕ) (w : ℕ → ℝ),
      (∀ k : ℕ, gaussianAscendingLadderTime (fun j (v : ℕ → ℝ) => v j) a
        ((ladderSequenceRestart a)^[k] w) ≠ ⊤) →
      ∀ m : ℕ, m < ladderSequenceEpoch a (n+1) w →
        gaussianDriftWalk (fun j (v : ℕ → ℝ) => v j) 0 a m w ≤ ladderSequenceSum a n w := by
  intro n
  induction n with
  | zero =>
    intro w hfin m hm
    rw [ladderSequenceEpoch_succ, ladderSequenceEpoch_zero, Nat.add_zero] at hm
    rw [ladderSequenceSum_zero]
    have hfin0 : gaussianAscendingLadderTime (fun j (v : ℕ → ℝ) => v j) a w ≠ ⊤ := hfin 0
    exact gaussianDriftWalk_nonpos_before_step a hfin0 hm
  | succ n ih =>
    intro w hfin m hm
    have hrest : ∀ k : ℕ, gaussianAscendingLadderTime (fun j (v : ℕ → ℝ) => v j) a
        ((ladderSequenceRestart a)^[k] (ladderSequenceRestart a w)) ≠ ⊤ := by
      intro k
      have := hfin (k+1)
      rwa [Function.iterate_succ_apply] at this
    have hfin0 : gaussianAscendingLadderTime (fun j (v : ℕ → ℝ) => v j) a w ≠ ⊤ := hfin 0
    rcases lt_or_ge m (ladderSequenceStep a w) with hlt | hge
    · have hle := gaussianDriftWalk_nonpos_before_step a hfin0 hlt
      have hnn : 0 ≤ ladderSequenceSum a (n+1) w := ladderSequenceSum_nonneg a (n+1) w
      linarith
    · obtain ⟨j, rfl⟩ : ∃ j, m = ladderSequenceStep a w + j := ⟨m - ladderSequenceStep a w, by omega⟩
      have hjlt : j < ladderSequenceEpoch a (n+1) (ladderSequenceRestart a w) := by
        rw [ladderSequenceEpoch_succ] at hm
        omega
      have hih := ih (ladderSequenceRestart a w) hrest j hjlt
      have hshift := gaussianDriftWalk_restart a w j
      have hstep := gaussianDriftWalk_step_eq_height a hfin0
      rw [ladderSequenceSum_succ_left]
      linarith

/-! ### First passage of the actual walk -/

/-- The first time the actual drift walk exceeds a level. -/
def gaussianWalkPassage (X : ℕ → Ω → ℝ) (a b : ℝ) (ω : Ω) : ℕ :=
  if h : ∃ m : ℕ, b < gaussianDriftWalk X 0 a m ω then Nat.find h else 0

/-- The overshoot of the actual drift walk above a level. -/
def gaussianWalkOvershoot (X : ℕ → Ω → ℝ) (a b : ℝ) (ω : Ω) : ℝ :=
  gaussianDriftWalk X 0 a (gaussianWalkPassage X a b ω) ω - b

omit mΩ in
theorem gaussianDriftWalk_eq_sequence (X : ℕ → Ω → ℝ) (a : ℝ) (m : ℕ) (ω : Ω) :
    gaussianDriftWalk X 0 a m ω =
      gaussianDriftWalk (fun j (v : ℕ → ℝ) => v j) 0 a m (fun k => X k ω) := rfl

omit mΩ in
/-- The walk's first passage above a nonnegative level happens exactly at a
ladder epoch, so its overshoot is the ladder overshoot. -/
theorem gaussianWalkOvershoot_eq_ladder (X : ℕ → Ω → ℝ) (a : ℝ) {b : ℝ} (hb : 0 ≤ b) {ω : Ω}
    (hfin : ∀ k : ℕ, gaussianAscendingLadderTime (fun j (v : ℕ → ℝ) => v j) a
      ((ladderSequenceRestart a)^[k] (fun k => X k ω)) ≠ ⊤)
    (hex : ∃ n : ℕ, b < gaussianLadderSum X a n ω) :
    gaussianWalkOvershoot X a b ω = gaussianLadderOvershoot X a b ω := by
  set w : ℕ → ℝ := fun k => X k ω with hwdef
  have hpass : gaussianLadderPassage X a b ω = Nat.find hex := by
    rw [gaussianLadderPassage, dif_pos hex]
  have hgt : b < gaussianLadderSum X a (Nat.find hex) ω := Nat.find_spec hex
  have hmin : ∀ j < Nat.find hex, gaussianLadderSum X a j ω ≤ b :=
    fun j hj => le_of_not_gt (Nat.find_min hex hj)
  have hpos : 0 < Nat.find hex := by
    by_contra hcon
    have h0 : Nat.find hex = 0 := by omega
    rw [h0, gaussianLadderSum_zero] at hgt
    linarith
  obtain ⟨p, hp⟩ : ∃ p, Nat.find hex = p+1 := ⟨Nat.find hex - 1, by omega⟩
  set E : ℕ := ladderSequenceEpoch a (p+1) w with hEdef
  have hwalkE : gaussianDriftWalk X 0 a E ω = gaussianLadderSum X a (p+1) ω := by
    rw [gaussianDriftWalk_eq_sequence, hEdef,
      ladderSequence_walk_epoch_eq a (p+1) w hfin, gaussianLadderSum_eq_sequence]
  have hEgt : b < gaussianDriftWalk X 0 a E ω := by
    rw [hwalkE, ← hp]
    exact hgt
  have hexw : ∃ m : ℕ, b < gaussianDriftWalk X 0 a m ω := ⟨E, hEgt⟩
  have hQ : gaussianWalkPassage X a b ω = Nat.find hexw := by
    rw [gaussianWalkPassage, dif_pos hexw]
  have hQle : Nat.find hexw ≤ E := Nat.find_le hEgt
  have hQge : E ≤ Nat.find hexw := by
    by_contra hcon
    have hlt : Nat.find hexw < E := by omega
    have hbound := ladderSequence_walk_le_level a p w hfin (Nat.find hexw) hlt
    have hspec : b < gaussianDriftWalk X 0 a (Nat.find hexw) ω := Nat.find_spec hexw
    rw [gaussianDriftWalk_eq_sequence] at hspec
    have hple : gaussianLadderSum X a p ω ≤ b := hmin p (by omega)
    rw [gaussianLadderSum_eq_sequence] at hple
    linarith
  have hQeq : Nat.find hexw = E := le_antisymm hQle hQge
  rw [gaussianWalkOvershoot, hQ, hQeq, hwalkE, gaussianLadderOvershoot, hpass, hp]

variable [IsProbabilityMeasure μ]

theorem gaussianWalkOvershoot_ae_eq_ladder
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {M a : ℝ} (ha : 0 < a) (haM : a ≤ M)
    {b : ℝ} (hb : 0 ≤ b) :
    ∀ᵐ ω ∂μ, gaussianWalkOvershoot X a b ω = gaussianLadderOvershoot X a b ω := by
  filter_upwards [ladderSequence_iterate_finite_ae hX hi hG ha,
    gaussianLadderSum_exists_gt_ae hX hi hG ha haM] with ω hfin hex
  exact gaussianWalkOvershoot_eq_ladder X a hb hfin (hex b)

/-- `eq:overshootrenewalidentity` for the actual positive-drift Gaussian walk. -/
theorem gaussianWalkOvershoot_tail_eq
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {M a : ℝ} (ha : 0 < a) (haM : a ≤ M)
    {b t : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) :
    μ {ω | t < gaussianWalkOvershoot X a b ω} =
      renewalOvershootTail (gaussianAscendingLadderLaw X μ a) b t := by
  have hcong : {ω | t < gaussianWalkOvershoot X a b ω} =ᵐ[μ]
      {ω | t < gaussianLadderOvershoot X a b ω} := by
    filter_upwards [gaussianWalkOvershoot_ae_eq_ladder hX hi hG ha haM hb] with ω hω
    refine propext ?_
    show t < gaussianWalkOvershoot X a b ω ↔ t < gaussianLadderOvershoot X a b ω
    rw [hω]
  rw [measure_congr hcong]
  exact gaussianLadderOvershoot_tail_eq hX hi hG ha haM hb ht

end SwingRepair
