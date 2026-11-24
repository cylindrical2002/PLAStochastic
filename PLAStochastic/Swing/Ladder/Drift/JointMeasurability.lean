import PLAStochastic.Swing.Ladder.Renewal.EquilibriumOvershoot

/-! # The ascending ladder height as a jointly measurable function of the drift

The limiting Swing kernel of `eq:limitingmarginkernel` samples the drift `a`
first and then the equilibrium overshoot of the walk with that drift.  To read
the second stage as a probability kernel the ladder height must be measurable in
the pair `(a, ω)`, not only in `ω` at each fixed drift.  Nothing probabilistic
is used here: the ladder time is characterised by countably many joint
inequalities on the drifted walk.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-- Evaluating a measurable family at a measurable natural index stays measurable. -/
theorem measurable_at_nat_index {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {N : α → ℕ}
    (hN : Measurable N) {F : ℕ → α → β} (hF : ∀ n, Measurable (F n)) :
    Measurable (fun a => F (N a) a) := by
  intro s hs
  have heq : (fun a => F (N a) a) ⁻¹' s = ⋃ n, (N ⁻¹' {n}) ∩ (F n ⁻¹' s) := by
    ext a
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_singleton_iff]
    exact ⟨fun h => ⟨N a, rfl, h⟩, by rintro ⟨n, hn, h⟩; rwa [hn]⟩
  rw [heq]
  exact MeasurableSet.iUnion fun n => (hN (measurableSet_singleton n)).inter (hF n hs)

/-- The drifted walk is jointly measurable in the drift and the sample point. -/
theorem gaussianDriftWalk_joint_measurable (hX : ∀ n, Measurable (X n)) (n : ℕ) :
    Measurable (fun p : ℝ × Ω => gaussianDriftWalk X 0 p.1 n p.2) := by
  have hs : Measurable (cumulativeSamples X n) :=
    Finset.measurable_sum _ (fun k _ => hX k)
  have hsum : Measurable (fun p : ℝ × Ω => cumulativeSamples X n p.2 + p.1*(n : ℝ)) :=
    (hs.comp measurable_snd).add (measurable_fst.mul measurable_const)
  simpa only [gaussianDriftWalk, zero_add] using hsum

/-- A `WithTop ℕ` value bounded above by `m` and strictly above every smaller
index equals `m`. -/
theorem withTop_nat_eq_of_le_of_forall_lt {τ : WithTop ℕ} {m : ℕ}
    (hle : τ ≤ (m : WithTop ℕ)) (hlt : ∀ j : ℕ, j < m → (j : WithTop ℕ) < τ) :
    τ = (m : WithTop ℕ) := by
  refine le_antisymm hle ?_
  rcases eq_or_ne τ ⊤ with rfl | hne
  · exact le_top
  · obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hne
    rw [← hk] at hle hlt ⊢
    have hkm : k ≤ m := WithTop.coe_le_coe.mp hle
    rcases lt_or_eq_of_le hkm with hklt | rfl
    · exact absurd (hlt k hklt) (lt_irrefl _)
    · exact le_rfl

omit [MeasurableSpace Ω] in
/-- The ladder time exceeds `n` exactly when the drifted walk has stayed
nonpositive through index `n`. -/
theorem lt_gaussianAscendingLadderTime_iff (X : ℕ → Ω → ℝ) (a : ℝ) (n : ℕ) (ω : Ω) :
    (n : WithTop ℕ) < gaussianAscendingLadderTime X a ω ↔
      ∀ j ≤ n, gaussianDriftWalk X 0 a j ω ≤ 0 := by
  rw [gaussianAscendingLadderTime, lt_gaussianHalfLineExit_iff]
  constructor
  · intro h j hj
    have := h j hj
    rw [gaussianDriftWalk_reflect_neg_drift] at this
    linarith
  · intro h j hj
    have := h j hj
    rw [gaussianDriftWalk_reflect_neg_drift]
    linarith

theorem measurableSet_lt_gaussianAscendingLadderTime
    (hX : ∀ n, Measurable (X n)) (n : ℕ) :
    MeasurableSet {p : ℝ × Ω | (n : WithTop ℕ) < gaussianAscendingLadderTime X p.1 p.2} := by
  have heq : {p : ℝ × Ω | (n : WithTop ℕ) < gaussianAscendingLadderTime X p.1 p.2} =
      ⋂ j ∈ Finset.range (n+1),
        {p : ℝ × Ω | gaussianDriftWalk X 0 p.1 (j : ℕ) p.2 ≤ 0} := by
    ext p
    simp only [Set.mem_ofPred_eq, mem_iInter, Finset.mem_range, Nat.lt_succ_iff]
    exact lt_gaussianAscendingLadderTime_iff X p.1 n p.2
  rw [heq]
  exact MeasurableSet.biInter (Set.to_countable _)
    (fun j _ => measurableSet_le (gaussianDriftWalk_joint_measurable hX j) measurable_const)

/-- The ladder time is jointly measurable in the drift and the sample point. -/
theorem gaussianAscendingLadderTime_joint_measurable (hX : ∀ n, Measurable (X n)) :
    Measurable (fun p : ℝ × Ω => gaussianAscendingLadderTime X p.1 p.2) := by
  refine measurable_to_countable' fun y => ?_
  induction y using WithTop.recTopCoe with
  | top =>
      have heq : (fun p : ℝ × Ω => gaussianAscendingLadderTime X p.1 p.2) ⁻¹' {⊤} =
          ⋂ n : ℕ, {p : ℝ × Ω | (n : WithTop ℕ) < gaussianAscendingLadderTime X p.1 p.2} := by
        ext p
        simp only [mem_preimage, mem_singleton_iff, mem_iInter, Set.mem_ofPred_eq]
        constructor
        · intro h n
          rw [h]
          exact WithTop.coe_lt_top n
        · intro h
          by_contra hne
          lift gaussianAscendingLadderTime X p.1 p.2 to ℕ using hne with m hm
          exact absurd (h m) (lt_irrefl _)
      exact MeasurableSet.congr
        (MeasurableSet.iInter fun n => measurableSet_lt_gaussianAscendingLadderTime hX n) heq.symm
  | coe m =>
      have heq : (fun p : ℝ × Ω => gaussianAscendingLadderTime X p.1 p.2) ⁻¹' {(m : WithTop ℕ)} =
          (⋂ j ∈ Finset.range m, {p : ℝ × Ω | gaussianDriftWalk X 0 p.1 (j : ℕ) p.2 ≤ 0}) ∩
            {p : ℝ × Ω | 0 < gaussianDriftWalk X 0 p.1 m p.2} := by
        ext p
        simp only [mem_preimage, mem_singleton_iff, mem_inter_iff, mem_iInter, Finset.mem_range,
          Set.mem_ofPred_eq]
        constructor
        · intro h
          have hbelow : ∀ j, j < m → gaussianDriftWalk X 0 p.1 j p.2 ≤ 0 := by
            intro j hj
            have hlt : ((j : ℕ) : WithTop ℕ) < gaussianAscendingLadderTime X p.1 p.2 := by
              rw [h]
              exact WithTop.coe_lt_coe.mpr hj
            exact (lt_gaussianAscendingLadderTime_iff X p.1 j p.2).mp hlt j le_rfl
          refine ⟨hbelow, ?_⟩
          by_contra hle
          push Not at hle
          have hcon : (m : WithTop ℕ) < gaussianAscendingLadderTime X p.1 p.2 := by
            rw [(lt_gaussianAscendingLadderTime_iff X p.1 m p.2)]
            intro j hj
            rcases lt_or_eq_of_le hj with hlt | rfl
            · exact hbelow j hlt
            · exact hle
          rw [h] at hcon
          exact lt_irrefl _ hcon
        · rintro ⟨hbelow, hpos⟩
          have hlt : ∀ j < m, ((j : ℕ) : WithTop ℕ) < gaussianAscendingLadderTime X p.1 p.2 := by
            intro j hj
            rw [(lt_gaussianAscendingLadderTime_iff X p.1 j p.2)]
            intro i hi
            exact hbelow i (lt_of_le_of_lt hi hj)
          have hnotlt : ¬ ((m : ℕ) : WithTop ℕ) < gaussianAscendingLadderTime X p.1 p.2 := by
            rw [(lt_gaussianAscendingLadderTime_iff X p.1 m p.2)]
            push Not
            exact ⟨m, le_rfl, hpos⟩
          exact withTop_nat_eq_of_le_of_forall_lt (not_lt.mp hnotlt) hlt
      exact MeasurableSet.congr
        ((MeasurableSet.biInter (Set.to_countable _)
            (fun j _ => measurableSet_le (gaussianDriftWalk_joint_measurable hX j)
              measurable_const)).inter
          (measurableSet_lt measurable_const (gaussianDriftWalk_joint_measurable hX m)))
        heq.symm

/-- The ladder height is jointly measurable in the drift and the sample point. -/
theorem gaussianAscendingLadderHeight_joint_measurable (hX : ∀ n, Measurable (X n)) :
    Measurable (fun p : ℝ × Ω => gaussianAscendingLadderHeight X p.1 p.2) := by
  have hτ := gaussianAscendingLadderTime_joint_measurable hX
  have hnat : Measurable (fun p : ℝ × Ω => (gaussianAscendingLadderTime X p.1 p.2).untopD 0) :=
    hτ.untopD 0
  have hpos : Measurable (fun p : ℝ × Ω =>
      gaussianDriftWalk X 0 p.1 ((gaussianAscendingLadderTime X p.1 p.2).untopD 0) p.2) := by
    refine measurable_at_nat_index hnat (fun n => gaussianDriftWalk_joint_measurable hX n)
  have hset : MeasurableSet {p : ℝ × Ω | gaussianAscendingLadderTime X p.1 p.2 = ⊤} :=
    hτ (measurableSet_singleton ⊤)
  have heq : (fun p : ℝ × Ω => gaussianAscendingLadderHeight X p.1 p.2) =
      fun p => if gaussianAscendingLadderTime X p.1 p.2 = ⊤ then 0 else
        gaussianDriftWalk X 0 p.1 ((gaussianAscendingLadderTime X p.1 p.2).untopD 0) p.2 := by
    funext p
    by_cases hT : gaussianAscendingLadderTime X p.1 p.2 = ⊤
    · rw [if_pos hT]
      dsimp only [gaussianAscendingLadderTime] at hT
      unfold gaussianAscendingLadderHeight gaussianHalfLineOvershoot
      rw [if_pos hT]
    · rw [if_neg hT]
      exact gaussianAscendingLadderHeight_eq_position hT
  rw [heq]
  exact Measurable.ite hset measurable_const hpos


end SwingRepair
