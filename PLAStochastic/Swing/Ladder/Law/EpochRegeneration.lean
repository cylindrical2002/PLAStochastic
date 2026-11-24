import PLAStochastic.Swing.Ladder.Law.AscendingLaw
import PLAStochastic.ForMathlib.Probability.Process.IIDRestart.FutureSequence
import PLAStochastic.ForMathlib.Probability.Process.IIDRestart.RegenerativeSplit

/-! # The actual strict ascending ladder epochs regenerate

The first ladder epoch of the positive-drift Gaussian walk is a stopping time
for the increment filtration once it is written through the index of the
increment that completes it.  The existing stopped-sequence machinery then
gives the strong Markov restart, and the regeneration engine turns it into
genuine mutual independence and identical distribution of all ladder heights.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} {X : ℕ → Ω → ℝ}

/-- The ℕ-valued first strict ascending ladder epoch. -/
def gaussianAscendingLadderTimeNat (X : ℕ → Ω → ℝ) (a : ℝ) (ω : Ω) : ℕ :=
  (gaussianAscendingLadderTime X a ω).untopD 0

/-- The index of the increment that completes the first ladder step. -/
def gaussianAscendingLadderIndex (X : ℕ → Ω → ℝ) (a : ℝ) : Ω → WithTop ℕ :=
  hittingAfter (fun n ω => gaussianDriftWalk X 0 a (n+1) ω) (Ioi 0) 0

theorem gaussianDriftWalk_zero_eq (X : ℕ → Ω → ℝ) (a : ℝ) (ω : Ω) :
    gaussianDriftWalk X 0 a 0 ω = 0 := by
  simp [gaussianDriftWalk]

/-- The completing index is one below the ladder epoch, in the form the
increment filtration needs. -/
theorem gaussianAscendingLadderIndex_le_iff (X : ℕ → Ω → ℝ) (a : ℝ) (ω : Ω) (n : ℕ) :
    gaussianAscendingLadderIndex X a ω ≤ (n : WithTop ℕ) ↔
      gaussianAscendingLadderTime X a ω ≤ ((n+1 : ℕ) : WithTop ℕ) := by
  have h1 : gaussianAscendingLadderIndex X a ω ≤ (n : WithTop ℕ) ↔
      ∃ j ∈ Icc 0 n, gaussianDriftWalk X 0 a (j+1) ω ∈ Ioi (0 : ℝ) := hittingAfter_le_iff
  have h2 : gaussianAscendingLadderTime X a ω ≤ ((n+1 : ℕ) : WithTop ℕ) ↔
      ∃ m ∈ Icc 0 (n+1), gaussianDriftWalk X 0 a m ω ∈ Ioi (0 : ℝ) := by
    rw [gaussianAscendingLadderTime_eq_hittingAfter]
    exact hittingAfter_le_iff
  rw [h1, h2]
  constructor
  · rintro ⟨j, hj, hjs⟩
    have hjn := hj.2
    exact ⟨j+1, ⟨Nat.zero_le _, by omega⟩, hjs⟩
  · rintro ⟨m, hm, hms⟩
    have hmn := hm.2
    have hm0 : m ≠ 0 := by
      intro h
      rw [h, gaussianDriftWalk_zero_eq] at hms
      exact absurd hms (by simp)
    obtain ⟨j, rfl⟩ : ∃ j, m = j+1 := ⟨m-1, by omega⟩
    exact ⟨j, ⟨Nat.zero_le _, by omega⟩, hms⟩

theorem gaussianAscendingLadderIndex_eq_top_iff (X : ℕ → Ω → ℝ) (a : ℝ) (ω : Ω) :
    gaussianAscendingLadderIndex X a ω = ⊤ ↔ gaussianAscendingLadderTime X a ω = ⊤ := by
  have h1 : gaussianAscendingLadderIndex X a ω = ⊤ ↔
      ∀ j : ℕ, 0 ≤ j → gaussianDriftWalk X 0 a (j+1) ω ∉ Ioi (0 : ℝ) := hittingAfter_eq_top_iff
  have h2 : gaussianAscendingLadderTime X a ω = ⊤ ↔
      ∀ m : ℕ, 0 ≤ m → gaussianDriftWalk X 0 a m ω ∉ Ioi (0 : ℝ) := by
    rw [gaussianAscendingLadderTime_eq_hittingAfter]
    exact hittingAfter_eq_top_iff
  rw [h1, h2]
  constructor
  · intro h m _
    cases m with
    | zero =>
      rw [gaussianDriftWalk_zero_eq]
      simp
    | succ j => exact h j (Nat.zero_le j)
  · intro h j _
    exact h (j+1) (Nat.zero_le _)

theorem gaussianAscendingLadderIndex_ne_top (X : ℕ → Ω → ℝ) (a : ℝ) {ω : Ω}
    (hfin : gaussianAscendingLadderTime X a ω ≠ ⊤) :
    gaussianAscendingLadderIndex X a ω ≠ ⊤ :=
  fun h => hfin ((gaussianAscendingLadderIndex_eq_top_iff X a ω).mp h)

/-- The ladder epoch is the completing index plus one. -/
theorem gaussianAscendingLadderTimeNat_eq_index_succ (X : ℕ → Ω → ℝ) (a : ℝ) {ω : Ω}
    (hfin : gaussianAscendingLadderTime X a ω ≠ ⊤) :
    gaussianAscendingLadderTimeNat X a ω =
      (gaussianAscendingLadderIndex X a ω).untopD 0 + 1 := by
  obtain ⟨i, hi⟩ := WithTop.ne_top_iff_exists.mp
    (gaussianAscendingLadderIndex_ne_top X a hfin)
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hfin
  have hiv : (gaussianAscendingLadderIndex X a ω).untopD 0 = i := by
    rw [← hi, WithTop.untopD_coe]
  have hkv : gaussianAscendingLadderTimeNat X a ω = k := by
    rw [gaussianAscendingLadderTimeNat, ← hk, WithTop.untopD_coe]
  rw [hiv, hkv]
  have hle : gaussianAscendingLadderTime X a ω ≤ ((i+1 : ℕ) : WithTop ℕ) := by
    refine (gaussianAscendingLadderIndex_le_iff X a ω i).mp ?_
    rw [← hi]
    exact le_rfl
  have hk1 : k ≤ i+1 := by
    rw [← hk] at hle
    exact WithTop.coe_le_coe.mp hle
  have hkpos : 0 < k := by
    have hp := gaussianAscendingLadderTime_pos (X := X) a ω
    rw [← hk] at hp
    exact WithTop.coe_lt_coe.mp hp
  by_contra hne
  have hki : k ≤ i := by omega
  cases i with
  | zero => omega
  | succ j =>
    have hle2 : gaussianAscendingLadderTime X a ω ≤ ((j+1 : ℕ) : WithTop ℕ) := by
      rw [← hk]
      exact WithTop.coe_le_coe.mpr hki
    have hidx := (gaussianAscendingLadderIndex_le_iff X a ω j).mpr hle2
    rw [← hi] at hidx
    have hcontr : j+1 ≤ j := WithTop.coe_le_coe.mp hidx
    omega

/-! ### The completing index is a stopping time -/

variable [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem gaussianLadderWalk_adapted (hX : ∀ n, Measurable (X n)) (a : ℝ) :
    Adapted (incrementFiltration X hX) (fun n ω => gaussianDriftWalk X 0 a (n+1) ω) := by
  intro n
  have hcum : Measurable[incrementFiltration X hX n] (cumulativeSamples X (n+1)) :=
    cumulativeSamples_measurable_at hX (le_refl (n+1))
  have hm : Measurable[incrementFiltration X hX n]
      (fun ω => gaussianDriftWalk X 0 a (n+1) ω) := by
    simp only [gaussianDriftWalk]
    exact (measurable_const.add hcum).add measurable_const
  exact hm

theorem gaussianAscendingLadderIndex_isStoppingTime (hX : ∀ n, Measurable (X n)) (a : ℝ) :
    IsStoppingTime (incrementFiltration X hX) (gaussianAscendingLadderIndex X a) :=
  (gaussianLadderWalk_adapted hX a).isStoppingTime_hittingAfter measurableSet_Ioi

theorem gaussianAscendingLadderIndex_finite_ae
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) :
    ∀ᵐ ω ∂μ, gaussianAscendingLadderIndex X a ω ≠ ⊤ := by
  filter_upwards [gaussianAscendingLadderTime_finite_ae hX hi hG ha] with ω hω
  exact gaussianAscendingLadderIndex_ne_top X a hω

/-! ### The ladder height is measurable at the ladder epoch -/

omit mΩ in
theorem gaussianAscendingLadderHeight_of_index (X : ℕ → Ω → ℝ) (a : ℝ) {i : ℕ} {ω : Ω}
    (hi : gaussianAscendingLadderIndex X a ω = (i : WithTop ℕ)) :
    gaussianAscendingLadderHeight X a ω = gaussianDriftWalk X 0 a (i+1) ω := by
  have hfin : gaussianAscendingLadderTime X a ω ≠ ⊤ := by
    intro h
    rw [(gaussianAscendingLadderIndex_eq_top_iff X a ω).mpr h] at hi
    exact WithTop.coe_ne_top hi.symm
  have hpos := gaussianAscendingLadderHeight_eq_position (X := X) (a := a) (ω := ω) hfin
  have hnat : (gaussianAscendingLadderTime X a ω).untopD 0 = i+1 := by
    have := gaussianAscendingLadderTimeNat_eq_index_succ X a hfin
    rw [gaussianAscendingLadderTimeNat] at this
    rw [this, hi]
    simp
  rw [hpos, hnat]

omit mΩ in
theorem gaussianAscendingLadderHeight_of_index_top (X : ℕ → Ω → ℝ) (a : ℝ) {ω : Ω}
    (h : gaussianAscendingLadderIndex X a ω = ⊤) :
    gaussianAscendingLadderHeight X a ω = 0 := by
  have hT : gaussianAscendingLadderTime X a ω = ⊤ :=
    (gaussianAscendingLadderIndex_eq_top_iff X a ω).mp h
  unfold gaussianAscendingLadderHeight gaussianHalfLineOvershoot
  exact if_pos hT

theorem gaussianAscendingLadderHeight_measurable_stopped
    (hX : ∀ n, Measurable (X n)) (a : ℝ) :
    Measurable[(gaussianAscendingLadderIndex_isStoppingTime hX a).measurableSpace]
      (gaussianAscendingLadderHeight X a) := by
  have hτ := gaussianAscendingLadderIndex_isStoppingTime hX a
  have htop : MeasurableSet[hτ.measurableSpace]
      {ω | gaussianAscendingLadderIndex X a ω = ⊤} := by
    refine ⟨hτ.measurableSet_eq_top', fun i => ?_⟩
    convert (@MeasurableSet.empty Ω (incrementFiltration X hX i)) using 1
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨h1, h2⟩
    rw [h1] at h2
    exact absurd h2 (by simp)
  intro A hA
  have hdec : gaussianAscendingLadderHeight X a ⁻¹' A =
      (⋃ j : ℕ, (gaussianAscendingLadderHeight X a ⁻¹' A) ∩
          {ω | gaussianAscendingLadderIndex X a ω = (j : WithTop ℕ)}) ∪
        ((gaussianAscendingLadderHeight X a ⁻¹' A) ∩
          {ω | gaussianAscendingLadderIndex X a ω = ⊤}) := by
    ext ω
    constructor
    · intro hω
      rcases eq_or_ne (gaussianAscendingLadderIndex X a ω) ⊤ with h | h
      · exact Or.inr ⟨hω, h⟩
      · obtain ⟨j, hj⟩ := WithTop.ne_top_iff_exists.mp h
        exact Or.inl (Set.mem_iUnion.mpr ⟨j, hω, hj.symm⟩)
    · rintro (h | h)
      · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp h
        exact hj.1
      · exact h.1
  rw [hdec]
  refine MeasurableSet.union (MeasurableSet.iUnion fun j => ?_) ?_
  · refine (IsStoppingTime.measurableSet_inter_eq_iff hτ _ j).mpr ?_
    have hset : (gaussianAscendingLadderHeight X a ⁻¹' A) ∩
        {ω | gaussianAscendingLadderIndex X a ω = (j : WithTop ℕ)} =
        ((fun ω => gaussianDriftWalk X 0 a (j+1) ω) ⁻¹' A) ∩
          {ω | gaussianAscendingLadderIndex X a ω = (j : WithTop ℕ)} := by
      ext ω
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        show gaussianDriftWalk X 0 a (j+1) ω ∈ A
        rw [← gaussianAscendingLadderHeight_of_index X a h2]
        exact h1
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        show gaussianAscendingLadderHeight X a ω ∈ A
        rw [gaussianAscendingLadderHeight_of_index X a h2]
        exact h1
    refine MeasurableSet.congr ?_ hset.symm
    exact MeasurableSet.inter ((gaussianLadderWalk_adapted hX a) j hA) (hτ.measurableSet_eq j)
  · by_cases h0 : (0 : ℝ) ∈ A
    · have hset : (gaussianAscendingLadderHeight X a ⁻¹' A) ∩
          {ω | gaussianAscendingLadderIndex X a ω = ⊤} =
          {ω | gaussianAscendingLadderIndex X a ω = ⊤} := by
        ext ω
        constructor
        · exact fun h => h.2
        · intro h
          refine ⟨?_, h⟩
          rw [Set.mem_preimage, gaussianAscendingLadderHeight_of_index_top X a h]
          exact h0
      exact MeasurableSet.congr htop hset.symm
    · have hset : (gaussianAscendingLadderHeight X a ⁻¹' A) ∩
          {ω | gaussianAscendingLadderIndex X a ω = ⊤} = ∅ := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq,
          Set.mem_empty_iff_false, iff_false]
        rintro ⟨h1, h2⟩
        rw [gaussianAscendingLadderHeight_of_index_top X a h2] at h1
        exact h0 h1
      exact MeasurableSet.congr (@MeasurableSet.empty Ω hτ.measurableSpace) hset.symm

/-! ### Regeneration on the increment-sequence space -/

/-- The ladder height read off a concrete increment sequence. -/
def ladderSequenceHeight (a : ℝ) (w : ℕ → ℝ) : ℝ :=
  gaussianAscendingLadderHeight (fun n (v : ℕ → ℝ) => v n) a w

/-- Remove exactly the increments consumed by the first ladder step. -/
def ladderSequenceRestart (a : ℝ) (w : ℕ → ℝ) (j : ℕ) : ℝ :=
  w ((gaussianAscendingLadderIndex (fun n (v : ℕ → ℝ) => v n) a w).untopD 0 + 1 + j)

theorem ladderSequenceHeight_measurable (a : ℝ) : Measurable (ladderSequenceHeight a) :=
  gaussianAscendingLadderHeight_measurable (fun n => measurable_pi_apply n) a

theorem ladderSequenceIndex_measurable (a : ℝ) :
    Measurable (fun w : ℕ → ℝ =>
      (gaussianAscendingLadderIndex (fun n (v : ℕ → ℝ) => v n) a w).untopD 0) :=
  ((gaussianAscendingLadderIndex_isStoppingTime
    (fun n => measurable_pi_apply n) a).measurable').untopD 0

theorem ladderSequenceRestart_measurable (a : ℝ) : Measurable (ladderSequenceRestart a) := by
  apply measurable_pi_lambda
  intro j
  exact countableSelection_measurable (fun n => measurable_pi_apply n)
    (((ladderSequenceIndex_measurable a).add_const 1).add_const j)

omit mΩ in
theorem ladderSequenceHeight_apply (X : ℕ → Ω → ℝ) (a : ℝ) (ω : Ω) :
    ladderSequenceHeight a (fun k => X k ω) = gaussianAscendingLadderHeight X a ω := rfl

omit mΩ in
theorem ladderSequenceRestart_apply (X : ℕ → Ω → ℝ) (a : ℝ) (ω : Ω) (j : ℕ) :
    ladderSequenceRestart a (fun k => X k ω) j =
      X ((gaussianAscendingLadderIndex X a ω).untopD 0 + 1 + j) ω := rfl

variable [IsProbabilityMeasure μ]

/-- The first ladder step removes exactly the increments it consumes, and the
remaining sequence still has the original iid Gaussian law. -/
theorem ladderSequenceRestart_identDistrib
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) :
    IdentDistrib (fun ω => ladderSequenceRestart a (fun k => X k ω))
      (fun ω (j : ℕ) => X j ω) μ μ :=
  stoppedSequence_identDistrib hX hi (gaussianIncrements_identDistrib hX hG)
    (gaussianAscendingLadderIndex_isStoppingTime hX a)
    (gaussianAscendingLadderIndex_finite_ae hX hi hG ha)

/-- The first ladder height and the entire remaining sequence are independent. -/
theorem ladderSequenceSplit_indep
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) :
    IndepFun (fun ω => ladderSequenceHeight a (fun k => X k ω))
      (fun ω => ladderSequenceRestart a (fun k => X k ω)) μ := by
  have hτ := gaussianAscendingLadderIndex_isStoppingTime hX a
  have hH : Measurable[hτ.measurableSpace] (gaussianAscendingLadderHeight X a) :=
    gaussianAscendingLadderHeight_measurable_stopped hX a
  exact indep_of_indep_of_le_left
    (stoppedSequence_indep_stopped hX hi (gaussianIncrements_identDistrib hX hG) hτ
      (gaussianAscendingLadderIndex_finite_ae hX hi hG ha)).symm hH.comap_le

/-- The successive strict ascending ladder heights of the actual positive-drift
Gaussian walk. -/
def gaussianLadderHeightAt (X : ℕ → Ω → ℝ) (a : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  regenerativeFactor (ladderSequenceHeight a) (ladderSequenceRestart a)
    (fun ω (k : ℕ) => X k ω) n ω

omit mΩ [IsProbabilityMeasure μ] in
@[simp] theorem gaussianLadderHeightAt_zero (X : ℕ → Ω → ℝ) (a : ℝ) (ω : Ω) :
    gaussianLadderHeightAt X a 0 ω = gaussianAscendingLadderHeight X a ω := rfl

theorem gaussianLadderHeightAt_measurable (hX : ∀ n, Measurable (X n)) (a : ℝ) (n : ℕ) :
    Measurable (gaussianLadderHeightAt X a n) :=
  regenerativeFactor_measurable (ladderSequenceHeight_measurable a)
    (ladderSequenceRestart_measurable a) (measurable_pi_lambda _ hX) n

/-- Every ladder height has the first ladder-height law. -/
theorem gaussianLadderHeightAt_identDistrib
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) (n : ℕ) :
    IdentDistrib (gaussianLadderHeightAt X a n) (gaussianAscendingLadderHeight X a) μ μ :=
  regenerativeFactor_identDistrib (ladderSequenceHeight_measurable a)
    (ladderSequenceRestart_measurable a) (measurable_pi_lambda _ hX)
    (ladderSequenceRestart_identDistrib hX hi hG ha) n

/-- Genuine mutual independence of all strict ascending ladder heights. -/
theorem gaussianLadderHeights_iIndepFun
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) :
    iIndepFun (gaussianLadderHeightAt X a) μ :=
  regenerativeFactors_iIndepFun (ladderSequenceHeight_measurable a)
    (ladderSequenceRestart_measurable a) (measurable_pi_lambda _ hX)
    (ladderSequenceRestart_identDistrib hX hi hG ha)
    (ladderSequenceSplit_indep hX hi hG ha)

/-- Each ladder height has exactly the parameterised ladder law. -/
theorem gaussianLadderHeightAt_map
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) (n : ℕ) :
    μ.map (gaussianLadderHeightAt X a n) = gaussianAscendingLadderLaw X μ a :=
  (gaussianLadderHeightAt_identDistrib hX hi hG ha n).map_eq

end SwingRepair
