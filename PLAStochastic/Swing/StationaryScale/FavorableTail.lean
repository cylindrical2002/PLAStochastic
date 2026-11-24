import PLAStochastic.Swing.StationaryScale.FavorableEvents

/-! # Uniform favorable tails of the actual stationary restart

The final index is first removed from each event by its predictable guard.
Only the fresh increment is Gaussian.  Charging back to the actual disjoint
completion events gives one Gaussian tail factor across both directions.
-/
noncomputable section
open Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {Ω : Type*}

/-- Survival through a prefix makes its actual constrained-SSE residual feasible. -/
theorem nativeRestartResidualAt_bound_of_survival (X : ℕ → Ω → ℝ) (E x : ℝ)
    (k : ℕ) (ω : Ω)
    (hsurv : ((k+1 : ℕ) : WithTop ℕ) ≤ nativeRestartLength X E x ω) :
    |nativeRestartResidualAt X E x k ω| ≤ E := by
  have hc := (le_nativePrefixLength_iff (nativeCarriedSamples X (fun _ => x))
    (fun _ => 0) E ω (k+1)).mp hsurv
  unfold nativePrefixFeasible at hc
  have hc' : ∃ m, feasibleSlope (Finset.Icc 1 (k+1)) (fun i => (i : ℝ))
      (fun i => nativeCarriedSamples X (fun _ => x) i ω) 0 0 E m := by
    simpa only [Nat.zero_add, Nat.cast_zero] using hc
  have ht : ∀ i ∈ Finset.Icc 1 (k+1), (0 : ℝ) < i := by
    intro i hi
    have := (Finset.mem_Icc.mp hi).1
    exact_mod_cast (by omega : 0 < i)
  have hf := nativeSelectedSlope_feasible (Finset.Icc 1 (k+1))
    (Finset.nonempty_Icc.mpr (by omega)) (fun i => (i : ℝ))
    (fun i => nativeCarriedSamples X (fun _ => x) i ω) 0 0 E ht hc'
  have hlast := hf (k+1) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
  dsimp only at hlast
  simpa only [nativeRestartResidualAt, nativeRestartSlopeAt,
    dif_pos (by omega : 0 < k+1), nativeCarriedSamples_succ,
    Nat.cast_zero, sub_zero, zero_add] using hlast

/-- The lower completion with a negative-margin tail is exactly a past guard
and one lower Gaussian half-line. -/
theorem nativeRestartFavorableLowerEvent_tail_eq_guard (X : ℕ → Ω → ℝ)
    {E : ℝ} (hE : 0 ≤ E) (x : ℝ) (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    {ω | (x,ω) ∈ nativeRestartFavorableLowerEvent X E k ∧
      t < max (|nativeRestartNext X E x ω|-E) 0} =
    {ω | ω ∈ nativeRestartFavorableLowerGuard X E x k ∧
      X k ω < -nativeRestartLowerGapAt X E x k ω-t} := by
  ext ω
  constructor
  · rintro ⟨he, htω⟩
    exact ⟨((nativeRestartFavorableLowerEvent_iff_guard X E k (x,ω)).mp he).1,
      (nativeRestartFavorableLowerEvent_tail_iff X hE k he ht).mp htω⟩
  · rintro ⟨hg, hz⟩
    have hr : X k ω < nativeRestartSlopeAt X E x (k+1) ω-
        nativeRestartLowerGapAt X E x k ω := by linarith [hg.2.2.1]
    have he := (nativeRestartFavorableLowerEvent_iff_guard X E k (x,ω)).mpr ⟨hg, hr⟩
    exact ⟨he, (nativeRestartFavorableLowerEvent_tail_iff X hE k he ht).mpr hz⟩

theorem nativeRestartFavorableUpperEvent_tail_eq_guard (X : ℕ → Ω → ℝ)
    {E : ℝ} (hE : 0 ≤ E) (x : ℝ) (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    {ω | (x,ω) ∈ nativeRestartFavorableUpperEvent X E k ∧
      t < max (|nativeRestartNext X E x ω|-E) 0} =
    {ω | ω ∈ nativeRestartFavorableUpperGuard X E x k ∧
      nativeRestartUpperGapAt X E x k ω+t < X k ω} := by
  ext ω
  constructor
  · rintro ⟨he, htω⟩
    exact ⟨((nativeRestartFavorableUpperEvent_iff_guard X E k (x,ω)).mp he).1,
      (nativeRestartFavorableUpperEvent_tail_iff X hE k he ht).mp htω⟩
  · rintro ⟨hg, hz⟩
    have hr : nativeRestartSlopeAt X E x (k+1) ω+
        nativeRestartUpperGapAt X E x k ω < X k ω := by linarith [hg.2.2.2]
    have he := (nativeRestartFavorableUpperEvent_iff_guard X E k (x,ω)).mpr ⟨hg, hr⟩
    exact ⟨he, (nativeRestartFavorableUpperEvent_tail_iff X hE k he ht).mpr hz⟩

section Probability
variable [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- Countable disjoint charging, stated for the two-direction index type used
by the restart decomposition.  The proof is the same measure tsum argument
as the existing Nat-indexed lemma, with no factor for the number of indices. -/
theorem measure_iUnion_le_of_disjoint_charging_countable
    {ι : Type*} [Countable ι] {A B : ι → Set Ω} {c : ℝ≥0∞}
    (hB : ∀ i, MeasurableSet (B i))
    (hd : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hcharge : ∀ i, μ (A i) ≤ c * μ (B i)) [IsProbabilityMeasure μ] :
    μ (⋃ i, A i) ≤ c := by
  calc
    μ (⋃ i, A i) ≤ ∑' i, μ (A i) := measure_iUnion_le _
    _ ≤ ∑' i, c * μ (B i) := ENNReal.tsum_le_tsum hcharge
    _ = c * (∑' i, μ (B i)) := ENNReal.tsum_mul_left
    _ = c * μ (⋃ i, B i) := by rw [measure_iUnion hd hB]
    _ ≤ c * 1 := mul_le_mul_right (prob_le_one (μ := μ)) _
    _ = c := mul_one _

/-- Convert a finite-probability real-measure charge to the ENNReal form used
by countable disjoint summation. -/
theorem measure_le_of_measureReal_charge
    {A B : Set Ω}
    {t : ℝ} [IsFiniteMeasure μ]
    (hc : μ.real A ≤ Real.exp (-t^2/2) * μ.real B) :
    μ A ≤ ENNReal.ofReal (Real.exp (-t^2/2)) * μ B := by
  have he := ENNReal.ofReal_le_ofReal hc
  rw [ENNReal.ofReal_mul (Real.exp_nonneg _), Measure.real,
    ENNReal.ofReal_toReal (measure_ne_top _ _), Measure.real,
    ENNReal.ofReal_toReal (measure_ne_top _ _)] at he
  exact he

/-- Combine the two favorable directions into one countable family. -/
def nativeRestartFavorableEventAt (X : ℕ → Ω → ℝ) (E : ℝ) (i : Bool × ℕ) :
    Set (ℝ × Ω) := if i.1 then nativeRestartFavorableUpperEvent X E i.2
      else nativeRestartFavorableLowerEvent X E i.2

def nativeRestartFavorableEventAtState (X : ℕ → Ω → ℝ) (E x : ℝ) (i : Bool × ℕ) :
    Set Ω := {ω | (x,ω) ∈ nativeRestartFavorableEventAt X E i}

theorem measurableSet_nativeRestartFavorableEventAt
    (hX : ∀ j, Measurable (X j)) (E : ℝ) (i : Bool × ℕ) :
    MeasurableSet (nativeRestartFavorableEventAt X E i) := by
  cases i with
  | mk b k => cases b <;> simp [nativeRestartFavorableEventAt,
      measurableSet_nativeRestartFavorableLowerEvent X hX E k,
      measurableSet_nativeRestartFavorableUpperEvent X hX E k]

theorem measurableSet_nativeRestartFavorableEventAtState
    (hX : ∀ j, Measurable (X j)) (E x : ℝ) (i : Bool × ℕ) :
    MeasurableSet (nativeRestartFavorableEventAtState X E x i) := by
  have h1 : Measurable (fun _ : Ω => x) := measurable_const
  have hp : Measurable (fun ω : Ω => (x, ω)) := h1.prod measurable_id
  exact (measurableSet_nativeRestartFavorableEventAt hX E i).preimage hp

omit mΩ in
theorem nativeRestartFavorableEventAt_pairwiseDisjoint
    (X : ℕ → Ω → ℝ) {E : ℝ} (hE : 0 ≤ E) :
    Pairwise (fun i j => Disjoint (nativeRestartFavorableEventAt X E i)
      (nativeRestartFavorableEventAt X E j)) := by
  rintro ⟨bi, ki⟩ ⟨bj, kj⟩ hij
  cases bi <;> cases bj
  · exact nativeRestartFavorableLowerEvent_pairwiseDisjoint X E (by
      intro h; apply hij; cases h; rfl)
  · exact nativeRestartFavorableLowerUpper_disjoint X hE ki kj
  · exact (nativeRestartFavorableLowerUpper_disjoint X hE kj ki).symm
  · exact nativeRestartFavorableUpperEvent_pairwiseDisjoint X E (by
      intro h; apply hij; cases h; rfl)

/-- The actual lower completion tail is charged to that same completion event. -/
theorem measureReal_nativeRestart_favorable_lower_charge
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ} (hE : 0 ≤ E)
    (x : ℝ) (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | (x,ω) ∈ nativeRestartFavorableLowerEvent X E k ∧
      t < max (|nativeRestartNext X E x ω|-E) 0} ≤
    Real.exp (-t^2/2)*μ.real {ω | (x,ω) ∈ nativeRestartFavorableLowerEvent X E k} := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hpair := (@iid_two_fresh_gaussians_of_history Ω Ω mΩ
    (incrementIndexSpace X (Iio k)) μ X hX hi hG k id measurable_id).1
  have hind : @IndepFun Ω Ω ℝ mΩ (incrementIndexSpace X (Iio k)) Real.measurableSpace
      (fun w => w) (X k) μ := by
    simpa only [Function.comp_def, id_eq] using hpair.comp measurable_id measurable_fst
  have hId : @Measurable Ω Ω mΩ (incrementIndexSpace X (Iio k)) id :=
    measurable_id.mono (incrementIndexSpace_le hX (Iio k)) le_rfl
  have hg0 : ∀ ω ∈ nativeRestartFavorableLowerGuard X E x k,
      0 ≤ nativeRestartLowerGapAt X E x k ω := by
    intro ω hω
    have hr := nativeRestartResidualAt_bound_of_survival X E x k ω hω.1
    dsimp only [nativeRestartLowerGapAt]
    linarith [(abs_le.mp hr).1]
  have hc := @independent_gaussian_favorable_lower_charge Ω Ω mΩ
    (incrementIndexSpace X (Iio k)) μ inferInstance (fun w => w) (X k) hId (hX k) hind (hG k)
    (nativeRestartFavorableLowerGuard X E x k)
    (measurableSet_nativeRestartFavorableLowerGuard_history X E x k)
    (nativeRestartLowerGapAt X E x k) (nativeRestartSlopeAt X E x (k+1))
    (nativeRestartLowerGapAt_measurable_history X E x k)
    (nativeRestartSlopeAt_measurable_history X E x k) hg0 (fun ω hω => hω.2.2.1) t ht
  rw [nativeRestartFavorableLowerEvent_tail_eq_guard X hE x k ht]
  have hb : {ω | ω ∈ nativeRestartFavorableLowerGuard X E x k ∧
      X k ω < nativeRestartSlopeAt X E x (k+1) ω-nativeRestartLowerGapAt X E x k ω} =
      {ω | (x,ω) ∈ nativeRestartFavorableLowerEvent X E k} := by
    ext ω
    exact (nativeRestartFavorableLowerEvent_iff_guard X E k (x,ω)).symm
  rwa [hb] at hc

theorem measureReal_nativeRestart_favorable_upper_charge
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ} (hE : 0 ≤ E)
    (x : ℝ) (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | (x,ω) ∈ nativeRestartFavorableUpperEvent X E k ∧
      t < max (|nativeRestartNext X E x ω|-E) 0} ≤
    Real.exp (-t^2/2)*μ.real {ω | (x,ω) ∈ nativeRestartFavorableUpperEvent X E k} := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hpair := (@iid_two_fresh_gaussians_of_history Ω Ω mΩ
    (incrementIndexSpace X (Iio k)) μ X hX hi hG k id measurable_id).1
  have hind : @IndepFun Ω Ω ℝ mΩ (incrementIndexSpace X (Iio k)) Real.measurableSpace
      (fun w => w) (X k) μ := by
    simpa only [Function.comp_def, id_eq] using hpair.comp measurable_id measurable_fst
  have hId : @Measurable Ω Ω mΩ (incrementIndexSpace X (Iio k)) id :=
    measurable_id.mono (incrementIndexSpace_le hX (Iio k)) le_rfl
  have hg0 : ∀ ω ∈ nativeRestartFavorableUpperGuard X E x k,
      0 ≤ nativeRestartUpperGapAt X E x k ω := by
    intro ω hω
    have hr := nativeRestartResidualAt_bound_of_survival X E x k ω hω.1
    dsimp only [nativeRestartUpperGapAt]
    linarith [(abs_le.mp hr).2]
  have hc := @independent_gaussian_favorable_upper_charge Ω Ω mΩ
    (incrementIndexSpace X (Iio k)) μ inferInstance (fun w => w) (X k) hId (hX k) hind (hG k)
    (nativeRestartFavorableUpperGuard X E x k)
    (measurableSet_nativeRestartFavorableUpperGuard_history X E x k)
    (nativeRestartUpperGapAt X E x k) (nativeRestartSlopeAt X E x (k+1))
    (nativeRestartUpperGapAt_measurable_history X E x k)
    (nativeRestartSlopeAt_measurable_history X E x k) hg0 (fun ω hω => hω.2.2.2) t ht
  rw [nativeRestartFavorableUpperEvent_tail_eq_guard X hE x k ht]
  have hb : {ω | ω ∈ nativeRestartFavorableUpperGuard X E x k ∧
      nativeRestartSlopeAt X E x (k+1) ω+nativeRestartUpperGapAt X E x k ω < X k ω} =
      {ω | (x,ω) ∈ nativeRestartFavorableUpperEvent X E k} := by
    ext ω
    exact (nativeRestartFavorableUpperEvent_iff_guard X E k (x,ω)).symm
  rwa [hb] at hc

theorem measure_nativeRestart_favorable_tail
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ} (hE : 0 ≤ E)
    (x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    μ (⋃ i : Bool × ℕ, {ω | (x,ω) ∈ nativeRestartFavorableEventAt X E i ∧
      t < max (|nativeRestartNext X E x ω|-E) 0}) ≤
      ENNReal.ofReal (Real.exp (-t^2/2)) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  let B : Bool × ℕ → Set Ω := fun i => nativeRestartFavorableEventAtState X E x i
  let A : Bool × ℕ → Set Ω := fun i => {ω | ω ∈ B i ∧
      t < max (|nativeRestartNext X E x ω|-E) 0}
  have hBm : ∀ i, MeasurableSet (B i) := by
    intro i
    exact measurableSet_nativeRestartFavorableEventAtState hX E x i
  have hBd : Pairwise (fun i j => Disjoint (B i) (B j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro ω hiω hjω
    have hi' : (x,ω) ∈ nativeRestartFavorableEventAt X E i := hiω
    have hj' : (x,ω) ∈ nativeRestartFavorableEventAt X E j := hjω
    have hd : Disjoint (nativeRestartFavorableEventAt X E i)
        (nativeRestartFavorableEventAt X E j) :=
      nativeRestartFavorableEventAt_pairwiseDisjoint X hE hij
    exact (Set.disjoint_left.mp hd hi') hj'
  have hcharge : ∀ i, μ (A i) ≤ ENNReal.ofReal (Real.exp (-t^2/2))*μ (B i) := by
    rintro ⟨b,k⟩
    cases b
    · simpa [A, B, nativeRestartFavorableEventAtState,
        nativeRestartFavorableEventAt] using
        (measure_le_of_measureReal_charge
          (measureReal_nativeRestart_favorable_lower_charge hX hi hG hE x k ht))
    · simpa [A, B, nativeRestartFavorableEventAtState,
        nativeRestartFavorableEventAt] using
        (measure_le_of_measureReal_charge
          (measureReal_nativeRestart_favorable_upper_charge hX hi hG hE x k ht))
  have hglobal := measure_iUnion_le_of_disjoint_charging_countable
    (μ := μ) (A := A) (B := B) hBm hBd hcharge
  simpa [A, B, nativeRestartFavorableEventAtState] using hglobal

end Probability
end SwingRepair
