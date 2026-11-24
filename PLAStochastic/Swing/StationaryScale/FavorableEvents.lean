import PLAStochastic.Swing.StationaryScale.LowerRejectionCharging
import PLAStochastic.Swing.StationaryScale.AbsorptionArithmetic
import PLAStochastic.Swing.StationaryScale.StoppedSumTail

/-! # Favorable completion events of the actual restart

The index `k` denotes the last accepted prefix of length `k+1`; the new
increment is exactly `X k`.  The events keep the actual finite completion
clock, constrained-SSE slope, old cone endpoint, and rejection threshold.
They are defined jointly in the starting carry and fresh increment path so
that they may later be integrated against a stationary starting law.
-/
noncomputable section
open Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {Ω : Type*}

/-- The lower endpoint of the genuine accepted-prefix cone. -/
def nativeRestartLowerEndpointAt (X : ℕ → Ω → ℝ) (E x : ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  nativeConeLower (Finset.Icc 1 (k+1)) (Finset.nonempty_Icc.mpr (by omega))
    (fun i => (i : ℝ)) (fun i => nativeCarriedSamples X (fun _ => x) i ω) 0 0 E

/-- The upper endpoint of the genuine accepted-prefix cone. -/
def nativeRestartUpperEndpointAt (X : ℕ → Ω → ℝ) (E x : ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  nativeConeUpper (Finset.Icc 1 (k+1)) (Finset.nonempty_Icc.mpr (by omega))
    (fun i => (i : ℝ)) (fun i => nativeCarriedSamples X (fun _ => x) i ω) 0 0 E

/-- Last accepted residual, computed before observing `X k`. -/
def nativeRestartResidualAt (X : ℕ → Ω → ℝ) (E x : ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  x+cumulativeSamples X k ω-nativeRestartSlopeAt X E x (k+1) ω*((k+1 : ℕ) : ℝ)

def nativeRestartLowerGapAt (X : ℕ → Ω → ℝ) (E x : ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  E+nativeRestartResidualAt X E x k ω

def nativeRestartUpperGapAt (X : ℕ → Ω → ℝ) (E x : ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  E-nativeRestartResidualAt X E x k ω

/-- An actual finite completion whose SSE slope is the nonnegative lower
endpoint and whose last increment rejects below the old cone. -/
def nativeRestartFavorableLowerEvent (X : ℕ → Ω → ℝ) (E : ℝ) (k : ℕ) : Set (ℝ × Ω) :=
  {p | nativeRestartLength X E p.1 p.2 = ((k+1 : ℕ) : WithTop ℕ) ∧
    nativeRestartSlopeAt X E p.1 (k+1) p.2 = nativeRestartLowerEndpointAt X E p.1 k p.2 ∧
    0 ≤ nativeRestartSlopeAt X E p.1 (k+1) p.2 ∧
    nativeRestartSlopeAt X E p.1 (k+1) p.2 ≤ E ∧
    X k p.2 < nativeRestartSlopeAt X E p.1 (k+1) p.2-nativeRestartLowerGapAt X E p.1 k p.2}

/-- The reflected actual completion: a nonpositive upper endpoint and an
upper rejection by the next increment. -/
def nativeRestartFavorableUpperEvent (X : ℕ → Ω → ℝ) (E : ℝ) (k : ℕ) : Set (ℝ × Ω) :=
  {p | nativeRestartLength X E p.1 p.2 = ((k+1 : ℕ) : WithTop ℕ) ∧
    nativeRestartSlopeAt X E p.1 (k+1) p.2 = nativeRestartUpperEndpointAt X E p.1 k p.2 ∧
    -E ≤ nativeRestartSlopeAt X E p.1 (k+1) p.2 ∧
    nativeRestartSlopeAt X E p.1 (k+1) p.2 ≤ 0 ∧
    nativeRestartSlopeAt X E p.1 (k+1) p.2+nativeRestartUpperGapAt X E p.1 k p.2 < X k p.2}

section Measurability
variable [MeasurableSpace Ω]

theorem nativeRestartLowerEndpointAt_measurable (X : ℕ → Ω → ℝ)
    (hX : ∀ j, Measurable (X j)) (E : ℝ) (k : ℕ) :
    Measurable (fun p : ℝ × Ω => nativeRestartLowerEndpointAt X E p.1 k p.2) := by
  exact measurable_nativeConeLower _ _ _
    (nativeCarriedSamples (fun j (p : ℝ × Ω) => X j p.2) Prod.fst) 0 E
    measurable_const (fun j _ => nativeCarriedSamples_measurable
      (fun j => (hX j).comp measurable_snd) measurable_fst j)

theorem nativeRestartUpperEndpointAt_measurable (X : ℕ → Ω → ℝ)
    (hX : ∀ j, Measurable (X j)) (E : ℝ) (k : ℕ) :
    Measurable (fun p : ℝ × Ω => nativeRestartUpperEndpointAt X E p.1 k p.2) := by
  exact measurable_nativeConeUpper _ _ _
    (nativeCarriedSamples (fun j (p : ℝ × Ω) => X j p.2) Prod.fst) 0 E
    measurable_const (fun j _ => nativeCarriedSamples_measurable
      (fun j => (hX j).comp measurable_snd) measurable_fst j)

theorem nativeRestartResidualAt_measurable (X : ℕ → Ω → ℝ)
    (hX : ∀ j, Measurable (X j)) (E : ℝ) (k : ℕ) :
    Measurable (fun p : ℝ × Ω => nativeRestartResidualAt X E p.1 k p.2) := by
  have hW : Measurable (cumulativeSamples X k) :=
    Finset.measurable_sum _ (fun j _ => hX j)
  exact (measurable_fst.add (hW.comp measurable_snd)).sub
    ((nativeRestartSlopeAt_measurable X hX E (k+1)).mul_const _)

theorem nativeRestartLowerGapAt_measurable (X : ℕ → Ω → ℝ)
    (hX : ∀ j, Measurable (X j)) (E : ℝ) (k : ℕ) :
    Measurable (fun p : ℝ × Ω => nativeRestartLowerGapAt X E p.1 k p.2) :=
  measurable_const.add (nativeRestartResidualAt_measurable X hX E k)

theorem nativeRestartUpperGapAt_measurable (X : ℕ → Ω → ℝ)
    (hX : ∀ j, Measurable (X j)) (E : ℝ) (k : ℕ) :
    Measurable (fun p : ℝ × Ω => nativeRestartUpperGapAt X E p.1 k p.2) :=
  measurable_const.sub (nativeRestartResidualAt_measurable X hX E k)

theorem measurableSet_nativeRestartFavorableLowerEvent (X : ℕ → Ω → ℝ)
    (hX : ∀ j, Measurable (X j)) (E : ℝ) (k : ℕ) :
    MeasurableSet (nativeRestartFavorableLowerEvent X E k) := by
  have hm := nativeRestartSlopeAt_measurable X hX E (k+1)
  exact (measurableSet_eq_fun (nativeRestartLength_measurable X hX E) measurable_const).inter
    ((measurableSet_eq_fun hm (nativeRestartLowerEndpointAt_measurable X hX E k)).inter
      ((measurableSet_le measurable_const hm).inter
        ((measurableSet_le hm measurable_const).inter
          (measurableSet_lt ((hX k).comp measurable_snd)
            (hm.sub (nativeRestartLowerGapAt_measurable X hX E k))))))

theorem measurableSet_nativeRestartFavorableUpperEvent (X : ℕ → Ω → ℝ)
    (hX : ∀ j, Measurable (X j)) (E : ℝ) (k : ℕ) :
    MeasurableSet (nativeRestartFavorableUpperEvent X E k) := by
  have hm := nativeRestartSlopeAt_measurable X hX E (k+1)
  exact (measurableSet_eq_fun (nativeRestartLength_measurable X hX E) measurable_const).inter
    ((measurableSet_eq_fun hm (nativeRestartUpperEndpointAt_measurable X hX E k)).inter
      ((measurableSet_le measurable_const hm).inter
        ((measurableSet_le hm measurable_const).inter
          (measurableSet_lt (hm.add (nativeRestartUpperGapAt_measurable X hX E k))
            ((hX k).comp measurable_snd)))))

end Measurability
/-! ## Actual final index and margin identities -/

theorem nativeRestartLengthNat_eq_of_length_eq (X : ℕ → Ω → ℝ) (E x : ℝ)
    (k : ℕ) (ω : Ω)
    (hL : nativeRestartLength X E x ω = ((k+1 : ℕ) : WithTop ℕ)) :
    nativeRestartLengthNat X E x ω = k+1 := by
  change (nativeRestartLength X E x ω).untopD 0 = k+1
  rw [hL]
  rfl

theorem nativeRestartNext_eq_residual_add_increment (X : ℕ → Ω → ℝ) (E x : ℝ)
    (k : ℕ) (ω : Ω)
    (hL : nativeRestartLength X E x ω = ((k+1 : ℕ) : WithTop ℕ)) :
    nativeRestartNext X E x ω = nativeRestartResidualAt X E x k ω+X k ω := by
  have hN := nativeRestartLengthNat_eq_of_length_eq X E x k ω hL
  simp only [nativeRestartNext, nativeRestartSlope, hN, cumulativeSamples_succ,
    nativeRestartResidualAt]
  ring

theorem nativeRestartResidualAt_bound_of_length_eq (X : ℕ → Ω → ℝ) {E : ℝ}
    (hE : 0 ≤ E) (x : ℝ) (k : ℕ) (ω : Ω)
    (hL : nativeRestartLength X E x ω = ((k+1 : ℕ) : WithTop ℕ)) :
    |nativeRestartResidualAt X E x k ω| ≤ E := by
  have hf : nativeRestartLength X E x ω ≠ ⊤ := by rw [hL]; simp
  have hN := nativeRestartLengthNat_eq_of_length_eq X E x k ω hL
  have hres := nativeRestart_last_accepted_residual X hE x ω hf
  simpa only [nativeRestartSlope, hN, Nat.add_sub_cancel, nativeRestartResidualAt] using hres

/-- The lower-branch margin is the actual residual-gap overshoot. -/
theorem nativeRestartFavorableLowerEvent_negative_margin_eq (X : ℕ → Ω → ℝ)
    {E : ℝ} (hE : 0 ≤ E) (k : ℕ) {p : ℝ × Ω}
    (hp : p ∈ nativeRestartFavorableLowerEvent X E k) :
    max (|nativeRestartNext X E p.1 p.2|-E) 0 =
      max (-nativeRestartLowerGapAt X E p.1 k p.2-X k p.2) 0 := by
  rcases hp with ⟨hL, _hend, hm0, hmE, hrej⟩
  have hres := nativeRestartResidualAt_bound_of_length_eq X hE p.1 k p.2 hL
  have hg : 0 ≤ nativeRestartLowerGapAt X E p.1 k p.2 := by
    dsimp [nativeRestartLowerGapAt]
    linarith [(abs_le.mp hres).1]
  have heq : nativeRestartNext X E p.1 p.2 =
      -E+nativeRestartLowerGapAt X E p.1 k p.2+X k p.2 := by
    rw [nativeRestartNext_eq_residual_add_increment X E p.1 k p.2 hL]
    dsimp [nativeRestartLowerGapAt]
    ring
  rw [heq]
  exact (stationary_favorable_lower_geometry hE hm0 hmE hg hrej).2.2

/-- Exact tail event on a true favorable lower completion. -/
theorem nativeRestartFavorableLowerEvent_tail_iff (X : ℕ → Ω → ℝ)
    {E : ℝ} (hE : 0 ≤ E) (k : ℕ) {p : ℝ × Ω}
    (hp : p ∈ nativeRestartFavorableLowerEvent X E k) {t : ℝ} (ht : 0 ≤ t) :
    t < max (|nativeRestartNext X E p.1 p.2|-E) 0 ↔
      X k p.2 < -nativeRestartLowerGapAt X E p.1 k p.2-t := by
  rw [nativeRestartFavorableLowerEvent_negative_margin_eq X hE k hp, lt_max_iff]
  constructor
  · rintro (h | h) <;> linarith
  · intro h
    exact Or.inl (by linarith)

/-- The reflected branch also has its exact actual-margin overshoot. -/
theorem nativeRestartFavorableUpperEvent_negative_margin_eq (X : ℕ → Ω → ℝ)
    {E : ℝ} (_hE : 0 ≤ E) (k : ℕ) {p : ℝ × Ω}
    (hp : p ∈ nativeRestartFavorableUpperEvent X E k) :
    max (|nativeRestartNext X E p.1 p.2|-E) 0 =
      max (X k p.2-nativeRestartUpperGapAt X E p.1 k p.2) 0 := by
  rcases hp with ⟨hL, _hend, hmE, _hm0, hrej⟩
  have heq : nativeRestartNext X E p.1 p.2 =
      E-nativeRestartUpperGapAt X E p.1 k p.2+X k p.2 := by
    rw [nativeRestartNext_eq_residual_add_increment X E p.1 k p.2 hL]
    dsimp [nativeRestartUpperGapAt]
    ring
  have hnonneg : 0 ≤ nativeRestartNext X E p.1 p.2 := by rw [heq]; linarith
  rw [abs_of_nonneg hnonneg, heq]
  congr 1
  ring

theorem nativeRestartFavorableUpperEvent_tail_iff (X : ℕ → Ω → ℝ)
    {E : ℝ} (hE : 0 ≤ E) (k : ℕ) {p : ℝ × Ω}
    (hp : p ∈ nativeRestartFavorableUpperEvent X E k) {t : ℝ} (ht : 0 ≤ t) :
    t < max (|nativeRestartNext X E p.1 p.2|-E) 0 ↔
      nativeRestartUpperGapAt X E p.1 k p.2+t < X k p.2 := by
  rw [nativeRestartFavorableUpperEvent_negative_margin_eq X hE k hp, lt_max_iff]
  constructor
  · rintro (h | h) <;> linarith
  · intro h
    exact Or.inl (by linarith)

/-! ## Mutual exclusion of completed indices and directions -/

theorem nativeRestartFavorableLowerEvent_pairwiseDisjoint (X : ℕ → Ω → ℝ) (E : ℝ) :
    Pairwise (fun k l => Disjoint (nativeRestartFavorableLowerEvent X E k)
      (nativeRestartFavorableLowerEvent X E l)) := by
  intro k l hkl
  rw [Set.disjoint_left]
  intro p hk hl
  have heq : ((k+1 : ℕ) : WithTop ℕ) = ((l+1 : ℕ) : WithTop ℕ) := hk.1.symm.trans hl.1
  have heqN : k+1 = l+1 := WithTop.coe_injective heq
  exact hkl (by omega)

theorem nativeRestartFavorableUpperEvent_pairwiseDisjoint (X : ℕ → Ω → ℝ) (E : ℝ) :
    Pairwise (fun k l => Disjoint (nativeRestartFavorableUpperEvent X E k)
      (nativeRestartFavorableUpperEvent X E l)) := by
  intro k l hkl
  rw [Set.disjoint_left]
  intro p hk hl
  have heq : ((k+1 : ℕ) : WithTop ℕ) = ((l+1 : ℕ) : WithTop ℕ) := hk.1.symm.trans hl.1
  have heqN : k+1 = l+1 := WithTop.coe_injective heq
  exact hkl (by omega)

/-- Opposite rejection directions cannot occur at one actual completion. -/
theorem nativeRestartFavorableLowerUpper_disjoint (X : ℕ → Ω → ℝ)
    {E : ℝ} (hE : 0 ≤ E) (k l : ℕ) :
    Disjoint (nativeRestartFavorableLowerEvent X E k) (nativeRestartFavorableUpperEvent X E l) := by
  rw [Set.disjoint_left]
  intro p hk hl
  have heq : ((k+1 : ℕ) : WithTop ℕ) = ((l+1 : ℕ) : WithTop ℕ) := hk.1.symm.trans hl.1
  have heqN : k+1 = l+1 := WithTop.coe_injective heq
  have hkl : k = l := by omega
  subst l
  have hlo := hk.2.2.2.2
  have hhi := hl.2.2.2.2
  dsimp [nativeRestartLowerGapAt, nativeRestartUpperGapAt] at hlo hhi
  linarith

/-! ## Predictable accepted-prefix guards -/

/-- The lower favorable branch before seeing the prospective final increment.
Only survival through the accepted prefix is tested, not the final clock. -/
def nativeRestartFavorableLowerGuard (X : ℕ → Ω → ℝ) (E x : ℝ) (k : ℕ) : Set Ω :=
  {ω | ((k+1 : ℕ) : WithTop ℕ) ≤ nativeRestartLength X E x ω ∧
    nativeRestartSlopeAt X E x (k+1) ω = nativeRestartLowerEndpointAt X E x k ω ∧
    0 ≤ nativeRestartSlopeAt X E x (k+1) ω ∧
    nativeRestartSlopeAt X E x (k+1) ω ≤ E}

def nativeRestartFavorableUpperGuard (X : ℕ → Ω → ℝ) (E x : ℝ) (k : ℕ) : Set Ω :=
  {ω | ((k+1 : ℕ) : WithTop ℕ) ≤ nativeRestartLength X E x ω ∧
    nativeRestartSlopeAt X E x (k+1) ω = nativeRestartUpperEndpointAt X E x k ω ∧
    -E ≤ nativeRestartSlopeAt X E x (k+1) ω ∧
    nativeRestartSlopeAt X E x (k+1) ω ≤ 0}

theorem nativeRestart_samples_prefix_measurable_history (X : ℕ → Ω → ℝ)
    (x : ℝ) (k : ℕ) {j : ℕ} (hj : j ≤ k+1) :
    Measurable[incrementIndexSpace X (Iio k)] (nativeCarriedSamples X (fun _ => x) j) := by
  let : MeasurableSpace Ω := incrementIndexSpace X (Iio k)
  change Measurable (fun ω => nativeCarriedSamples X (fun _ => x) j ω)
  cases j with
  | zero =>
      simpa only [nativeCarriedSamples_zero] using (measurable_const (a := (0 : ℝ)))
  | succ j =>
      have hW : Measurable (cumulativeSamples X j) := by
        apply Finset.measurable_sum
        intro i hi
        exact incrementIndexSpace_eval (Set.mem_Iio.mpr (by
          have := Finset.mem_range.mp hi
          omega))
      simpa only [nativeCarriedSamples_succ] using!
        (measurable_const.add hW : Measurable (fun ω => x+cumulativeSamples X j ω))

theorem nativeRestartSlopeAt_measurable_history (X : ℕ → Ω → ℝ)
    (E x : ℝ) (k : ℕ) :
    Measurable[incrementIndexSpace X (Iio k)] (nativeRestartSlopeAt X E x (k+1)) := by
  let : MeasurableSpace Ω := incrementIndexSpace X (Iio k)
  change Measurable (fun ω => nativeRestartSlopeAt X E x (k+1) ω)
  simp only [nativeRestartSlopeAt, dif_pos (by omega : 0 < k+1)]
  exact measurable_nativeSelectedSlope _ _ _ (nativeCarriedSamples X (fun _ => x)) 0 E
    measurable_const (fun j hj => nativeRestart_samples_prefix_measurable_history X x k
      (Finset.mem_Icc.mp hj).2)

theorem nativeRestartLowerEndpointAt_measurable_history (X : ℕ → Ω → ℝ)
    (E x : ℝ) (k : ℕ) :
    Measurable[incrementIndexSpace X (Iio k)] (nativeRestartLowerEndpointAt X E x k) := by
  let : MeasurableSpace Ω := incrementIndexSpace X (Iio k)
  exact measurable_nativeConeLower _ _ _ (nativeCarriedSamples X (fun _ => x)) 0 E
    measurable_const (fun j hj => nativeRestart_samples_prefix_measurable_history X x k
      (Finset.mem_Icc.mp hj).2)

theorem nativeRestartUpperEndpointAt_measurable_history (X : ℕ → Ω → ℝ)
    (E x : ℝ) (k : ℕ) :
    Measurable[incrementIndexSpace X (Iio k)] (nativeRestartUpperEndpointAt X E x k) := by
  let : MeasurableSpace Ω := incrementIndexSpace X (Iio k)
  exact measurable_nativeConeUpper _ _ _ (nativeCarriedSamples X (fun _ => x)) 0 E
    measurable_const (fun j hj => nativeRestart_samples_prefix_measurable_history X x k
      (Finset.mem_Icc.mp hj).2)

theorem nativeRestartResidualAt_measurable_history (X : ℕ → Ω → ℝ)
    (E x : ℝ) (k : ℕ) :
    Measurable[incrementIndexSpace X (Iio k)] (nativeRestartResidualAt X E x k) := by
  let : MeasurableSpace Ω := incrementIndexSpace X (Iio k)
  have hW : Measurable (cumulativeSamples X k) := by
    apply Finset.measurable_sum
    intro j hj
    exact incrementIndexSpace_eval (Set.mem_Iio.mpr (Finset.mem_range.mp hj))
  exact (measurable_const.add hW).sub
    ((nativeRestartSlopeAt_measurable_history X E x k).mul_const _)

theorem nativeRestartLowerGapAt_measurable_history (X : ℕ → Ω → ℝ)
    (E x : ℝ) (k : ℕ) :
    Measurable[incrementIndexSpace X (Iio k)] (nativeRestartLowerGapAt X E x k) :=
  measurable_const.add (nativeRestartResidualAt_measurable_history X E x k)

theorem nativeRestartUpperGapAt_measurable_history (X : ℕ → Ω → ℝ)
    (E x : ℝ) (k : ℕ) :
    Measurable[incrementIndexSpace X (Iio k)] (nativeRestartUpperGapAt X E x k) :=
  measurable_const.sub (nativeRestartResidualAt_measurable_history X E x k)

theorem measurableSet_nativeRestartFavorableLowerGuard_history (X : ℕ → Ω → ℝ)
    (E x : ℝ) (k : ℕ) :
    MeasurableSet[incrementIndexSpace X (Iio k)] (nativeRestartFavorableLowerGuard X E x k) := by
  let : MeasurableSpace Ω := incrementIndexSpace X (Iio k)
  have hm := nativeRestartSlopeAt_measurable_history X E x k
  exact (measurableSet_nativeRestartLength_ge_history X E x k).inter
    ((measurableSet_eq_fun hm (nativeRestartLowerEndpointAt_measurable_history X E x k)).inter
      ((measurableSet_le measurable_const hm).inter (measurableSet_le hm measurable_const)))

theorem measurableSet_nativeRestartFavorableUpperGuard_history (X : ℕ → Ω → ℝ)
    (E x : ℝ) (k : ℕ) :
    MeasurableSet[incrementIndexSpace X (Iio k)] (nativeRestartFavorableUpperGuard X E x k) := by
  let : MeasurableSpace Ω := incrementIndexSpace X (Iio k)
  have hm := nativeRestartSlopeAt_measurable_history X E x k
  exact (measurableSet_nativeRestartLength_ge_history X E x k).inter
    ((measurableSet_eq_fun hm (nativeRestartUpperEndpointAt_measurable_history X E x k)).inter
      ((measurableSet_le measurable_const hm).inter (measurableSet_le hm measurable_const)))

/-- An accepted lower endpoint hit from below forces this exact final length.
Thus the completion clock need not be conditioned on in the charging step. -/
theorem nativeRestartLength_eq_of_lower_threshold (X : ℕ → Ω → ℝ) (E x : ℝ)
    (k : ℕ) (ω : Ω)
    (hsurv : ((k+1 : ℕ) : WithTop ℕ) ≤ nativeRestartLength X E x ω)
    (hend : nativeRestartSlopeAt X E x (k+1) ω = nativeRestartLowerEndpointAt X E x k ω)
    (hrej : X k ω < nativeRestartSlopeAt X E x (k+1) ω-nativeRestartLowerGapAt X E x k ω) :
    nativeRestartLength X E x ω = ((k+1 : ℕ) : WithTop ℕ) := by
  apply le_antisymm ?_ hsurv
  apply (nativePrefixLength_le_iff (nativeCarriedSamples X (fun _ => x))
    (fun _ => 0) E ω (k+1)).mpr
  refine ⟨k+1, le_rfl, ?_⟩
  rintro ⟨a, ha⟩
  have ht : ∀ i ∈ Finset.Icc 1 (k+1), (0 : ℝ) < i := by
    intro i hi
    have := (Finset.mem_Icc.mp hi).1
    exact_mod_cast (by omega : 0 < i)
  have haold : feasibleSlope (Finset.Icc 1 (k+1)) (fun i => (i : ℝ))
      (fun i => nativeCarriedSamples X (fun _ => x) i ω) 0 0 E a := by
    intro i hi
    have hi' := Finset.mem_Icc.mp hi
    simpa only [Nat.cast_zero, sub_zero, zero_add] using
      ha i (Finset.mem_Icc.mpr ⟨hi'.1, by omega⟩)
  have hlo : nativeRestartLowerEndpointAt X E x k ω ≤ a :=
    ((nativeCone_mem_iff _ _ _ _ 0 0 E a ht).mpr haold).1
  have hnew := ha (k+2) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  have hstep : nativeCarriedSamples X (fun _ => x) (k+2) ω =
      x+cumulativeSamples X k ω+X k ω := by
    rw [show k+2 = (k+1)+1 by omega, nativeCarriedSamples_succ, cumulativeSamples_succ]
    ring
  dsimp only at hnew
  simp only [Nat.cast_zero, sub_zero, zero_add] at hnew
  rw [hstep] at hnew
  have hma : nativeRestartSlopeAt X E x (k+1) ω ≤ a := hend ▸ hlo
  have hmul := mul_le_mul_of_nonneg_right hma (show (0 : ℝ) ≤ ((k+2 : ℕ) : ℝ) by positivity)
  dsimp [nativeRestartLowerGapAt, nativeRestartResidualAt] at hrej
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hnew hmul hrej
  nlinarith [(abs_le.mp hnew).1]

theorem nativeRestartLength_eq_of_upper_threshold (X : ℕ → Ω → ℝ) (E x : ℝ)
    (k : ℕ) (ω : Ω)
    (hsurv : ((k+1 : ℕ) : WithTop ℕ) ≤ nativeRestartLength X E x ω)
    (hend : nativeRestartSlopeAt X E x (k+1) ω = nativeRestartUpperEndpointAt X E x k ω)
    (hrej : nativeRestartSlopeAt X E x (k+1) ω+nativeRestartUpperGapAt X E x k ω < X k ω) :
    nativeRestartLength X E x ω = ((k+1 : ℕ) : WithTop ℕ) := by
  apply le_antisymm ?_ hsurv
  apply (nativePrefixLength_le_iff (nativeCarriedSamples X (fun _ => x))
    (fun _ => 0) E ω (k+1)).mpr
  refine ⟨k+1, le_rfl, ?_⟩
  rintro ⟨a, ha⟩
  have ht : ∀ i ∈ Finset.Icc 1 (k+1), (0 : ℝ) < i := by
    intro i hi
    have := (Finset.mem_Icc.mp hi).1
    exact_mod_cast (by omega : 0 < i)
  have haold : feasibleSlope (Finset.Icc 1 (k+1)) (fun i => (i : ℝ))
      (fun i => nativeCarriedSamples X (fun _ => x) i ω) 0 0 E a := by
    intro i hi
    have hi' := Finset.mem_Icc.mp hi
    simpa only [Nat.cast_zero, sub_zero, zero_add] using
      ha i (Finset.mem_Icc.mpr ⟨hi'.1, by omega⟩)
  have hhi : a ≤ nativeRestartUpperEndpointAt X E x k ω :=
    ((nativeCone_mem_iff _ _ _ _ 0 0 E a ht).mpr haold).2
  have hnew := ha (k+2) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  have hstep : nativeCarriedSamples X (fun _ => x) (k+2) ω =
      x+cumulativeSamples X k ω+X k ω := by
    rw [show k+2 = (k+1)+1 by omega, nativeCarriedSamples_succ, cumulativeSamples_succ]
    ring
  dsimp only at hnew
  simp only [Nat.cast_zero, sub_zero, zero_add] at hnew
  rw [hstep] at hnew
  have ham : a ≤ nativeRestartSlopeAt X E x (k+1) ω := hend ▸ hhi
  have hmul := mul_le_mul_of_nonneg_right ham (show (0 : ℝ) ≤ ((k+2 : ℕ) : ℝ) by positivity)
  dsimp [nativeRestartUpperGapAt, nativeRestartResidualAt] at hrej
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hnew hmul hrej
  nlinarith [(abs_le.mp hnew).2]

/-- Exact predictable-guard decomposition of the real lower completion. -/
theorem nativeRestartFavorableLowerEvent_iff_guard (X : ℕ → Ω → ℝ) (E : ℝ)
    (k : ℕ) (p : ℝ × Ω) :
    p ∈ nativeRestartFavorableLowerEvent X E k ↔
      p.2 ∈ nativeRestartFavorableLowerGuard X E p.1 k ∧
        X k p.2 < nativeRestartSlopeAt X E p.1 (k+1) p.2-nativeRestartLowerGapAt X E p.1 k p.2 := by
  constructor
  · rintro ⟨hL, hend, hm0, hmE, hrej⟩
    exact ⟨⟨hL.ge, hend, hm0, hmE⟩, hrej⟩
  · rintro ⟨⟨hsurv, hend, hm0, hmE⟩, hrej⟩
    exact ⟨nativeRestartLength_eq_of_lower_threshold X E p.1 k p.2 hsurv hend hrej,
      hend, hm0, hmE, hrej⟩

theorem nativeRestartFavorableUpperEvent_iff_guard (X : ℕ → Ω → ℝ) (E : ℝ)
    (k : ℕ) (p : ℝ × Ω) :
    p ∈ nativeRestartFavorableUpperEvent X E k ↔
      p.2 ∈ nativeRestartFavorableUpperGuard X E p.1 k ∧
        nativeRestartSlopeAt X E p.1 (k+1) p.2+nativeRestartUpperGapAt X E p.1 k p.2 < X k p.2 := by
  constructor
  · rintro ⟨hL, hend, hmE, hm0, hrej⟩
    exact ⟨⟨hL.ge, hend, hmE, hm0⟩, hrej⟩
  · rintro ⟨⟨hsurv, hend, hmE, hm0⟩, hrej⟩
    exact ⟨nativeRestartLength_eq_of_upper_threshold X E p.1 k p.2 hsurv hend hrej,
      hend, hmE, hm0, hrej⟩

end SwingRepair
