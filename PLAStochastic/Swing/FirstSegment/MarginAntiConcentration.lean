import PLAStochastic.Swing.FirstSegment.MarginCharging
import PLAStochastic.Swing.FirstSegment.MarginMoments

/-! # Lemma H.2 for the actual first completed segment

The output margin of the first segment is `E-|X'|` with `X'` the genuine
carried value.  Before the rejecting increment the whole segment state is
measurable, and `X'` is that state's shift plus the fresh increment.
-/
noncomputable section
open Classical
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Z : ℕ → Ω → ℝ}

/-- The actual recording of the accepted prefix of length `n+1`. -/
def nativeFirstShift (Z : ℕ → Ω → ℝ) (E : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  cumulativeSamples Z (n+1) ω-
    ((n+1 : ℕ) : ℝ)*nativeRestartSlopeAt (fun k => Z (1+k)) E (Z 0 ω) (n+1) ω

omit [MeasurableSpace Ω] in
theorem cumulativeSamples_succ_shift (Z : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    Z 0 ω+cumulativeSamples (fun k => Z (1+k)) n ω = cumulativeSamples Z (n+1) ω := by
  simp only [cumulativeSamples, Finset.sum_range_succ' (fun k => Z k ω) n]
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by rw [Nat.add_comm]

omit [MeasurableSpace Ω] in
/-- On the actual first-rejection fiber the carried value is the state shift
plus the rejecting increment. -/
theorem nativeFirstNext_eq_shift_add (Z : ℕ → Ω → ℝ) (E : ℝ) (n : ℕ) {ω : Ω}
    (hN : nativeRestartLengthNat (fun k => Z (1+k)) E (Z 0 ω) ω = n+1) :
    nativeFirstNext Z E ω = nativeFirstShift Z E n ω+Z (n+1) ω := by
  simp only [nativeFirstNext, nativeRestartNext, nativeRestartSlope, hN, nativeFirstShift]
  have hstep : cumulativeSamples Z (n+2) ω = cumulativeSamples Z (n+1) ω+Z (n+1) ω := by
    simpa only [Nat.add_assoc] using cumulativeSamples_succ Z (n+1) ω
  have hbase : Z 0 ω+cumulativeSamples (fun k => Z (1+k)) (n+1) ω = cumulativeSamples Z (n+2) ω :=
    cumulativeSamples_succ_shift Z (n+1) ω
  have : Z 0 ω+cumulativeSamples (fun k => Z (1+k)) (n+1) ω =
      cumulativeSamples Z (n+1) ω+Z (n+1) ω := by rw [hbase, hstep]
  rw [show Z 0 ω+cumulativeSamples (fun k => Z (1+k)) (n+1) ω-
      nativeRestartSlopeAt (fun k => Z (1+k)) E (Z 0 ω) (n+1) ω*((n+1 : ℕ) : ℝ) =
      (Z 0 ω+cumulativeSamples (fun k => Z (1+k)) (n+1) ω)-
        ((n+1 : ℕ) : ℝ)*nativeRestartSlopeAt (fun k => Z (1+k)) E (Z 0 ω) (n+1) ω by ring, this]
  ring

omit [MeasurableSpace Ω] in
theorem nativeFirstShift_eq (Z : ℕ → Ω → ℝ) (E : ℝ) (n : ℕ) (ω : Ω) :
    nativeFirstShift Z E n ω = cumulativeSamples Z (n+1) ω-
      ((n+1 : ℕ) : ℝ)*nativeSelectedSlope (Finset.Icc 1 (n+1))
        (Finset.nonempty_Icc.mpr (by omega : (1 : ℕ) ≤ n+1)) (fun i => (i : ℝ))
        (fun i => nativeCarriedSamples (fun k => Z (1+k)) (fun _ => Z 0 ω) i ω) 0 0 E := by
  simp only [nativeFirstShift, nativeRestartSlopeAt, dif_pos (by omega : 0 < n+1)]

omit [MeasurableSpace Ω] in
theorem nativeCarriedSamples_first_eq (Z : ℕ → Ω → ℝ) {i : ℕ} (hi : 1 ≤ i) (ω : Ω) :
    nativeCarriedSamples (fun k => Z (1+k)) (fun _ => Z 0 ω) i ω = cumulativeSamples Z i ω := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j+1 := ⟨i-1, by omega⟩
  rw [nativeCarriedSamples_succ]
  exact cumulativeSamples_succ_shift Z j ω

/-- The genuine segment state before the rejecting increment, as a function of
the observed history. -/
def nativeFirstMarginState (Z : ℕ → Ω → ℝ) (E : ℝ) (n : ℕ) (ω : Ω) : ℝ × ℝ × ℝ × Bool :=
  ((nativeFirstPrefixState (cumulativeSamples Z) E n ω).1,
    (nativeFirstPrefixState (cumulativeSamples Z) E n ω).2.1,
    nativeFirstShift Z E n ω,
    (nativeFirstPrefixState (cumulativeSamples Z) E n ω).2.2)

def nativeFirstMarginStateLower (Z : ℕ → Ω → ℝ) (E : ℝ) (n : ℕ) (ω : Ω) : ℝ × ℝ × ℝ × Bool :=
  (nativeFirstConeLower (cumulativeSamples Z) E n ω,
    nativeFirstLowerThreshold (cumulativeSamples Z) E n ω,
    nativeFirstShift Z E n ω,
    (nativeFirstPrefixState (cumulativeSamples Z) E n ω).2.2)

omit [MeasurableSpace Ω] in
theorem measurable_nativeFirstShift_history (Z : ℕ → Ω → ℝ) (E : ℝ) (n : ℕ) :
    Measurable[incrementIndexSpace Z (Iio (n+1))] (nativeFirstShift Z E n) := by
  let : MeasurableSpace Ω := incrementIndexSpace Z (Iio (n+1))
  have hY (j : ℕ) (hj : j ≤ n+1) : Measurable (cumulativeSamples Z j) := by
    apply Finset.measurable_sum
    intro k hk
    exact incrementIndexSpace_eval (X := Z)
      (show k ∈ Set.Iio (n+1) from Set.mem_Iio.mpr (by have := Finset.mem_range.mp hk; omega))
  have hW : ∀ i ∈ Finset.Icc 1 (n+1),
      Measurable (fun ω => nativeCarriedSamples (fun k => Z (1+k)) (fun _ => Z 0 ω) i ω) := by
    intro i hi
    have hi' := Finset.mem_Icc.mp hi
    have heq : (fun ω => nativeCarriedSamples (fun k => Z (1+k)) (fun _ => Z 0 ω) i ω) =
        cumulativeSamples Z i := funext fun ω => nativeCarriedSamples_first_eq Z hi'.1 ω
    rw [heq]
    exact hY i hi'.2
  have hslope := measurable_nativeSelectedSlope (Finset.Icc 1 (n+1))
    (Finset.nonempty_Icc.mpr (by omega : (1 : ℕ) ≤ n+1)) (fun i => (i : ℝ))
    (fun i ω => nativeCarriedSamples (fun k => Z (1+k)) (fun _ => Z 0 ω) i ω) 0 E
    (Q := fun _ => (0 : ℝ)) measurable_const hW
  have heq : nativeFirstShift Z E n = fun ω => cumulativeSamples Z (n+1) ω-
      ((n+1 : ℕ) : ℝ)*nativeSelectedSlope (Finset.Icc 1 (n+1))
        (Finset.nonempty_Icc.mpr (by omega : (1 : ℕ) ≤ n+1)) (fun i => (i : ℝ))
        (fun i => nativeCarriedSamples (fun k => Z (1+k)) (fun _ => Z 0 ω) i ω) 0 0 E :=
    funext fun ω => nativeFirstShift_eq Z E n ω
  rw [heq]
  exact (hY (n+1) le_rfl).sub (hslope.const_mul _)

omit [MeasurableSpace Ω] in
theorem measurable_nativeFirstMarginState_history (Z : ℕ → Ω → ℝ) (E : ℝ) (n : ℕ) :
    Measurable[incrementIndexSpace Z (Iio (n+1))] (nativeFirstMarginState Z E n) := by
  let : MeasurableSpace Ω := incrementIndexSpace Z (Iio (n+1))
  have hS := measurable_nativeFirstPrefixState_history Z E n
  have hV := measurable_nativeFirstShift_history Z E n
  exact hS.fst.prodMk (hS.snd.fst.prodMk (hV.prodMk hS.snd.snd))

theorem measurable_nativeFirstMarginState (hZ : ∀ j, Measurable (Z j)) (E : ℝ) (n : ℕ) :
    Measurable (nativeFirstMarginState Z E n) :=
  (measurable_nativeFirstMarginState_history Z E n).mono (incrementIndexSpace_le hZ _) le_rfl

/-- The guard on the small-threshold upper layer. -/
def marginUpperGuard (B : ℝ) : Set (ℝ × ℝ × ℝ × Bool) :=
  {p | p.2.2.2 = true ∧ p.1 ≤ B ∧ p.2.1 ≤ 1}

/-- The guard on the large-threshold upper layer. -/
def marginUpperLargeGuard (B : ℝ) : Set (ℝ × ℝ × ℝ × Bool) :=
  {p | p.2.2.2 = true ∧ p.1 ≤ B ∧ 1 < p.2.1}

theorem measurableSet_marginUpperGuard (B : ℝ) : MeasurableSet (marginUpperGuard B) :=
  (measurableSet_eq_fun measurable_snd.snd.snd measurable_const).inter
    ((measurableSet_le measurable_fst measurable_const).inter
      (measurableSet_le measurable_snd.fst measurable_const))

theorem measurableSet_marginUpperLargeGuard (B : ℝ) : MeasurableSet (marginUpperLargeGuard B) :=
  (measurableSet_eq_fun measurable_snd.snd.snd measurable_const).inter
    ((measurableSet_le measurable_fst measurable_const).inter
      (measurableSet_lt measurable_const measurable_snd.fst))

/-- The actual small-threshold upper layer of the margin target. -/
def nativeFirstMarginUpperSmallEvent (Z : ℕ → Ω → ℝ) (E B p q : ℝ) (n : ℕ) : Set Ω :=
  {ω | nativeFirstMarginState Z E n ω ∈ marginUpperGuard B ∧
    Z (n+1) ω ∈ marginTargetSet E (nativeFirstMarginState Z E n ω).2.2.1 p q ∧
    (nativeFirstMarginState Z E n ω).2.1 < Z (n+1) ω}

theorem measure_nativeFirstMarginUpperSmall_union_le
    (hZ : ∀ j, Measurable (Z j)) (hi : iIndepFun Z μ)
    (hG : ∀ j, μ.map (Z j) = gaussianReal 0 1) (E B : ℝ) {p q : ℝ} (hpq : p ≤ q) :
    μ (⋃ n, nativeFirstMarginUpperSmallEvent Z E B p q n) ≤
      ENNReal.ofReal (marginAntiConcentrationConstant*(q-p)) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  apply measure_iUnion_le_of_disjoint_charging (measurableSet_nativeFirstUpperRejectionEvent hZ E)
    (nativeFirstUpperRejectionEvent_disjoint Z E)
  intro n
  have hind := (iid_two_fresh_gaussians_of_history hZ hi hG (n+1)
    (measurable_nativeFirstMarginState_history Z E n)).1
  have hind' := hind.comp measurable_id measurable_fst
  have hc := independent_gaussian_margin_one_step_charge
    (measurable_nativeFirstMarginState hZ E n) (hZ (n+1))
    (by simpa only [Function.comp_def, id_eq] using hind') (hG (n+1))
    (measurableSet_marginUpperGuard B)
    (r := fun p : ℝ × ℝ × ℝ × Bool => p.2.1) (v := fun p : ℝ × ℝ × ℝ × Bool => p.2.2.1)
    measurable_snd.fst measurable_snd.snd.fst (Eb := E) hpq
    (fun x hx => hx.2.2)
  have hsub : {ω | nativeFirstMarginState Z E n ω ∈ marginUpperGuard B ∧
      (nativeFirstMarginState Z E n ω).2.1 < Z (n+1) ω} ⊆
      nativeFirstUpperRejectionEvent Z E n := by
    intro ω hω
    exact ⟨hω.1.1, hω.2⟩
  have hm := hc.trans (mul_le_mul_of_nonneg_left (measureReal_mono hsub)
    (mul_nonneg marginAntiConcentrationConstant_pos.le (sub_nonneg.mpr hpq)))
  have hsource : {ω | nativeFirstMarginState Z E n ω ∈ marginUpperGuard B ∧
      Z (n+1) ω ∈ marginTargetSet E ((fun p : ℝ × ℝ × ℝ × Bool => p.2.2.1)
        (nativeFirstMarginState Z E n ω)) p q ∧
      (fun p : ℝ × ℝ × ℝ × Bool => p.2.1) (nativeFirstMarginState Z E n ω) < Z (n+1) ω} =
      nativeFirstMarginUpperSmallEvent Z E B p q n := rfl
  rw [hsource] at hm
  have he := ENNReal.ofReal_le_ofReal hm
  rw [ENNReal.ofReal_mul (mul_nonneg marginAntiConcentrationConstant_pos.le (sub_nonneg.mpr hpq)),
    Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _),
    Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] at he
  exact he

/-- The actual large-threshold upper layer of the margin target. -/
def nativeFirstMarginUpperLargeEvent (Z : ℕ → Ω → ℝ) (E B p q : ℝ) (n : ℕ) : Set Ω :=
  {ω | nativeFirstMarginState Z E n ω ∈ marginUpperLargeGuard B ∧
    Z (n+1) ω ∈ marginTargetSet E (nativeFirstMarginState Z E n ω).2.2.1 p q ∧
    (nativeFirstMarginState Z E n ω).2.1 < Z (n+1) ω}

omit [MeasurableSpace Ω] in
/-- The two-step charging rectangle is contained in the genuine upper proxy event. -/
theorem nativeFirstMargin_upper_rectangle_subset (Z : ℕ → Ω → ℝ) (E B : ℝ) (n : ℕ) :
    {ω | nativeFirstMarginState Z E n ω ∈ marginUpperLargeGuard B ∧
      Z (n+1) ω ∈ Icc ((nativeFirstMarginState Z E n ω).2.1-1)
        ((nativeFirstMarginState Z E n ω).2.1-1/2) ∧ B+1 < Z (n+2) ω} ⊆
      nativeFirstUpperProxyEvent (cumulativeSamples Z) E n := by
  intro ω hω
  obtain ⟨hguard, hmid, hnext⟩ := hω
  have hflag : (nativeFirstPrefixState (cumulativeSamples Z) E n ω).2.2 = true := hguard.1
  have hfit : nativePrefixFeasible (fun j => (j : ℝ)) (fun j => cumulativeSamples Z j ω)
      E 0 (n+1) (cumulativeSamples Z 0 ω) := by
    dsimp only [nativeFirstPrefixState] at hflag
    by_contra hn
    simp only [if_neg hn, Bool.false_eq_true] at hflag
  have hu : (nativeFirstPrefixState (cumulativeSamples Z) E n ω).1 ≤ B := hguard.2.1
  have hm : (nativeFirstPrefixState (cumulativeSamples Z) E n ω).2.1-1 ≤ Z (n+1) ω ∧
      Z (n+1) ω ≤ (nativeFirstPrefixState (cumulativeSamples Z) E n ω).2.1-1/2 := mem_Icc.mp hmid
  dsimp only [nativeFirstPrefixState] at hm hu
  have hstep : cumulativeSamples Z (n+2) ω = cumulativeSamples Z (n+1) ω+Z (n+1) ω := by
    simpa only [Nat.add_assoc] using cumulativeSamples_succ Z (n+1) ω
  have hstep2 : cumulativeSamples Z (n+3) ω = cumulativeSamples Z (n+2) ω+Z (n+2) ω := by
    simpa only [Nat.add_assoc] using cumulativeSamples_succ Z (n+2) ω
  have e1 : n+1+1 = n+2 := by omega
  have e2 : n+1+2 = n+3 := by omega
  refine ⟨hfit, ?_, ?_⟩
  · simp only [e1]
    rw [hstep]
    exact mem_Icc.mpr ⟨by linarith [hm.2], by linarith [hm.1]⟩
  · simp only [e1, e2]
    rw [hstep2, hstep]
    linarith [hm.1, hm.2]

theorem measure_nativeFirstMarginUpperLarge_union_le
    (hZ : ∀ j, Measurable (Z j)) (hi : iIndepFun Z μ)
    (hG : ∀ j, μ.map (Z j) = gaussianReal 0 1) {E B : ℝ} (hE : 1 ≤ 2*E) (hB : 0 ≤ B)
    {p q : ℝ} (hpq : p ≤ q) :
    μ (⋃ n, nativeFirstMarginUpperLargeEvent Z E B p q n) ≤
      ENNReal.ofReal (4*(q-p)/(gaussianReal 0 1).real (Ioi (B+1))) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hβ : 0 < (gaussianReal 0 1).real (Ioi (B+1)) := gaussianReal_Ioi_real_pos (by linarith)
  have hcoef : 0 ≤ 4*(q-p)/(gaussianReal 0 1).real (Ioi (B+1)) := by
    have : 0 ≤ 4*(q-p) := by nlinarith [sub_nonneg.mpr hpq]
    positivity
  apply measure_iUnion_le_of_disjoint_charging
    (measurableSet_nativeFirstUpperProxyEvent (cumulativeSamples Z)
      (fun j => Finset.measurable_sum (Finset.range j) (fun k _ => hZ k)) E)
    (nativeFirstUpperProxyEvent_pairwiseDisjoint (cumulativeSamples Z) hE)
  intro n
  have hpair := iid_two_fresh_gaussians_of_history hZ hi hG (n+1)
    (measurable_nativeFirstMarginState_history Z E n)
  have hc := independent_gaussian_margin_two_step_charge
    (measurable_nativeFirstMarginState hZ E n) ((hZ (n+1)).prodMk (hZ (n+2)))
    hpair.1 hpair.2 (measurableSet_marginUpperLargeGuard B)
    (r := fun p : ℝ × ℝ × ℝ × Bool => p.2.1) (v := fun p : ℝ × ℝ × ℝ × Bool => p.2.2.1)
    measurable_snd.fst measurable_snd.snd.fst (Eb := E) (M := B) hpq (by linarith)
    (fun x hx => hx.2.2)
  have hm := hc.trans (mul_le_mul_of_nonneg_left
    (measureReal_mono (nativeFirstMargin_upper_rectangle_subset Z E B n)) hcoef)
  have hset : {ω | nativeFirstMarginState Z E n ω ∈ marginUpperLargeGuard B ∧
      ((Z (n+1) ω, Z (n+2) ω)).1 ∈ marginTargetSet E
        ((fun p : ℝ × ℝ × ℝ × Bool => p.2.2.1) (nativeFirstMarginState Z E n ω)) p q ∧
      (fun p : ℝ × ℝ × ℝ × Bool => p.2.1) (nativeFirstMarginState Z E n ω) <
        ((Z (n+1) ω, Z (n+2) ω)).1} = nativeFirstMarginUpperLargeEvent Z E B p q n := rfl
  rw [hset] at hm
  calc
    μ (nativeFirstMarginUpperLargeEvent Z E B p q n)
        = ENNReal.ofReal (μ.real (nativeFirstMarginUpperLargeEvent Z E B p q n)) :=
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (4*(q-p)/(gaussianReal 0 1).real (Ioi (B+1))*
          μ.real (nativeFirstUpperProxyEvent (cumulativeSamples Z) E n)) :=
      ENNReal.ofReal_le_ofReal hm
    _ = ENNReal.ofReal (4*(q-p)/(gaussianReal 0 1).real (Ioi (B+1)))*
          ENNReal.ofReal (μ.real (nativeFirstUpperProxyEvent (cumulativeSamples Z) E n)) :=
      ENNReal.ofReal_mul hcoef
    _ = ENNReal.ofReal (4*(q-p)/(gaussianReal 0 1).real (Ioi (B+1)))*
          μ (nativeFirstUpperProxyEvent (cumulativeSamples Z) E n) := by
      congr 1
      exact ENNReal.ofReal_toReal (measure_ne_top _ _)

/-! ## The mirrored lower layers -/

omit [MeasurableSpace Ω] in
theorem nativeConeUpper_neg_eq_nativeFirstConeLower (Z : ℕ → Ω → ℝ) (E : ℝ) (n : ℕ) (ω : Ω) :
    nativeConeUpper (Finset.Icc 1 (n+1)) (Finset.nonempty_Icc.mpr (by omega : (1 : ℕ) ≤ n+1))
      (fun j => (j : ℝ)) (fun j => cumulativeSamples (negIncrements Z) j ω) 0
      (cumulativeSamples (negIncrements Z) 0 ω) E =
      -nativeFirstConeLower (cumulativeSamples Z) E n ω :=
  congrArg Prod.fst (nativeFirstPrefixState_neg Z E n ω)

omit [MeasurableSpace Ω] in
theorem nativeFirstPrefixFeasible_neg_iff (Z : ℕ → Ω → ℝ) (E : ℝ) (n : ℕ) (ω : Ω)
    (hflag : (nativeFirstPrefixState (cumulativeSamples Z) E n ω).2.2 = true) :
    nativePrefixFeasible (fun j => (j : ℝ))
      (fun j => cumulativeSamples (negIncrements Z) j ω) E 0 (n+1)
      (cumulativeSamples (negIncrements Z) 0 ω) := by
  have hfit : nativePrefixFeasible (fun j => (j : ℝ)) (fun j => cumulativeSamples Z j ω)
      E 0 (n+1) (cumulativeSamples Z 0 ω) := by
    dsimp only [nativeFirstPrefixState] at hflag
    by_contra hn
    simp only [if_neg hn, Bool.false_eq_true] at hflag
  have hy : (fun j => cumulativeSamples (negIncrements Z) j ω) =
      (fun j => -(cumulativeSamples Z j ω)) := funext fun j => cumulativeSamples_neg Z j ω
  rw [hy, cumulativeSamples_neg Z 0 ω]
  exact (nativePrefixFeasible_neg _ _ E 0 (n+1) _).mpr hfit

omit [MeasurableSpace Ω] in
theorem measurable_nativeFirstMarginStateLower_history (Z : ℕ → Ω → ℝ) (E : ℝ) (n : ℕ) :
    Measurable[incrementIndexSpace Z (Iio (n+1))] (nativeFirstMarginStateLower Z E n) := by
  let : MeasurableSpace Ω := incrementIndexSpace Z (Iio (n+1))
  have hY (j : ℕ) (hj : j ≤ n+1) : Measurable (cumulativeSamples Z j) := by
    apply Finset.measurable_sum
    intro k hk
    exact incrementIndexSpace_eval (X := Z)
      (show k ∈ Set.Iio (n+1) from Set.mem_Iio.mpr (by have := Finset.mem_range.mp hk; omega))
  have hl := measurable_nativeConeLower (Finset.Icc 1 (n+1))
    (Finset.nonempty_Icc.mpr (by omega : (1 : ℕ) ≤ n+1)) (fun j => (j : ℝ))
    (cumulativeSamples Z) 0 E (hY 0 (by omega)) (fun j hj => hY j (Finset.mem_Icc.mp hj).2)
  have hthr : Measurable (nativeFirstLowerThreshold (cumulativeSamples Z) E n) :=
    (((hY 0 (by omega)).add (hl.const_mul ((n+2 : ℕ) : ℝ))).sub_const E).sub (hY (n+1) le_rfl)
  have hS := measurable_nativeFirstPrefixState_history Z E n
  have hV := measurable_nativeFirstShift_history Z E n
  exact hl.prodMk (hthr.prodMk (hV.prodMk hS.snd.snd))

theorem measurable_nativeFirstMarginStateLower (hZ : ∀ j, Measurable (Z j)) (E : ℝ) (n : ℕ) :
    Measurable (nativeFirstMarginStateLower Z E n) :=
  (measurable_nativeFirstMarginStateLower_history Z E n).mono (incrementIndexSpace_le hZ _) le_rfl

def marginLowerGuard (B : ℝ) : Set (ℝ × ℝ × ℝ × Bool) :=
  {p | p.2.2.2 = true ∧ -B ≤ p.1 ∧ -1 ≤ p.2.1}

def marginLowerLargeGuard (B : ℝ) : Set (ℝ × ℝ × ℝ × Bool) :=
  {p | p.2.2.2 = true ∧ -B ≤ p.1 ∧ p.2.1 < -1}

theorem measurableSet_marginLowerGuard (B : ℝ) : MeasurableSet (marginLowerGuard B) :=
  (measurableSet_eq_fun measurable_snd.snd.snd measurable_const).inter
    ((measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_le measurable_const measurable_snd.fst))

theorem measurableSet_marginLowerLargeGuard (B : ℝ) : MeasurableSet (marginLowerLargeGuard B) :=
  (measurableSet_eq_fun measurable_snd.snd.snd measurable_const).inter
    ((measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_lt measurable_snd.fst measurable_const))

def nativeFirstMarginLowerSmallEvent (Z : ℕ → Ω → ℝ) (E B p q : ℝ) (n : ℕ) : Set Ω :=
  {ω | nativeFirstMarginStateLower Z E n ω ∈ marginLowerGuard B ∧
    Z (n+1) ω ∈ marginTargetSet E (nativeFirstMarginStateLower Z E n ω).2.2.1 p q ∧
    Z (n+1) ω < (nativeFirstMarginStateLower Z E n ω).2.1}

def nativeFirstMarginLowerLargeEvent (Z : ℕ → Ω → ℝ) (E B p q : ℝ) (n : ℕ) : Set Ω :=
  {ω | nativeFirstMarginStateLower Z E n ω ∈ marginLowerLargeGuard B ∧
    Z (n+1) ω ∈ marginTargetSet E (nativeFirstMarginStateLower Z E n ω).2.2.1 p q ∧
    Z (n+1) ω < (nativeFirstMarginStateLower Z E n ω).2.1}

theorem measurableSet_nativeFirstLowerRejectionEvent (hZ : ∀ j, Measurable (Z j)) (E : ℝ) (n : ℕ) :
    MeasurableSet (nativeFirstLowerRejectionEvent Z E n) := by
  rw [nativeFirstLowerRejectionEvent_eq_neg]
  exact measurableSet_nativeFirstUpperRejectionEvent (fun j => (hZ j).neg) E n

omit [MeasurableSpace Ω] in
theorem nativeFirstLowerRejectionEvent_disjoint (Z : ℕ → Ω → ℝ) (E : ℝ) :
    Pairwise (fun n m => Disjoint (nativeFirstLowerRejectionEvent Z E n)
      (nativeFirstLowerRejectionEvent Z E m)) := by
  intro n m hnm
  simp only [nativeFirstLowerRejectionEvent_eq_neg]
  exact nativeFirstUpperRejectionEvent_disjoint (negIncrements Z) E hnm

theorem measure_nativeFirstMarginLowerSmall_union_le
    (hZ : ∀ j, Measurable (Z j)) (hi : iIndepFun Z μ)
    (hG : ∀ j, μ.map (Z j) = gaussianReal 0 1) (E B : ℝ) {p q : ℝ} (hpq : p ≤ q) :
    μ (⋃ n, nativeFirstMarginLowerSmallEvent Z E B p q n) ≤
      ENNReal.ofReal (2*marginAntiConcentrationConstant*(q-p)) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hcoef : (0 : ℝ) ≤ 2*marginAntiConcentrationConstant*(q-p) := by
    nlinarith [marginAntiConcentrationConstant_pos, sub_nonneg.mpr hpq]
  apply measure_iUnion_le_of_disjoint_charging (measurableSet_nativeFirstLowerRejectionEvent hZ E)
    (nativeFirstLowerRejectionEvent_disjoint Z E)
  intro n
  have hind := (iid_two_fresh_gaussians_of_history hZ hi hG (n+1)
    (measurable_nativeFirstMarginStateLower_history Z E n)).1
  have hind' := hind.comp measurable_id measurable_fst
  have hc := independent_gaussian_margin_one_step_charge_below
    (measurable_nativeFirstMarginStateLower hZ E n) (hZ (n+1))
    (by simpa only [Function.comp_def, id_eq] using hind') (hG (n+1))
    (measurableSet_marginLowerGuard B)
    (r := fun p : ℝ × ℝ × ℝ × Bool => p.2.1) (v := fun p : ℝ × ℝ × ℝ × Bool => p.2.2.1)
    measurable_snd.fst measurable_snd.snd.fst (Eb := E) hpq
    (fun x hx => hx.2.2)
  have hsub : {ω | nativeFirstMarginStateLower Z E n ω ∈ marginLowerGuard B ∧
      Z (n+1) ω < (nativeFirstMarginStateLower Z E n ω).2.1} ⊆
      nativeFirstLowerRejectionEvent Z E n := by
    intro ω hω
    exact ⟨hω.1.1, hω.2⟩
  have hm := hc.trans (mul_le_mul_of_nonneg_left (measureReal_mono hsub) hcoef)
  have hset : {ω | nativeFirstMarginStateLower Z E n ω ∈ marginLowerGuard B ∧
      Z (n+1) ω ∈ marginTargetSet E ((fun p : ℝ × ℝ × ℝ × Bool => p.2.2.1)
        (nativeFirstMarginStateLower Z E n ω)) p q ∧
      Z (n+1) ω < (fun p : ℝ × ℝ × ℝ × Bool => p.2.1) (nativeFirstMarginStateLower Z E n ω)} =
      nativeFirstMarginLowerSmallEvent Z E B p q n := rfl
  rw [hset] at hm
  calc
    μ (nativeFirstMarginLowerSmallEvent Z E B p q n)
        = ENNReal.ofReal (μ.real (nativeFirstMarginLowerSmallEvent Z E B p q n)) :=
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (2*marginAntiConcentrationConstant*(q-p)*
          μ.real (nativeFirstLowerRejectionEvent Z E n)) := ENNReal.ofReal_le_ofReal hm
    _ = ENNReal.ofReal (2*marginAntiConcentrationConstant*(q-p))*
          ENNReal.ofReal (μ.real (nativeFirstLowerRejectionEvent Z E n)) :=
      ENNReal.ofReal_mul hcoef
    _ = ENNReal.ofReal (2*marginAntiConcentrationConstant*(q-p))*
          μ (nativeFirstLowerRejectionEvent Z E n) := by
      congr 1
      exact ENNReal.ofReal_toReal (measure_ne_top _ _)

omit [MeasurableSpace Ω] in
/-- The mirrored two-step rectangle is contained in the reflected proxy event. -/
theorem nativeFirstMargin_lower_rectangle_subset (Z : ℕ → Ω → ℝ) (E B : ℝ) (n : ℕ) :
    {ω | nativeFirstMarginStateLower Z E n ω ∈ marginLowerLargeGuard B ∧
      Z (n+1) ω ∈ Icc ((nativeFirstMarginStateLower Z E n ω).2.1+1/2)
        ((nativeFirstMarginStateLower Z E n ω).2.1+1) ∧ Z (n+2) ω < -(B+1)} ⊆
      nativeFirstUpperProxyEvent (cumulativeSamples (negIncrements Z)) E n := by
  intro ω hω
  obtain ⟨hguard, hmid, hnext⟩ := hω
  have hflag : (nativeFirstPrefixState (cumulativeSamples Z) E n ω).2.2 = true := hguard.1
  have hfit := nativeFirstPrefixFeasible_neg_iff Z E n ω hflag
  have hl : -B ≤ nativeFirstConeLower (cumulativeSamples Z) E n ω := hguard.2.1
  have hm : nativeFirstLowerThreshold (cumulativeSamples Z) E n ω+1/2 ≤ Z (n+1) ω ∧
      Z (n+1) ω ≤ nativeFirstLowerThreshold (cumulativeSamples Z) E n ω+1 := mem_Icc.mp hmid
  dsimp only [nativeFirstLowerThreshold] at hm
  have hstep : cumulativeSamples Z (n+2) ω = cumulativeSamples Z (n+1) ω+Z (n+1) ω := by
    simpa only [Nat.add_assoc] using cumulativeSamples_succ Z (n+1) ω
  have hstep2 : cumulativeSamples Z (n+3) ω = cumulativeSamples Z (n+2) ω+Z (n+2) ω := by
    simpa only [Nat.add_assoc] using cumulativeSamples_succ Z (n+2) ω
  have e1 : n+1+1 = n+2 := by omega
  have e2 : n+1+2 = n+3 := by omega
  refine ⟨hfit, ?_, ?_⟩
  · rw [e1, nativeConeUpper_neg_eq_nativeFirstConeLower Z E n ω]
    simp only [cumulativeSamples_neg]
    rw [hstep]
    exact mem_Icc.mpr ⟨by linarith [hm.2], by linarith [hm.1]⟩
  · rw [e1, e2, nativeConeUpper_neg_eq_nativeFirstConeLower Z E n ω]
    simp only [cumulativeSamples_neg]
    rw [hstep2, hstep]
    linarith [hm.1, hm.2, hl, hnext]

theorem measure_nativeFirstMarginLowerLarge_union_le
    (hZ : ∀ j, Measurable (Z j)) (hi : iIndepFun Z μ)
    (hG : ∀ j, μ.map (Z j) = gaussianReal 0 1) {E B : ℝ} (hE : 1 ≤ 2*E) (hB : 0 ≤ B)
    {p q : ℝ} (hpq : p ≤ q) :
    μ (⋃ n, nativeFirstMarginLowerLargeEvent Z E B p q n) ≤
      ENNReal.ofReal (4*(q-p)/(gaussianReal 0 1).real (Iio (-(B+1)))) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hβ : 0 < (gaussianReal 0 1).real (Iio (-(B+1))) := gaussianReal_Iio_real_pos (by linarith)
  have hcoef : 0 ≤ 4*(q-p)/(gaussianReal 0 1).real (Iio (-(B+1))) := by
    have : 0 ≤ 4*(q-p) := by nlinarith [sub_nonneg.mpr hpq]
    positivity
  have hZneg : ∀ j, Measurable (negIncrements Z j) := fun j => (hZ j).neg
  apply measure_iUnion_le_of_disjoint_charging
    (measurableSet_nativeFirstUpperProxyEvent (cumulativeSamples (negIncrements Z))
      (fun j => Finset.measurable_sum (Finset.range j) (fun k _ => hZneg k)) E)
    (nativeFirstUpperProxyEvent_pairwiseDisjoint (cumulativeSamples (negIncrements Z)) hE)
  intro n
  have hpair := iid_two_fresh_gaussians_of_history hZ hi hG (n+1)
    (measurable_nativeFirstMarginStateLower_history Z E n)
  have hc := independent_gaussian_margin_two_step_charge_below
    (measurable_nativeFirstMarginStateLower hZ E n) ((hZ (n+1)).prodMk (hZ (n+2)))
    hpair.1 hpair.2 (measurableSet_marginLowerLargeGuard B)
    (r := fun p : ℝ × ℝ × ℝ × Bool => p.2.1) (v := fun p : ℝ × ℝ × ℝ × Bool => p.2.2.1)
    measurable_snd.fst measurable_snd.snd.fst (Eb := E) (M := B) hpq (by linarith)
    (fun x hx => hx.2.2)
  have hm := hc.trans (mul_le_mul_of_nonneg_left
    (measureReal_mono (nativeFirstMargin_lower_rectangle_subset Z E B n)) hcoef)
  have hset : {ω | nativeFirstMarginStateLower Z E n ω ∈ marginLowerLargeGuard B ∧
      ((Z (n+1) ω, Z (n+2) ω)).1 ∈ marginTargetSet E
        ((fun p : ℝ × ℝ × ℝ × Bool => p.2.2.1) (nativeFirstMarginStateLower Z E n ω)) p q ∧
      ((Z (n+1) ω, Z (n+2) ω)).1 <
        (fun p : ℝ × ℝ × ℝ × Bool => p.2.1) (nativeFirstMarginStateLower Z E n ω)} =
      nativeFirstMarginLowerLargeEvent Z E B p q n := rfl
  rw [hset] at hm
  calc
    μ (nativeFirstMarginLowerLargeEvent Z E B p q n)
        = ENNReal.ofReal (μ.real (nativeFirstMarginLowerLargeEvent Z E B p q n)) :=
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (4*(q-p)/(gaussianReal 0 1).real (Iio (-(B+1)))*
          μ.real (nativeFirstUpperProxyEvent (cumulativeSamples (negIncrements Z)) E n)) :=
      ENNReal.ofReal_le_ofReal hm
    _ = ENNReal.ofReal (4*(q-p)/(gaussianReal 0 1).real (Iio (-(B+1))))*
          ENNReal.ofReal (μ.real
            (nativeFirstUpperProxyEvent (cumulativeSamples (negIncrements Z)) E n)) :=
      ENNReal.ofReal_mul hcoef
    _ = ENNReal.ofReal (4*(q-p)/(gaussianReal 0 1).real (Iio (-(B+1))))*
          μ (nativeFirstUpperProxyEvent (cumulativeSamples (negIncrements Z)) E n) := by
      congr 1
      exact ENNReal.ofReal_toReal (measure_ne_top _ _)

/-! ## The covering argument and Lemma H.2 for the first segment -/

/-- Every actual first-segment margin in a target interval inside `[-B,B]` lies in one
of the four charged layers. -/
theorem nativeFirstMargin_mem_Icc_cover_ae
    (hZ : ∀ j, Measurable (Z j)) (hi : iIndepFun Z μ)
    (hG : ∀ j, μ.map (Z j) = gaussianReal 0 1) {E B p q : ℝ} (hE : 0 ≤ E) (hB : 0 ≤ B)
    (hpB : -B ≤ p) :
    ∀ᵐ ω ∂μ, nativeFirstMargin Z E ω ∈ Icc p q →
      ω ∈ (((⋃ n, nativeFirstMarginUpperSmallEvent Z E B p q n) ∪
        (⋃ n, nativeFirstMarginUpperLargeEvent Z E B p q n)) ∪
        ((⋃ n, nativeFirstMarginLowerSmallEvent Z E B p q n) ∪
          (⋃ n, nativeFirstMarginLowerLargeEvent Z E B p q n)) : Set Ω) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hts : StrictMono (fun n : ℕ => (n : ℝ)) := by
    intro a b hab
    change (a : ℝ) < b
    exact_mod_cast hab
  filter_upwards [firstRepairReject_ae_finite_gaussian hZ hi hG (ε := 2*E) (by linarith)]
    with ω hfin
  intro hmargin
  set Y : ℕ → Ω → ℝ := fun k => Z (1+k) with hY
  have hcone : ∀ j, nativePrefixFeasible (fun n => (n : ℝ))
      (fun n => cumulativeSamples Z n ω) E 0 j (cumulativeSamples Z 0 ω) ↔
        j < firstRepairSpan Z (2*E) ω := fun j =>
    (nativePrefix_trueAnchor_iff _ _ hts E 0 j).trans
      (prefixCone_iff_lt_firstRepairSpan Z (2*E) ω hfin j)
  have hK : 1 < firstRepairSpan Z (2*E) ω :=
    (hcone 1).mp (nativePrefix_singleton _ _ hts hE 0 _)
  obtain ⟨n, hn⟩ : ∃ n, firstRepairSpan Z (2*E) ω = n+2 := ⟨firstRepairSpan Z (2*E) ω-2, by omega⟩
  have hfit0 : nativePrefixFeasible (fun j => (j : ℝ)) (fun j => cumulativeSamples Z j ω)
      E 0 (n+1) (cumulativeSamples Z 0 ω) := (hcone (n+1)).mpr (by omega)
  have hrej0 : ¬ nativePrefixFeasible (fun j => (j : ℝ)) (fun j => cumulativeSamples Z j ω)
      E 0 (n+2) (cumulativeSamples Z 0 ω) := fun h => by
    have := (hcone (n+2)).mp h
    omega
  -- identify the rebased restart length with the actual first duration
  have hfeas : ∀ k, nativePrefixFeasible (fun i => (i : ℝ))
      (fun i => cumulativeSamples Z i ω) E 0 k 0 ↔
        (k : WithTop ℕ) ≤ nativeRestartLength Y E (Z 0 ω) ω := by
    intro k
    simpa [cumulativeSamples, Y] using nativeRestart_feasible_iff Z 0 k E 0 ω
  have hfitz : nativePrefixFeasible (fun j => (j : ℝ)) (fun j => cumulativeSamples Z j ω)
      E 0 (n+1) 0 := by simpa only [cumulativeSamples_zero] using hfit0
  have hrejz : ¬ nativePrefixFeasible (fun j => (j : ℝ)) (fun j => cumulativeSamples Z j ω)
      E 0 (n+2) 0 := by
    simp only [← cumulativeSamples_zero Z ω]
    exact hrej0
  have hlen : nativeRestartLength Y E (Z 0 ω) ω = ((n+1 : ℕ) : WithTop ℕ) := by
    apply le_antisymm _ ((hfeas (n+1)).mp hfitz)
    by_contra hnot
    have hgt : ((n+1 : ℕ) : WithTop ℕ) < nativeRestartLength Y E (Z 0 ω) ω := lt_of_not_ge hnot
    have hnext : ((n+2 : ℕ) : WithTop ℕ) ≤ nativeRestartLength Y E (Z 0 ω) ω := by
      cases heq : nativeRestartLength Y E (Z 0 ω) ω using WithTop.recTopCoe with
      | top => exact le_top
      | coe j =>
        rw [heq] at hgt
        have hj : n+1 < j := WithTop.coe_lt_coe.mp hgt
        exact WithTop.coe_le_coe.mpr (show n+2 ≤ j by omega)
    exact hrejz ((hfeas (n+2)).mpr hnext)
  have hNat : nativeRestartLengthNat Y E (Z 0 ω) ω = n+1 := by
    change (nativeRestartLength Y E (Z 0 ω) ω).untopD 0 = n+1
    rw [hlen]
    rfl
  -- the selected slope sits inside the actual cone
  have hslopefeas : feasibleSlope (Finset.Icc 1 (n+1)) (fun i => (i : ℝ))
      (fun i => cumulativeSamples Z i ω) 0 0 E
      (nativeRestartSlopeAt Y E (Z 0 ω) (n+1) ω) := by
    have hf : nativeRestartLength Y E (Z 0 ω) ω ≠ ⊤ := by rw [hlen]; exact WithTop.coe_ne_top
    have hfs := nativeRestartSlope_feasible Y hE (Z 0 ω) ω hf
    rw [hNat] at hfs
    intro i hi
    have heq : nativeCarriedSamples Y (fun _ => Z 0 ω) i ω = cumulativeSamples Z i ω :=
      nativeCarriedSamples_first_eq Z (Finset.mem_Icc.mp hi).1 ω
    have hval : nativeRestartSlope Y E (Z 0 ω) ω = nativeRestartSlopeAt Y E (Z 0 ω) (n+1) ω := by
      rw [nativeRestartSlope, hNat]
    rw [← hval]
    simpa only [heq] using hfs i hi
  have hbounds := (nativeCone_mem_iff (Finset.Icc 1 (n+1))
    (Finset.nonempty_Icc.mpr (by omega : (1 : ℕ) ≤ n+1)) (fun i => (i : ℝ))
    (fun i => cumulativeSamples Z i ω) 0 0 E (nativeRestartSlopeAt Y E (Z 0 ω) (n+1) ω)
    (fun i hi => by
      have := (Finset.mem_Icc.mp hi).1
      exact_mod_cast (show 0 < i by omega))).mpr hslopefeas
  have hzero : cumulativeSamples Z 0 ω = 0 := cumulativeSamples_zero Z ω
  have hshift : nativeFirstShift Z E n ω =
      cumulativeSamples Z (n+1) ω-((n+1 : ℕ) : ℝ)*nativeRestartSlopeAt Y E (Z 0 ω) (n+1) ω := rfl
  have hnext : nativeFirstNext Z E ω = nativeFirstShift Z E n ω+Z (n+1) ω :=
    nativeFirstNext_eq_shift_add Z E n hNat
  have htarget : Z (n+1) ω ∈ marginTargetSet E (nativeFirstShift Z E n ω) p q := by
    have : E-|nativeFirstShift Z E n ω+Z (n+1) ω| ∈ Icc p q := by
      rw [← hnext]
      exact hmargin
    exact this
  have hstep : cumulativeSamples Z (n+2) ω = cumulativeSamples Z (n+1) ω+Z (n+1) ω := by
    simpa only [Nat.add_assoc] using cumulativeSamples_succ Z (n+1) ω
  have hflag : (nativeFirstPrefixState (cumulativeSamples Z) E n ω).2.2 = true := by
    dsimp only [nativeFirstPrefixState]
    rw [if_pos hfit0]
  have hmem := nativeFirst_rejection_upper_or_lower Z hE n hfit0 hrej0
  rcases hmem with hup | hlow
  · -- the upper layers
    have hu : (nativeFirstPrefixState (cumulativeSamples Z) E n ω).1 ≤ B := by
      by_contra hbigraw
      have hbig := lt_of_not_ge hbigraw
      have hrejineq : (nativeFirstPrefixState (cumulativeSamples Z) E n ω).2.1 < Z (n+1) ω := hup.2
      dsimp only [nativeFirstPrefixState] at hbig hrejineq
      rw [hzero] at hrejineq hbig
      have hcast : (0 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by positivity
      have hmu := mul_le_mul_of_nonneg_left hbounds.2 hcast
      have hXbig : E+B < nativeFirstShift Z E n ω+Z (n+1) ω := by
        rw [hshift]
        push_cast at hrejineq hmu ⊢
        linarith
      have hmarg : p ≤ E-|nativeFirstShift Z E n ω+Z (n+1) ω| := by
        have h := (mem_Icc.mp hmargin).1
        rw [nativeFirstMargin, hnext] at h
        exact h
      have habs : E+B < |nativeFirstShift Z E n ω+Z (n+1) ω| :=
        lt_of_lt_of_le hXbig (le_abs_self _)
      linarith
    by_cases hsmallr : (nativeFirstPrefixState (cumulativeSamples Z) E n ω).2.1 ≤ 1
    · exact Or.inl (Or.inl (mem_iUnion.mpr ⟨n, ⟨hflag, hu, hsmallr⟩, htarget, hup.2⟩))
    · exact Or.inl (Or.inr (mem_iUnion.mpr
        ⟨n, ⟨hflag, hu, lt_of_not_ge hsmallr⟩, htarget, hup.2⟩))
  · -- the lower layers
    have hlow' := nativeFirstLowerRejectionEvent_spec Z E n hlow
    have hl : -B ≤ nativeFirstConeLower (cumulativeSamples Z) E n ω := by
      by_contra hbigraw
      have hbig := lt_of_not_ge hbigraw
      have hrejineq : Z (n+1) ω < nativeFirstLowerThreshold (cumulativeSamples Z) E n ω := hlow.2
      dsimp only [nativeFirstLowerThreshold, nativeFirstConeLower] at hrejineq
      dsimp only [nativeFirstConeLower] at hbig
      rw [hzero] at hrejineq hbig
      have hcast : (0 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by positivity
      have hmu := mul_le_mul_of_nonneg_left hbounds.1 hcast
      have hXsmall : nativeFirstShift Z E n ω+Z (n+1) ω < -(E+B) := by
        rw [hshift]
        push_cast at hrejineq hmu ⊢
        linarith
      have hmarg : p ≤ E-|nativeFirstShift Z E n ω+Z (n+1) ω| := by
        have h := (mem_Icc.mp hmargin).1
        rw [nativeFirstMargin, hnext] at h
        exact h
      have habs : E+B < |nativeFirstShift Z E n ω+Z (n+1) ω| := by
        rw [abs_of_neg (by linarith)]
        linarith
      linarith
    by_cases hsmallr : -1 ≤ nativeFirstLowerThreshold (cumulativeSamples Z) E n ω
    · exact Or.inr (Or.inl (mem_iUnion.mpr ⟨n, ⟨hflag, hl, hsmallr⟩, htarget, hlow.2⟩))
    · exact Or.inr (Or.inr (mem_iUnion.mpr
        ⟨n, ⟨hflag, hl, lt_of_not_ge hsmallr⟩, htarget, hlow.2⟩))

/-- The absolute anti-concentration constant of Lemma H.2 for a target window
inside `[-B,B]`. -/
def nativeFirstMarginConcentrationConstant (B : ℝ) : ℝ :=
  3*marginAntiConcentrationConstant+4/(gaussianReal 0 1).real (Ioi (B+1))+
    4/(gaussianReal 0 1).real (Iio (-(B+1)))

theorem nativeFirstMarginConcentrationConstant_nonneg {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ nativeFirstMarginConcentrationConstant B := by
  have h1 : 0 < (gaussianReal 0 1).real (Ioi (B+1)) := gaussianReal_Ioi_real_pos (by linarith)
  have h2 : 0 < (gaussianReal 0 1).real (Iio (-(B+1))) := gaussianReal_Iio_real_pos (by linarith)
  have h3 := marginAntiConcentrationConstant_pos
  dsimp [nativeFirstMarginConcentrationConstant]
  positivity

/-- Lemma H.2 for the actual first completed segment: the output margin has a
density-type bound on every target interval inside `[-B,B]`, with a constant
independent of the budget `E`. -/
theorem measureReal_nativeFirstMargin_mem_Icc_le
    (hZ : ∀ j, Measurable (Z j)) (hi : iIndepFun Z μ)
    (hG : ∀ j, μ.map (Z j) = gaussianReal 0 1) {E B p q : ℝ} (hE : 1 ≤ 2*E) (hB : 0 ≤ B)
    (hpq : p ≤ q) (hpB : -B ≤ p) :
    μ.real {ω | nativeFirstMargin Z E ω ∈ Icc p q} ≤
      nativeFirstMarginConcentrationConstant B*(q-p) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hE0 : 0 ≤ E := by linarith
  have hqp : 0 ≤ q-p := sub_nonneg.mpr hpq
  have hβ1 : 0 < (gaussianReal 0 1).real (Ioi (B+1)) := gaussianReal_Ioi_real_pos (by linarith)
  have hβ2 : 0 < (gaussianReal 0 1).real (Iio (-(B+1))) := gaussianReal_Iio_real_pos (by linarith)
  have hC0 := marginAntiConcentrationConstant_pos
  have hcov := ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono_ae (nativeFirstMargin_mem_Icc_cover_ae hZ hi hG hE0 hB hpB (q := q)))
  have hus := measure_nativeFirstMarginUpperSmall_union_le hZ hi hG E B hpq
  have hul := measure_nativeFirstMarginUpperLarge_union_le hZ hi hG hE hB hpq
  have hls := measure_nativeFirstMarginLowerSmall_union_le hZ hi hG E B hpq
  have hll := measure_nativeFirstMarginLowerLarge_union_le hZ hi hG hE hB hpq
  have hus' : μ.real (⋃ n, nativeFirstMarginUpperSmallEvent Z E B p q n) ≤
      marginAntiConcentrationConstant*(q-p) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hus
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  have hul' : μ.real (⋃ n, nativeFirstMarginUpperLargeEvent Z E B p q n) ≤
      4*(q-p)/(gaussianReal 0 1).real (Ioi (B+1)) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hul
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  have hls' : μ.real (⋃ n, nativeFirstMarginLowerSmallEvent Z E B p q n) ≤
      2*marginAntiConcentrationConstant*(q-p) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hls
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  have hll' : μ.real (⋃ n, nativeFirstMarginLowerLargeEvent Z E B p q n) ≤
      4*(q-p)/(gaussianReal 0 1).real (Iio (-(B+1))) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hll
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  have hsplit := measureReal_union_le (μ := μ)
    ((⋃ n, nativeFirstMarginUpperSmallEvent Z E B p q n) ∪
      (⋃ n, nativeFirstMarginUpperLargeEvent Z E B p q n))
    ((⋃ n, nativeFirstMarginLowerSmallEvent Z E B p q n) ∪
      (⋃ n, nativeFirstMarginLowerLargeEvent Z E B p q n))
  have hup := measureReal_union_le (μ := μ)
    (⋃ n, nativeFirstMarginUpperSmallEvent Z E B p q n)
    (⋃ n, nativeFirstMarginUpperLargeEvent Z E B p q n)
  have hlo := measureReal_union_le (μ := μ)
    (⋃ n, nativeFirstMarginLowerSmallEvent Z E B p q n)
    (⋃ n, nativeFirstMarginLowerLargeEvent Z E B p q n)
  have hfinal : μ.real {ω | nativeFirstMargin Z E ω ∈ Icc p q} ≤
      (marginAntiConcentrationConstant*(q-p)+4*(q-p)/(gaussianReal 0 1).real (Ioi (B+1)))+
        (2*marginAntiConcentrationConstant*(q-p)+
          4*(q-p)/(gaussianReal 0 1).real (Iio (-(B+1)))) := by
    refine hcov.trans (hsplit.trans (add_le_add (hup.trans (add_le_add hus' hul'))
      (hlo.trans (add_le_add hls' hll'))))
  refine hfinal.trans ?_
  dsimp [nativeFirstMarginConcentrationConstant]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  ring_nf
  nlinarith [hqp, hβ1, hβ2]

/-- The form used in the paper: the actual first margin has no atom near zero. -/
theorem measureReal_nativeFirstMargin_abs_le
    (hZ : ∀ j, Measurable (Z j)) (hi : iIndepFun Z μ)
    (hG : ∀ j, μ.map (Z j) = gaussianReal 0 1) {E B δ : ℝ} (hE : 1 ≤ 2*E) (hδ : 0 ≤ δ)
    (hδB : δ ≤ B) :
    μ.real {ω | |nativeFirstMargin Z E ω| ≤ δ} ≤
      nativeFirstMarginConcentrationConstant B*(2*δ) := by
  have hB : 0 ≤ B := le_trans hδ hδB
  have hset : {ω | |nativeFirstMargin Z E ω| ≤ δ} =
      {ω | nativeFirstMargin Z E ω ∈ Icc (-δ) δ} := by
    ext ω
    simp only [mem_ofPred_eq, mem_Icc, abs_le]
  rw [hset]
  have h := measureReal_nativeFirstMargin_mem_Icc_le hZ hi hG hE hB
    (by linarith : -δ ≤ δ) (by linarith : -B ≤ -δ)
  refine h.trans ?_
  have := nativeFirstMarginConcentrationConstant_nonneg hB
  nlinarith

end SwingRepair
