import PLAStochastic.Swing.FirstSegment.MarginAntiConcentration
import PLAStochastic.Swing.Restart.Chain.ClockFiniteness
import PLAStochastic.Swing.Restart.Chain.MarkovLaw
import PLAStochastic.ForMathlib.Probability.Process.IIDRestart.FutureSequence

/-! # Gaussian output margins after an arbitrary carried sample

The first sample is retained as observed state. Only the subsequent fresh
increments receive Gaussian laws. The four charging layers and the cone proxy
geometry are the existing actual-segment constructions.
-/
noncomputable section
open Classical
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Z : ℕ → Ω → ℝ}

/-- Two fresh coordinates are independent of their genuine past. Only their
own two laws need to be Gaussian; earlier coordinates can have arbitrary laws. -/
theorem segment_two_fresh_gaussians_of_history {α : Type*} [MeasurableSpace α]
    (hZ : ∀ j, Measurable (Z j)) (hi : iIndepFun Z μ) (n : ℕ)
    (hGn : μ.map (Z n) = gaussianReal 0 1)
    (hGn1 : μ.map (Z (n+1)) = gaussianReal 0 1)
    {X : Ω → α} (hX : Measurable[incrementIndexSpace Z (Iio n)] X) :
    IndepFun X (fun ω => (Z n ω,Z (n+1) ω)) μ ∧
      μ.map (fun ω => (Z n ω,Z (n+1) ω)) = (gaussianReal 0 1).prod (gaussianReal 0 1) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hdis : Disjoint (Iio n) (Ici n) := by
    apply Set.disjoint_left.mpr
    intro j hj hj'
    change j < n at hj
    change n ≤ j at hj'
    omega
  have hspaces := indep_iSup_of_disjoint (fun j => (hZ j).comap_le) hi.iIndep hdis
  have hfuture : Measurable[incrementIndexSpace Z (Ici n)] (fun ω => (Z n ω,Z (n+1) ω)) :=
    (incrementIndexSpace_eval (X := Z) (show n ∈ Set.Ici n from Set.mem_Ici.mpr le_rfl)).prodMk
      (incrementIndexSpace_eval (X := Z) (show n+1 ∈ Set.Ici n from Set.mem_Ici.mpr (by omega)))
  have hind : IndepFun X (fun ω => (Z n ω,Z (n+1) ω)) μ :=
    indep_of_indep_of_le_right (indep_of_indep_of_le_left hspaces hX.comap_le) hfuture.comap_le
  refine ⟨hind,?_⟩
  have hp := IndepFun.map_prod_eq_prod_map_map (hZ n).aemeasurable (hZ (n+1)).aemeasurable
    (hi.indepFun (show n ≠ n+1 by omega))
  simpa only [hGn, hGn1] using hp

theorem measure_segmentMarginUpperSmall_union_le
    (hZ : ∀ j, Measurable (Z j)) (hi : iIndepFun Z μ)
    (hG : ∀ j, 1 ≤ j → μ.map (Z j) = gaussianReal 0 1) (E B : ℝ) {p q : ℝ} (hpq : p ≤ q) :
    μ (⋃ n, nativeFirstMarginUpperSmallEvent Z E B p q n) ≤
      ENNReal.ofReal (marginAntiConcentrationConstant*(q-p)) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  apply measure_iUnion_le_of_disjoint_charging (measurableSet_nativeFirstUpperRejectionEvent hZ E)
    (nativeFirstUpperRejectionEvent_disjoint Z E)
  intro n
  have hind := (segment_two_fresh_gaussians_of_history hZ hi (n+1)
    (hG (n+1) (by omega)) (hG (n+2) (by omega))
    (measurable_nativeFirstMarginState_history Z E n)).1
  have hind' := hind.comp measurable_id measurable_fst
  have hc := independent_gaussian_margin_one_step_charge
    (measurable_nativeFirstMarginState hZ E n) (hZ (n+1))
    (by simpa only [Function.comp_def, id_eq] using hind') (hG (n+1) (by omega))
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


theorem measure_segmentMarginUpperLarge_union_le
    (hZ : ∀ j, Measurable (Z j)) (hi : iIndepFun Z μ)
    (hG : ∀ j, 1 ≤ j → μ.map (Z j) = gaussianReal 0 1) {E B : ℝ} (hE : 1 ≤ 2*E) (hB : 0 ≤ B)
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
  have hpair := segment_two_fresh_gaussians_of_history hZ hi (n+1)
    (hG (n+1) (by omega)) (hG (n+2) (by omega))
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


theorem measure_segmentMarginLowerSmall_union_le
    (hZ : ∀ j, Measurable (Z j)) (hi : iIndepFun Z μ)
    (hG : ∀ j, 1 ≤ j → μ.map (Z j) = gaussianReal 0 1) (E B : ℝ) {p q : ℝ} (hpq : p ≤ q) :
    μ (⋃ n, nativeFirstMarginLowerSmallEvent Z E B p q n) ≤
      ENNReal.ofReal (2*marginAntiConcentrationConstant*(q-p)) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hcoef : (0 : ℝ) ≤ 2*marginAntiConcentrationConstant*(q-p) := by
    nlinarith [marginAntiConcentrationConstant_pos, sub_nonneg.mpr hpq]
  apply measure_iUnion_le_of_disjoint_charging (measurableSet_nativeFirstLowerRejectionEvent hZ E)
    (nativeFirstLowerRejectionEvent_disjoint Z E)
  intro n
  have hind := (segment_two_fresh_gaussians_of_history hZ hi (n+1)
    (hG (n+1) (by omega)) (hG (n+2) (by omega))
    (measurable_nativeFirstMarginStateLower_history Z E n)).1
  have hind' := hind.comp measurable_id measurable_fst
  have hc := independent_gaussian_margin_one_step_charge_below
    (measurable_nativeFirstMarginStateLower hZ E n) (hZ (n+1))
    (by simpa only [Function.comp_def, id_eq] using hind') (hG (n+1) (by omega))
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


theorem measure_segmentMarginLowerLarge_union_le
    (hZ : ∀ j, Measurable (Z j)) (hi : iIndepFun Z μ)
    (hG : ∀ j, 1 ≤ j → μ.map (Z j) = gaussianReal 0 1) {E B : ℝ} (hE : 1 ≤ 2*E) (hB : 0 ≤ B)
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
  have hpair := segment_two_fresh_gaussians_of_history hZ hi (n+1)
    (hG (n+1) (by omega)) (hG (n+2) (by omega))
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


omit [MeasurableSpace Ω] in
/-- Finite actual restart geometry covers all output-margin targets; the
already carried observation is arbitrary. -/
theorem nativeSegmentMargin_mem_Icc_cover_of_finite
    (Z : ℕ → Ω → ℝ) {E B p q : ℝ} (hE : 0 ≤ E) (hB : 0 ≤ B)
    (hpB : -B ≤ p) (ω : Ω)
    (hfin : nativeRestartLength (fun k => Z (1+k)) E (Z 0 ω) ω ≠ ⊤)
    (hmargin : nativeFirstMargin Z E ω ∈ Icc p q) :
      ω ∈ (((⋃ n, nativeFirstMarginUpperSmallEvent Z E B p q n) ∪
        (⋃ n, nativeFirstMarginUpperLargeEvent Z E B p q n)) ∪
        ((⋃ n, nativeFirstMarginLowerSmallEvent Z E B p q n) ∪
          (⋃ n, nativeFirstMarginLowerLargeEvent Z E B p q n)) : Set Ω) := by
  set Y : ℕ → Ω → ℝ := fun k => Z (1+k) with hY
  have hNpos := nativeRestartLengthNat_pos_of_finite Y hE (Z 0 ω) ω hfin
  obtain ⟨n, hNat⟩ : ∃ n, nativeRestartLengthNat Y E (Z 0 ω) ω = n+1 :=
    ⟨nativeRestartLengthNat Y E (Z 0 ω) ω-1, by omega⟩
  have hlen : nativeRestartLength Y E (Z 0 ω) ω = ((n+1 : ℕ) : WithTop ℕ) := by
    rw [← nativeRestartLengthNat_cast_of_finite Y E (Z 0 ω) ω hfin, hNat]
  have hfeas : ∀ k, nativePrefixFeasible (fun i => (i : ℝ))
      (fun i => cumulativeSamples Z i ω) E 0 k 0 ↔
        (k : WithTop ℕ) ≤ nativeRestartLength Y E (Z 0 ω) ω := by
    intro k
    simpa [cumulativeSamples, Y] using nativeRestart_feasible_iff Z 0 k E 0 ω
  have hfitz := (hfeas (n+1)).mpr (by rw [hlen])
  have hrejz : ¬ nativePrefixFeasible (fun j => (j : ℝ))
      (fun j => cumulativeSamples Z j ω) E 0 (n+2) 0 := by
    intro hh
    have hbad := (hfeas (n+2)).mp hh
    rw [hlen] at hbad
    have : n+2 ≤ n+1 := WithTop.coe_le_coe.mp hbad
    omega
  have hfit0 : nativePrefixFeasible (fun j => (j : ℝ))
      (fun j => cumulativeSamples Z j ω) E 0 (n+1) (cumulativeSamples Z 0 ω) := by
    simpa only [cumulativeSamples_zero] using hfitz
  have hrej0 : ¬ nativePrefixFeasible (fun j => (j : ℝ))
      (fun j => cumulativeSamples Z j ω) E 0 (n+2) (cumulativeSamples Z 0 ω) := by
    simpa only [cumulativeSamples_zero] using hrejz
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


theorem measureReal_nativeSegmentMargin_mem_Icc_le
    (hZ : ∀ j, Measurable (Z j)) (hi : iIndepFun Z μ)
    (hG : ∀ j, 1 ≤ j → μ.map (Z j) = gaussianReal 0 1) {E B p q : ℝ} (hE : 1 ≤ 2*E) (hB : 0 ≤ B)
    (hpq : p ≤ q) (hpB : -B ≤ p)
    (hfin : ∀ᵐ ω ∂μ, nativeRestartLength (fun k => Z (1+k)) E (Z 0 ω) ω ≠ ⊤) :
    μ.real {ω | nativeFirstMargin Z E ω ∈ Icc p q} ≤
      nativeFirstMarginConcentrationConstant B*(q-p) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hE0 : 0 ≤ E := by linarith
  have hqp : 0 ≤ q-p := sub_nonneg.mpr hpq
  have hβ1 : 0 < (gaussianReal 0 1).real (Ioi (B+1)) := gaussianReal_Ioi_real_pos (by linarith)
  have hβ2 : 0 < (gaussianReal 0 1).real (Iio (-(B+1))) := gaussianReal_Iio_real_pos (by linarith)
  have hC0 := marginAntiConcentrationConstant_pos
  have hcov := ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono_ae (hfin.mono (fun ω hω =>
      nativeSegmentMargin_mem_Icc_cover_of_finite Z hE0 hB hpB (q := q) ω hω)))
  have hus := measure_segmentMarginUpperSmall_union_le hZ hi hG E B hpq
  have hul := measure_segmentMarginUpperLarge_union_le hZ hi hG hE hB hpq
  have hls := measure_segmentMarginLowerSmall_union_le hZ hi hG E B hpq
  have hll := measure_segmentMarginLowerLarge_union_le hZ hi hG hE hB hpq
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


/-- The genuine output margin after every fixed carried value has one common
anti-concentration bound. No law is assigned to the carried value. -/
theorem measureReal_nativeRestartMargin_mem_Icc_le
    {X : ℕ → Ω → ℝ} (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E B p q : ℝ}
    (hE : 1 ≤ 2*E) (hB : 0 ≤ B) (hpq : p ≤ q) (hpB : -B ≤ p) (x : ℝ) :
    μ.real {ω | E-|nativeRestartNext X E x ω| ∈ Icc p q} ≤
      nativeFirstMarginConcentrationConstant B*(q-p) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  let Z : ℕ → Ω → ℝ := fun n ω => if n = 0 then x else X n ω
  have hZm : ∀ n, Measurable (Z n) := by
    intro n
    dsimp only [Z]
    split_ifs <;> fun_prop
  have hZi : iIndepFun Z μ := by
    exact hi.comp (fun n z => if n = 0 then x else z) (fun n => by
      split_ifs <;> fun_prop)
  have hZg : ∀ n, 1 ≤ n → μ.map (Z n) = gaussianReal 0 1 := by
    intro n hn
    simpa only [Z, if_neg (by omega : n ≠ 0)] using hG n
  have htail : (fun k => Z (1+k)) = (fun k => X (1+k)) := by
    funext k ω
    simp [Z]
  have hZ0 : Z 0 = fun _ => x := by funext ω; simp [Z]
  have hfin : ∀ᵐ ω ∂μ, nativeRestartLength (fun k => Z (1+k)) E (Z 0 ω) ω ≠ ⊤ := by
    rw [htail, hZ0]
    exact nativeRestartLength_ae_finite (fun j => hX (1+j))
      (hi.precomp (g := fun j => 1+j) (by intro i j hij; dsimp at hij; omega))
      (fun j => hG (1+j)) (by linarith) x
  have hbase := measureReal_nativeSegmentMargin_mem_Icc_le hZm hZi hZg
    hE hB hpq hpB hfin
  have hshift : μ.real {ω | E-|nativeRestartNext (fun k => X (1+k)) E x ω| ∈ Icc p q} ≤
      nativeFirstMarginConcentrationConstant B*(q-p) := by
    simpa only [nativeFirstMargin, nativeFirstNext, htail, hZ0] using hbase
  have hid : ∀ n, IdentDistrib (X n) (X 0) μ μ := fun n =>
    ⟨(hX n).aemeasurable, (hX 0).aemeasurable, (hG n).trans (hG 0).symm⟩
  have hseq := futureSequence_identDistrib hX hi hid 0
  have hnext : Measurable (fun z : ℕ → ℝ => E-|nativeRestartNext nativeIncrementCoordinates E x z|) :=
    measurable_const.sub (((nativeRestartNext_measurable nativeIncrementCoordinates
      nativeIncrementCoordinates_measurable E).comp
        ((measurable_const (a := x)).prodMk measurable_id)).abs)
  have heq := (hseq.comp hnext).measure_mem_eq (measurableSet_Icc (a := p) (b := q))
  have heqR := congrArg ENNReal.toReal heq
  change μ.real {ω | E-|nativeRestartNext (fun k => X (1+k)) E x ω| ∈ Icc p q} =
    μ.real {ω | E-|nativeRestartNext X E x ω| ∈ Icc p q} at heqR
  rw [← heqR]
  exact hshift

/-- Lemma H.2 for a genuine constrained-SSE segment initialized by any state
measurable in the complete stopped history. The entire unused sequence is
independent of that history by the proved stopped-iid theorem. -/
theorem condExp_nativeRestartMargin_mem_Icc_le
    {X : ℕ → Ω → ℝ} (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1)
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime (incrementFiltration X hX) τ)
    (hfinite : ∀ᵐ ω ∂μ, τ ω ≠ ⊤)
    {S : Ω → ℝ} (hS : Measurable[hτ.measurableSpace] S)
    {E B p q : ℝ} (hE : 1 ≤ 2*E) (hB : 0 ≤ B) (hpq : p ≤ q) (hpB : -B ≤ p) :
    ∀ᵐ ω ∂μ,
      μ[(fun η => if E-|nativeRestartNext nativeIncrementCoordinates E (S η)
        (fun j => X ((τ η).untopD 0+1+j) η)| ∈ Icc p q then (1 : ℝ) else 0) |
        hτ.measurableSpace] ω ≤ nativeFirstMarginConcentrationConstant B*(q-p) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  let Y : Ω → (ℕ → ℝ) := fun ω j => X ((τ ω).untopD 0+1+j) ω
  let F : Ω × (ℕ → ℝ) → ℝ := fun p' =>
    if E-|nativeRestartNext nativeIncrementCoordinates E (S p'.1) p'.2| ∈ Icc p q
      then 1 else 0
  have hid : ∀ n, IdentDistrib (X n) (X 0) μ μ := fun n =>
    ⟨(hX n).aemeasurable, (hX 0).aemeasurable, (hG n).trans (hG 0).symm⟩
  have hY : Measurable Y := stoppedSequence_measurable hX hτ
  have hind : Indep (MeasurableSpace.comap Y inferInstance) hτ.measurableSpace μ :=
    stoppedSequence_indep_stopped hX hi hid hτ hfinite
  have hF : @Measurable _ _ (hτ.measurableSpace.prod inferInstance) _ F := by
    let : MeasurableSpace Ω := hτ.measurableSpace
    have hnext := (nativeRestartNext_measurable nativeIncrementCoordinates
      nativeIncrementCoordinates_measurable E).comp ((hS.comp measurable_fst).prodMk measurable_snd)
    exact measurable_const.ite (measurableSet_Icc.preimage (measurable_const.sub hnext.abs))
      measurable_const
  have hb : ∀ p', |F p'| ≤ 1 := by
    intro p'
    dsimp only [F]
    split_ifs <;> norm_num
  have hc := condExp_history_independent_integral hτ.measurableSpace_le hY.aemeasurable
    hind hF (by norm_num : (0 : ℝ) ≤ 1) hb
  have hlaw : μ.map Y = μ.map (fun ω j => X j ω) :=
    (stoppedSequence_identDistrib hX hi hid hτ hfinite).map_eq
  filter_upwards [hc] with ω hω
  change μ[(fun η => F (η,Y η)) | hτ.measurableSpace] ω ≤ _
  rw [hω, hlaw]
  rw [integral_map (f := fun y => F (ω,y)) (measurable_pi_lambda _ hX).aemeasurable
    (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable]
  have hnext := (nativeRestartNext_measurable X hX E).comp
    ((measurable_const (a := S ω)).prodMk measurable_id)
  have hA : MeasurableSet {η | E-|nativeRestartNext X E (S ω) η| ∈ Icc p q} :=
    measurableSet_Icc.preimage (measurable_const.sub hnext.abs)
  change (∫ η, if η ∈ {η | E-|nativeRestartNext X E (S ω) η| ∈ Icc p q}
    then (1 : ℝ) else 0 ∂μ) ≤ _
  rw [integral_if_one_eq_measureReal hA]
  exact measureReal_nativeRestartMargin_mem_Icc_le hX hi hG hE hB hpq hpB (S ω)

/-- The conditional H.2 bound at every actual native recording. The stopping
time, its finiteness and the state measurability are all discharged here. -/
theorem condExp_nativeRecordingMargin_mem_Icc_le
    {X : ℕ → Ω → ℝ} (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E B p q : ℝ}
    (hE : 1 ≤ 2*E) (hB : 0 ≤ B) (hpq : p ≤ q) (hpB : -B ≤ p) (k : ℕ) :
    ∀ᵐ ω ∂μ,
      μ[(fun η => if E-|nativeRestartRecordingState X E (k+1) η| ∈ Icc p q
        then (1 : ℝ) else 0) |
        (nativeRecordingTime_isStoppingTime_increment X hX E k).measurableSpace] ω ≤
          nativeFirstMarginConcentrationConstant B*(q-p) := by
  have hEpos : 0 < E := by linarith
  have hc := condExp_nativeRestartMargin_mem_Icc_le hX hi hG
    (nativeRecordingTime_isStoppingTime_increment X hX E k)
    ((nativeRecordingTime_ae_all_finite hX hi hG hEpos).mono (fun _ h => h k))
    (nativeRestartRecordingState_measurable_stopped hX E k) hE hB hpq hpB
  have hfg : (fun η => if E-|nativeRestartRecordingState X E (k+1) η| ∈ Icc p q
      then (1 : ℝ) else 0) =ᵐ[μ]
      (fun η => if E-|nativeRestartNext nativeIncrementCoordinates E
        (nativeRestartRecordingState X E k η)
        (fun j => X ((nativeRecordingTime (fun j => (j : ℝ)) (cumulativeSamples X) E k η).untopD 0+1+j) η)|
          ∈ Icc p q then (1 : ℝ) else 0) := by
    filter_upwards [nativeRestartRecordingState_succ_ae hX hi hG hEpos k] with ω hω
    rw [hω]
  have he := condExp_congr_ae
    (m := (nativeRecordingTime_isStoppingTime_increment X hX E k).measurableSpace) hfg
  filter_upwards [he, hc] with ω hω hbound
  rw [hω]
  exact hbound

end SwingRepair
