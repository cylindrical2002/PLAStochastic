import PLAStochastic.Swing.FirstSegment.ExponentialCharging
import PLAStochastic.Swing.FirstSegment.ConeEnvelope

/-! # Exponential tails of the actual first selected rejection increment -/
noncomputable section
open Classical
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- A Gaussian tail ratio on the entire small-threshold layer, including
negative thresholds. -/
theorem gaussianReal_small_threshold_tail {t r : ℝ} (ht : 0 ≤ t) (hr : r ≤ t/2) :
    gaussianReal 0 1 (Ioi t) ≤ ENNReal.ofReal (Real.exp (-t^2/8))*gaussianReal 0 1 (Ioi r) := by
  have hs := gaussianReal_Ioi_shift_le (r := t/2) (u := t/2) (by positivity) (by positivity)
  have he : t/2+t/2 = t := by ring
  have he' : -(t/2)^2/2 = -t^2/8 := by ring
  rw [he,he'] at hs
  exact hs.trans (mul_le_mul_right (measure_mono (fun _ hx => hr.trans_lt hx)) _)

/-- Local charging of a large next increment against the actual rejection
at a past-selected threshold. -/
theorem independent_gaussian_small_threshold_charge {Ω α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → α} {Z : Ω → ℝ} (hX : Measurable X) (hZ : Measurable Z)
    (hi : IndepFun X Z μ) (hlaw : μ.map Z = gaussianReal 0 1)
    {U : Set α} (hU : MeasurableSet U) {r : α → ℝ} (hr : Measurable r)
    {t : ℝ} (ht : 0 ≤ t) (hsmall : ∀ x ∈ U, r x ≤ t/2) :
    μ.real {ω | X ω ∈ U ∧ t < Z ω} ≤
      Real.exp (-t^2/8)*μ.real {ω | X ω ∈ U ∧ r (X ω) < Z ω} := by
  let F (p : α × ℝ) : ℝ := if t < p.2 then 1 else 0
  let G (p : α × ℝ) : ℝ := if r p.1 < p.2 then 1 else 0
  have hFm : Measurable F := measurable_const.ite (measurableSet_lt measurable_const measurable_snd) measurable_const
  have hGm : Measurable G := measurable_const.ite (measurableSet_lt (hr.comp measurable_fst) measurable_snd) measurable_const
  have hbF : ∀ p, |F p| ≤ 1 := by intro p; dsimp [F]; split_ifs <;> norm_num
  have hbG : ∀ p, |G p| ≤ 1 := by intro p; dsimp [G]; split_ifs <;> norm_num
  have hs : ∀ x ∈ U, (∫ z, F (x,z) ∂μ.map Z) ≤
      Real.exp (-t^2/8)*(∫ z, G (x,z) ∂μ.map Z)+0 := by
    intro x hx
    rw [hlaw]
    have hFv : (∫ z, F (x,z) ∂gaussianReal 0 1) = (gaussianReal 0 1).real (Ioi t) :=
      integral_if_one_eq_measureReal measurableSet_Ioi
    have hGv : (∫ z, G (x,z) ∂gaussianReal 0 1) = (gaussianReal 0 1).real (Ioi (r x)) :=
      integral_if_one_eq_measureReal (A := Ioi (r x)) measurableSet_Ioi
    rw [hFv,hGv,add_zero]
    have hm := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
      (gaussianReal_small_threshold_tail ht (hsmall x hx))
    simpa only [Measure.real,ENNReal.toReal_mul,ENNReal.toReal_ofReal (Real.exp_nonneg _)] using hm
  have hc := IndepFun.integral_state_guard_le hX.aemeasurable hZ.aemeasurable hi hU hFm hGm
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1) hbF hbG hs
  have hA : MeasurableSet {ω | X ω ∈ U ∧ t < Z ω} :=
    (hU.preimage hX).inter (measurableSet_lt measurable_const hZ)
  have hB : MeasurableSet {ω | X ω ∈ U ∧ r (X ω) < Z ω} :=
    (hU.preimage hX).inter (measurableSet_lt (hr.comp hX) hZ)
  have hFi : (∫ ω, if X ω ∈ U then F (X ω,Z ω) else 0 ∂μ) = μ.real {ω | X ω ∈ U ∧ t < Z ω} := by
    have he : (fun ω => if X ω ∈ U then F (X ω,Z ω) else 0) =
        fun ω => if ω ∈ {ω | X ω ∈ U ∧ t < Z ω} then (1 : ℝ) else 0 := by
      funext ω; dsimp [F]; split_ifs <;> tauto
    exact (congrArg (fun f : Ω → ℝ => ∫ ω, f ω ∂μ) he).trans (integral_if_one_eq_measureReal hA)
  have hGi : (∫ ω, if X ω ∈ U then G (X ω,Z ω) else 0 ∂μ) = μ.real {ω | X ω ∈ U ∧ r (X ω) < Z ω} := by
    have he : (fun ω => if X ω ∈ U then G (X ω,Z ω) else 0) =
        fun ω => if ω ∈ {ω | X ω ∈ U ∧ r (X ω) < Z ω} then (1 : ℝ) else 0 := by
      funext ω; dsimp [G]; split_ifs <;> tauto
    exact (congrArg (fun f : Ω → ℝ => ∫ ω, f ω ∂μ) he).trans (integral_if_one_eq_measureReal hB)
  rwa [hFi,hGi,zero_mul,add_zero] at hc

def nativeFirstUpperRejectionEvent {Ω : Type*} (Z : ℕ → Ω → ℝ) (E : ℝ) (n : ℕ) : Set Ω :=
  {ω | (nativeFirstPrefixState (cumulativeSamples Z) E n ω).2.2 = true ∧
    (nativeFirstPrefixState (cumulativeSamples Z) E n ω).2.1 < Z (n+1) ω}

theorem nativeFirstUpperRejectionEvent_recording {Ω : Type*} (Z : ℕ → Ω → ℝ)
    (E : ℝ) (n : ℕ) {ω : Ω} (hω : ω ∈ nativeFirstUpperRejectionEvent Z E n) :
    nativeFirstDuration Z E ω = n+1 := by
  rcases hω with ⟨hg,hz⟩
  dsimp only [nativeFirstPrefixState] at hg hz
  have hfit : nativePrefixFeasible (fun j => (j : ℝ)) (fun j => cumulativeSamples Z j ω)
      E 0 (n+1) (cumulativeSamples Z 0 ω) := by
    by_contra hn
    simp only [if_neg hn, Bool.false_eq_true] at hg
  have hs := native_first_upper_endpoint_spec (fun j => cumulativeSamples Z j ω) E (by omega : 1 ≤ n+1) hfit
  have hr : ¬ nativePrefixFeasible (fun j => (j : ℝ)) (fun j => cumulativeSamples Z j ω)
      E 0 (n+2) (cumulativeSamples Z 0 ω) := by
    rintro ⟨m,hm⟩
    have hmold : feasibleSlope (Finset.Icc 1 (n+1)) (fun j => (j : ℝ))
        (fun j => cumulativeSamples Z j ω) 0 (cumulativeSamples Z 0 ω) E m := by
      intro j hj
      have hj' := Finset.mem_Icc.mp hj
      simpa only [Nat.cast_zero] using! hm j (Finset.mem_Icc.mpr ⟨hj'.1,by omega⟩)
    have hmu := hs.2 m hmold
    have hend := hm (n+2) (Finset.mem_Icc.mpr ⟨by omega,le_rfl⟩)
    simp only [Nat.cast_zero,sub_zero] at hend
    have hb := (abs_le.mp hend).2
    have hstep : cumulativeSamples Z (n+2) ω = cumulativeSamples Z (n+1) ω+Z (n+1) ω := by
      simpa only [Nat.add_assoc] using cumulativeSamples_succ Z (n+1) ω
    rw [hstep] at hb
    have hmul := mul_le_mul_of_nonneg_left hmu (show (0 : ℝ) ≤ ((n+2 : ℕ) : ℝ) by positivity)
    nlinarith
  have hthreshold : ∀ j, nativePrefixFeasible (fun j => (j : ℝ)) (fun j => cumulativeSamples Z j ω)
      E 0 j (cumulativeSamples Z 0 ω) ↔ j < n+2 := by
    intro j
    exact ⟨fun hj => by
      by_contra hnj
      exact hr (nativePrefixFeasible_mono_end hj (by omega)),
      fun hj => nativePrefixFeasible_mono_end hfit (by omega)⟩
  simpa only [nativeFirstDuration,show n+2-1 = n+1 by omega] using
    nativeFirstRecording_eq_threshold (fun j => (j : ℝ)) (fun j => cumulativeSamples Z j ω) E
      (by omega : 1 < n+2) hthreshold

theorem nativeFirstUpperRejectionEvent_disjoint {Ω : Type*} (Z : ℕ → Ω → ℝ) (E : ℝ) :
    Pairwise (fun n m => Disjoint (nativeFirstUpperRejectionEvent Z E n) (nativeFirstUpperRejectionEvent Z E m)) := by
  intro n m hnm
  apply Set.disjoint_left.mpr
  intro ω hn hm
  have h₁ := nativeFirstUpperRejectionEvent_recording Z E n hn
  have h₂ := nativeFirstUpperRejectionEvent_recording Z E m hm
  exact hnm (by omega)

theorem measurable_nativeFirstPrefixState {Ω : Type*} [MeasurableSpace Ω]
    {Z : ℕ → Ω → ℝ} (hZ : ∀ j, Measurable (Z j)) (E : ℝ) (n : ℕ) :
    Measurable (nativeFirstPrefixState (cumulativeSamples Z) E n) :=
  (measurable_nativeFirstPrefixState_history Z E n).mono (incrementIndexSpace_le hZ _) le_rfl

theorem measurableSet_nativeFirstUpperRejectionEvent {Ω : Type*} [MeasurableSpace Ω]
    {Z : ℕ → Ω → ℝ} (hZ : ∀ j, Measurable (Z j)) (E : ℝ) (n : ℕ) :
    MeasurableSet (nativeFirstUpperRejectionEvent Z E n) :=
  (measurableSet_eq_fun (measurable_nativeFirstPrefixState hZ E n).snd.snd measurable_const).inter
    (measurableSet_lt (measurable_nativeFirstPrefixState hZ E n).snd.fst (hZ (n+1)))

def nativeFirstSmallThresholdEvent {Ω : Type*} (Z : ℕ → Ω → ℝ) (E t : ℝ) (n : ℕ) : Set Ω :=
  {ω | (nativeFirstPrefixState (cumulativeSamples Z) E n ω).2.2 = true ∧
    (nativeFirstPrefixState (cumulativeSamples Z) E n ω).2.1 ≤ t/2 ∧ t < Z (n+1) ω}

/-- The small-threshold part is summed over disjoint actual first rejections. -/
theorem measure_nativeFirstSmallThreshold_union_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {Z : ℕ → Ω → ℝ} (hZ : ∀ j, Measurable (Z j)) (hi : iIndepFun Z μ)
    (hG : ∀ j, μ.map (Z j) = gaussianReal 0 1) (E : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    μ (⋃ n, nativeFirstSmallThresholdEvent Z E t n) ≤ ENNReal.ofReal (Real.exp (-t^2/8)) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  apply measure_iUnion_le_of_disjoint_charging (measurableSet_nativeFirstUpperRejectionEvent hZ E)
    (nativeFirstUpperRejectionEvent_disjoint Z E)
  intro n
  let U : Set (ℝ × ℝ × Bool) := {p | p.2.2 = true ∧ p.2.1 ≤ t/2}
  have hU : MeasurableSet U :=
    (measurableSet_eq_fun measurable_snd.snd measurable_const).inter (measurableSet_le measurable_snd.fst measurable_const)
  have hind := (iid_two_fresh_gaussians_of_history hZ hi hG (n+1)
    (measurable_nativeFirstPrefixState_history Z E n)).1
  have hind' := hind.comp measurable_id measurable_fst
  have hc := independent_gaussian_small_threshold_charge (measurable_nativeFirstPrefixState hZ E n)
    (hZ (n+1)) (by simpa only [Function.comp_def,id_eq] using hind') (hG (n+1)) hU
    (r := fun p : ℝ × ℝ × Bool => p.2.1) measurable_snd.fst ht (fun _ hx => hx.2)
  have hs : {ω | nativeFirstPrefixState (cumulativeSamples Z) E n ω ∈ U ∧
      (nativeFirstPrefixState (cumulativeSamples Z) E n ω).2.1 < Z (n+1) ω} ⊆
      nativeFirstUpperRejectionEvent Z E n := fun _ hx => ⟨hx.1.1,hx.2⟩
  have hm := hc.trans (mul_le_mul_of_nonneg_left (measureReal_mono hs) (Real.exp_nonneg _))
  have hsource : {ω | nativeFirstPrefixState (cumulativeSamples Z) E n ω ∈ U ∧ t < Z (n+1) ω} =
      nativeFirstSmallThresholdEvent Z E t n := by ext ω; simp only [U,nativeFirstSmallThresholdEvent,mem_ofPred_eq]; tauto
  rw [hsource] at hm
  have he := ENNReal.ofReal_le_ofReal hm
  rw [ENNReal.ofReal_mul (Real.exp_nonneg _),Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _),
    Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _)] at he
  exact he

/-- Geometric information at an actual upper rejection, including the old
endpoint's feasibility and the threshold inequality r≥u. -/
theorem nativeFirstUpperRejectionEvent_spec {Ω : Type*} (Z : ℕ → Ω → ℝ)
    (E : ℝ) (n : ℕ) {ω : Ω} (hω : ω ∈ nativeFirstUpperRejectionEvent Z E n) :
    let S := nativeFirstPrefixState (cumulativeSamples Z) E n ω
    nativePrefixFeasible (fun j => (j : ℝ)) (fun j => cumulativeSamples Z j ω) E 0 (n+1) 0 ∧
    ¬ nativePrefixFeasible (fun j => (j : ℝ)) (fun j => cumulativeSamples Z j ω) E 0 (n+2) 0 ∧
    feasibleSlope (Finset.Icc 1 (n+1)) (fun j => (j : ℝ)) (fun j => cumulativeSamples Z j ω) 0 0 E S.1 ∧
    S.1 ≤ S.2.1 := by
  rcases hω with ⟨hg,hz⟩
  dsimp only [nativeFirstPrefixState] at hg hz ⊢
  have hfit : nativePrefixFeasible (fun j => (j : ℝ)) (fun j => cumulativeSamples Z j ω)
      E 0 (n+1) (cumulativeSamples Z 0 ω) := by
    by_contra hn
    simp only [if_neg hn, Bool.false_eq_true] at hg
  have hs := native_first_upper_endpoint_spec (fun j => cumulativeSamples Z j ω) E (by omega : 1 ≤ n+1) hfit
  have hr : ¬ nativePrefixFeasible (fun j => (j : ℝ)) (fun j => cumulativeSamples Z j ω)
      E 0 (n+2) (cumulativeSamples Z 0 ω) := by
    rintro ⟨m,hm⟩
    have hmold : feasibleSlope (Finset.Icc 1 (n+1)) (fun j => (j : ℝ))
        (fun j => cumulativeSamples Z j ω) 0 (cumulativeSamples Z 0 ω) E m := by
      intro j hj
      have hj' := Finset.mem_Icc.mp hj
      simpa only [Nat.cast_zero] using! hm j (Finset.mem_Icc.mpr ⟨hj'.1,by omega⟩)
    have hmu := hs.2 m hmold
    have hend := hm (n+2) (Finset.mem_Icc.mpr ⟨by omega,le_rfl⟩)
    simp only [Nat.cast_zero,sub_zero] at hend
    have hb := (abs_le.mp hend).2
    have hstep : cumulativeSamples Z (n+2) ω = cumulativeSamples Z (n+1) ω+Z (n+1) ω := by
      simpa only [Nat.add_assoc] using cumulativeSamples_succ Z (n+1) ω
    rw [hstep] at hb
    have hmul := mul_le_mul_of_nonneg_left hmu (show (0 : ℝ) ≤ ((n+2 : ℕ) : ℝ) by positivity)
    nlinarith
  refine ⟨by simpa only [cumulativeSamples_zero] using hfit,
    by simpa only [cumulativeSamples_zero] using hr,
    by simpa only [cumulativeSamples_zero] using hs.1,?_⟩
  have hend := hs.1 (n+1) (Finset.mem_Icc.mpr ⟨by omega,le_rfl⟩)
  simp only [sub_zero] at hend
  have hb := (abs_le.mp hend).2
  push_cast at hb ⊢
  linarith

def nativeFirstUpperPositiveEvent {Ω : Type*} (Z : ℕ → Ω → ℝ) (E t : ℝ) : Set Ω :=
  ⋃ n, nativeFirstUpperRejectionEvent Z E n ∩ {ω | t < Z (n+1) ω}

/-- The difficult and easy threshold layers plus one common Gaussian endpoint
envelope cover every positive large upper-rejection increment. -/
theorem nativeFirstUpperPositiveEvent_cover_ae {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {Z : ℕ → Ω → ℝ} (hZ : ∀ j, Measurable (Z j)) (hi : iIndepFun Z μ)
    (hG : ∀ j, μ.map (Z j) = gaussianReal 0 1) {E : ℝ} (hE : 0 ≤ E) (t : ℝ) :
    ∀ᵐ ω ∂μ, ω ∈ nativeFirstUpperPositiveEvent Z E t →
      ω ∈ ({ω | Real.sqrt t/4 < nativeFirstSlopeEnvelope Z ω} ∪
        (⋃ n, nativeFirstSmallThresholdEvent Z E t n) ∪ (⋃ n, nativeFirstLargeThresholdEvent Z E t n) : Set Ω) := by
  filter_upwards [nativeFirst_feasible_slope_bound_ae hZ hi hG] with ω he
  intro hω
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hω
  rcases hn with ⟨hupper,hz⟩
  have hs := nativeFirstUpperRejectionEvent_spec Z E n hupper
  let S := nativeFirstPrefixState (cumulativeSamples Z) E n ω
  have hS : |S.1| ≤ nativeFirstSlopeEnvelope Z ω := he E hE (n+1) (by omega) hs.1 hs.2.1 _ hs.2.2.1
  by_cases hu : Real.sqrt t/4 < S.1
  · exact Or.inl (Or.inl (hu.trans_le ((le_abs_self _).trans hS)))
  · by_cases hr : S.2.1 ≤ t/2
    · exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨n,hupper.1,hr,hz⟩))
    · exact Or.inr (Set.mem_iUnion.mpr ⟨n,⟨hupper.1,le_of_not_gt hu,lt_of_not_ge hr⟩,hupper.2⟩)

def nativeFirstUpperTailConstant : ℝ := nativeFirstSlopeEnvelopeTailConstant+1+
  gaussianChargingConstant*gaussianChargingCutoffConstant

/-- Upper rejection with a positive selected increment. -/
theorem measureReal_nativeFirstUpperPositiveEvent_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {Z : ℕ → Ω → ℝ} (hZ : ∀ j, Measurable (Z j)) (hi : iIndepFun Z μ)
    (hG : ∀ j, μ.map (Z j) = gaussianReal 0 1) {E : ℝ} (hE : 1 ≤ 2*E)
    {t : ℝ} (ht : 2 < t) :
    μ.real (nativeFirstUpperPositiveEvent Z E t) ≤ nativeFirstUpperTailConstant*Real.exp (-t/25600) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hc := ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono_ae (nativeFirstUpperPositiveEvent_cover_ae hZ hi hG (by linarith : 0 ≤ E) t))
  have hu := (measureReal_union_le (μ := μ)
    ({ω | Real.sqrt t/4 < nativeFirstSlopeEnvelope Z ω} ∪ ⋃ n, nativeFirstSmallThresholdEvent Z E t n)
    (⋃ n, nativeFirstLargeThresholdEvent Z E t n))
  have hu' := measureReal_union_le (μ := μ) {ω | Real.sqrt t/4 < nativeFirstSlopeEnvelope Z ω}
    (⋃ n, nativeFirstSmallThresholdEvent Z E t n)
  have he := nativeFirstSlopeEnvelope_tail_bound hZ hi hG (t := Real.sqrt t/4) (by positivity)
  have hs := ENNReal.toReal_mono ENNReal.ofReal_ne_top (measure_nativeFirstSmallThreshold_union_le hZ hi hG E (by linarith : 0 ≤ t))
  rw [ENNReal.toReal_ofReal (Real.exp_nonneg _)] at hs
  have hl := ENNReal.toReal_mono ENNReal.ofReal_ne_top (measure_nativeFirstLargeThreshold_union_le hZ hi hG hE ht)
  rw [ENNReal.toReal_ofReal (by exact mul_nonneg (mul_nonneg gaussianChargingConstant_pos.le gaussianChargingCutoffConstant_pos.le) (Real.exp_nonneg _))] at hl
  have heq : -(Real.sqrt t/4)^2/1600 = -t/25600 := by rw [div_pow, Real.sq_sqrt (by linarith : 0 ≤ t)]; ring
  rw [heq] at he
  have hs' : Real.exp (-t^2/8) ≤ Real.exp (-t/25600) := Real.exp_le_exp.mpr (by nlinarith)
  have hl' : Real.exp (-t/8) ≤ Real.exp (-t/25600) := Real.exp_le_exp.mpr (by linarith)
  have hp := mul_le_mul_of_nonneg_left hl' (mul_nonneg gaussianChargingConstant_pos.le gaussianChargingCutoffConstant_pos.le)
  change _ ≤ nativeFirstUpperTailConstant*Real.exp (-t/25600)
  dsimp [nativeFirstUpperTailConstant]
  change μ.real (⋃ n, nativeFirstSmallThresholdEvent Z E t n) ≤ _ at hs
  change μ.real (⋃ n, nativeFirstLargeThresholdEvent Z E t n) ≤ _ at hl
  change μ.real (nativeFirstUpperPositiveEvent Z E t) ≤
    μ.real (({ω | Real.sqrt t/4 < nativeFirstSlopeEnvelope Z ω} ∪
      ⋃ n, nativeFirstSmallThresholdEvent Z E t n) ∪
        ⋃ n, nativeFirstLargeThresholdEvent Z E t n) at hc
  have hcov : μ.real (nativeFirstUpperPositiveEvent Z E t) ≤
      μ.real ({ω | Real.sqrt t/4 < nativeFirstSlopeEnvelope Z ω} ∪
        ⋃ n, nativeFirstSmallThresholdEvent Z E t n) +
        μ.real (⋃ n, nativeFirstLargeThresholdEvent Z E t n) := by
    exact hc.trans hu
  have hsmall : μ.real ({ω | Real.sqrt t/4 < nativeFirstSlopeEnvelope Z ω} ∪
      ⋃ n, nativeFirstSmallThresholdEvent Z E t n) ≤
      nativeFirstSlopeEnvelopeTailConstant * Real.exp (-t/25600) +
        Real.exp (-t^2/8) := by
    exact hu'.trans (add_le_add he hs)
  have htotal := hcov.trans (add_le_add hsmall hl)
  have hpow : Real.exp (-t^2/8) ≤ Real.exp (-t/25600) := hs'
  have hlarge : gaussianChargingConstant*gaussianChargingCutoffConstant *
      Real.exp (-t/8) ≤ gaussianChargingConstant*gaussianChargingCutoffConstant *
        Real.exp (-t/25600) := hp
  have hconst : nativeFirstSlopeEnvelopeTailConstant * Real.exp (-t/25600) +
      Real.exp (-t^2/8) + gaussianChargingConstant*gaussianChargingCutoffConstant *
        Real.exp (-t/8) ≤
      (nativeFirstSlopeEnvelopeTailConstant + 1 +
        gaussianChargingConstant*gaussianChargingCutoffConstant) * Real.exp (-t/25600) := by
    nlinarith
  exact htotal.trans (hconst)


/-- The reflected lower-rejection process.  It is definitionally the same
first-recording construction after replacing every fresh increment by its
negative; this isolates the reflection step from the positive charging proof. -/
def nativeFirstLowerPositiveEvent {Ω : Type*} (Z : ℕ → Ω → ℝ) (E t : ℝ) : Set Ω :=
  nativeFirstUpperPositiveEvent (fun n ω => - Z n ω) E t

theorem measureReal_nativeFirstLowerPositiveEvent_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {Z : ℕ → Ω → ℝ} (hZ : ∀ j, Measurable (Z j)) (hi : iIndepFun Z μ)
    (hG : ∀ j, μ.map (Z j) = gaussianReal 0 1) {E : ℝ} (hE : 1 ≤ 2*E)
    {t : ℝ} (ht : 2 < t) :
    μ.real (nativeFirstLowerPositiveEvent Z E t) ≤ nativeFirstUpperTailConstant*Real.exp (-t/25600) := by
  let Zneg : ℕ → Ω → ℝ := fun n ω => - Z n ω
  have hZneg : ∀ n, Measurable (Zneg n) := fun n => (hZ n).neg
  have hineg : iIndepFun Zneg μ := by
    simpa only [Zneg, Function.comp_def] using hi.comp (fun _ x => -x) (fun _ => measurable_neg)
  have hGneg : ∀ n, μ.map (Zneg n) = gaussianReal 0 1 := by
    intro n
    calc
      μ.map (Zneg n) = Measure.map ((fun x : ℝ => -x) ∘ Z n) μ := by rfl
      _ = Measure.map (fun x : ℝ => -x) (μ.map (Z n)) :=
        (Measure.map_map measurable_neg (hZ n)).symm
      _ = Measure.map (fun x : ℝ => -x) (gaussianReal 0 1) := by rw [hG n]
      _ = gaussianReal 0 1 := by rw [gaussianReal_map_neg]; simp
  exact measureReal_nativeFirstUpperPositiveEvent_le hZneg hineg hGneg hE ht

end SwingRepair
