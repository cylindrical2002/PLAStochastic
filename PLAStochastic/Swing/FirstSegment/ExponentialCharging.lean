import PLAStochastic.Swing.FirstSegment.TwoStepCharging

/-! # Exponential charging for actual Gaussian first-rejection prefixes

The state consists of the genuine old cone's upper endpoint, its next upper
rejection threshold, and its actual feasibility flag. It is measurable before
the two prospective increments are observed.
-/
noncomputable section
open Classical
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- Upper endpoint, next rejection threshold, and accepted-prefix flag. -/
def nativeFirstPrefixState {Ω : Type*} (Y : ℕ → Ω → ℝ) (E : ℝ) (n : ℕ) (ω : Ω) :
    ℝ × ℝ × Bool :=
  let u := nativeConeUpper (Finset.Icc 1 (n+1)) (Finset.nonempty_Icc.mpr (by omega))
    (fun j => (j : ℝ)) (fun j => Y j ω) 0 (Y 0 ω) E
  (u, Y 0 ω+((n+2 : ℕ) : ℝ)*u+E-Y (n+1) ω,
    if nativePrefixFeasible (fun j => (j : ℝ)) (fun j => Y j ω) E 0 (n+1) (Y 0 ω) then true else false)

def nativeFirstLargeThresholdGuard (t : ℝ) : Set (ℝ × ℝ × Bool) :=
  {p | p.2.2 = true ∧ p.1 ≤ Real.sqrt t/4 ∧ t/2 < p.2.1}

theorem measurableSet_nativeFirstLargeThresholdGuard (t : ℝ) :
    MeasurableSet (nativeFirstLargeThresholdGuard t) :=
  (measurableSet_eq_fun measurable_snd.snd measurable_const).inter
    ((measurableSet_le measurable_fst measurable_const).inter
      (measurableSet_lt measurable_const measurable_snd.fst))

theorem measurable_nativeFirstPrefixState_history {Ω : Type*} [MeasurableSpace Ω]
    (Z : ℕ → Ω → ℝ) (E : ℝ) (n : ℕ) :
    Measurable[incrementIndexSpace Z (Iio (n+1))] (nativeFirstPrefixState (cumulativeSamples Z) E n) := by
  let : MeasurableSpace Ω := incrementIndexSpace Z (Iio (n+1))
  have hY (j : ℕ) (hj : j ≤ n+1) : Measurable (cumulativeSamples Z j) := by
    apply Finset.measurable_sum
    intro k hk
    exact incrementIndexSpace_eval (X := Z)
      (show k ∈ Set.Iio (n+1) from Set.mem_Iio.mpr (by have := Finset.mem_range.mp hk; omega))
  have hu := measurable_nativeConeUpper (Finset.Icc 1 (n+1)) (Finset.nonempty_Icc.mpr (by omega))
    (fun j => (j : ℝ)) (cumulativeSamples Z) 0 E (hY 0 (by omega))
    (fun j hj => hY j (Finset.mem_Icc.mp hj).2)
  have hr := (((hY 0 (by omega)).add (hu.const_mul ((n+2 : ℕ) : ℝ))).add_const E).sub (hY (n+1) le_rfl)
  have hp := nativePrefixFeasible_measurableSet (fun j => (j : ℝ))
    (fun i j hij => by simpa using! (Nat.cast_lt.mpr hij : (i : ℝ) < (j : ℝ)))
    (cumulativeSamples Z) E 0 (n+1) (by omega) (hY 0 (by omega))
    (fun j hj => hY j (Finset.mem_Icc.mp hj).2)
  exact hu.prodMk (hr.prodMk (measurable_const.ite hp measurable_const))

/-- Upper first-rejection prefixes in the difficult large-threshold layer. -/
def nativeFirstLargeThresholdEvent {Ω : Type*} (Z : ℕ → Ω → ℝ) (E t : ℝ) (n : ℕ) : Set Ω :=
  {ω | nativeFirstPrefixState (cumulativeSamples Z) E n ω ∈ nativeFirstLargeThresholdGuard t ∧
    (nativeFirstPrefixState (cumulativeSamples Z) E n ω).2.1 < Z (n+1) ω}

/-- The rectangular two-increment charging event is contained in the genuine
native proxy event. The second increment enforces the actual next rejection. -/
theorem nativeFirstCharging_rectangle_subset {Ω : Type*} (Z : ℕ → Ω → ℝ) (E t : ℝ) (n : ℕ) :
    {ω | nativeFirstPrefixState (cumulativeSamples Z) E n ω ∈ nativeFirstLargeThresholdGuard t ∧
      Z (n+1) ω ∈ Icc ((nativeFirstPrefixState (cumulativeSamples Z) E n ω).2.1-1)
        ((nativeFirstPrefixState (cumulativeSamples Z) E n ω).2.1-1/2) ∧
      Real.sqrt t/4+1 < Z (n+2) ω} ⊆ nativeFirstUpperProxyEvent (cumulativeSamples Z) E n := by
  intro ω hω
  rcases hω with ⟨hg,hz,hz'⟩
  dsimp only [nativeFirstLargeThresholdGuard, Set.mem_ofPred_eq, nativeFirstPrefixState] at hg hz
  have hfit : nativePrefixFeasible (fun j => (j : ℝ)) (fun j => cumulativeSamples Z j ω)
      E 0 (n+1) (cumulativeSamples Z 0 ω) := by
    by_contra hn
    simp only [if_neg hn, Bool.false_eq_true] at hg
    exact hg.1
  have hu := hg.2.1
  change _ ∈ Icc _ _ at hz
  have hzlo := hz.1
  have hzhi := hz.2
  have hstep1 : cumulativeSamples Z (n+2) ω = cumulativeSamples Z (n+1) ω+Z (n+1) ω := by
    simpa only [Nat.add_assoc] using cumulativeSamples_succ Z (n+1) ω
  have hstep2 : cumulativeSamples Z (n+3) ω = cumulativeSamples Z (n+2) ω+Z (n+2) ω := by
    simpa only [Nat.add_assoc] using cumulativeSamples_succ Z (n+2) ω
  dsimp only [nativeFirstUpperProxyEvent, Set.mem_ofPred_eq]
  simp only [show n+1+1 = n+2 by omega, show n+1+2 = n+3 by omega]
  refine ⟨hfit,?_,?_⟩
  · rw [hstep1]
    constructor <;> linarith
  · rw [hstep2, hstep1]
    linarith

/-- Local exponential charging of the actual difficult prefixes. The only
probabilistic hypotheses are the original measurable iid standard Gaussians. -/
theorem measureReal_nativeFirstLargeThresholdEvent_le_proxy {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} {Z : ℕ → Ω → ℝ}
    (hZ : ∀ j, Measurable (Z j)) (hi : iIndepFun Z μ)
    (hG : ∀ j, μ.map (Z j) = gaussianReal 0 1) (E : ℝ) {t : ℝ} (ht : 2 < t) (n : ℕ) :
    μ.real (nativeFirstLargeThresholdEvent Z E t n) ≤
      (gaussianChargingConstant*gaussianChargingCutoffConstant*Real.exp (-t/8))*
        μ.real (nativeFirstUpperProxyEvent (cumulativeSamples Z) E n) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hc := iid_gaussian_two_step_charge_sqrt_cutoff hZ hi hG (n+1)
    (measurable_nativeFirstPrefixState_history Z E n)
    (measurableSet_nativeFirstLargeThresholdGuard t) (r := fun p : ℝ × ℝ × Bool => p.2.1)
    measurable_snd.fst ht (fun _ hx => hx.2.2)
  apply hc.trans
  apply mul_le_mul_of_nonneg_left _ (by
    exact mul_nonneg (mul_nonneg gaussianChargingConstant_pos.le gaussianChargingCutoffConstant_pos.le)
      (Real.exp_nonneg _))
  exact measureReal_mono (nativeFirstCharging_rectangle_subset Z E t n)

/-- Summing over all actual first-rejection prefixes costs at most one total
proxy probability. In particular there is no factor involving E[J]. -/
theorem measure_nativeFirstLargeThreshold_union_le {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} {Z : ℕ → Ω → ℝ}
    (hZ : ∀ j, Measurable (Z j)) (hi : iIndepFun Z μ)
    (hG : ∀ j, μ.map (Z j) = gaussianReal 0 1) {E : ℝ} (hE : 1 ≤ 2*E)
    {t : ℝ} (ht : 2 < t) :
    μ (⋃ n, nativeFirstLargeThresholdEvent Z E t n) ≤
      ENNReal.ofReal (gaussianChargingConstant*gaussianChargingCutoffConstant*Real.exp (-t/8)) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  apply native_first_upper_proxy_charging (cumulativeSamples Z)
    (fun j => Finset.measurable_sum _ (fun k _ => hZ k)) hE
  intro n
  have hc := ENNReal.ofReal_le_ofReal (measureReal_nativeFirstLargeThresholdEvent_le_proxy hZ hi hG E ht n)
  have hc0 : 0 ≤ gaussianChargingConstant*gaussianChargingCutoffConstant*Real.exp (-t/8) :=
    mul_nonneg (mul_nonneg gaussianChargingConstant_pos.le gaussianChargingCutoffConstant_pos.le)
      (Real.exp_nonneg _)
  rw [ENNReal.ofReal_mul hc0, Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _),
    Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] at hc
  exact hc

/-- Every charged source prefix is itself the actual first native rejection,
so its increment index is the selected index, not a prospective Gaussian. -/
theorem nativeFirstLargeThresholdEvent_recording {Ω : Type*} (Z : ℕ → Ω → ℝ)
    (E t : ℝ) (n : ℕ) {ω : Ω} (hω : ω ∈ nativeFirstLargeThresholdEvent Z E t n) :
    nativeFirstRecording (fun j => (j : ℝ)) (fun j => cumulativeSamples Z j ω) E = n+1 := by
  rcases hω with ⟨hg,hz⟩
  dsimp only [nativeFirstLargeThresholdGuard, Set.mem_ofPred_eq, nativeFirstPrefixState] at hg hz
  have hfit : nativePrefixFeasible (fun j => (j : ℝ)) (fun j => cumulativeSamples Z j ω)
      E 0 (n+1) (cumulativeSamples Z 0 ω) := by
    by_contra hn
    simp only [if_neg hn, Bool.false_eq_true] at hg
    exact hg.1
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
    simp only [Nat.cast_zero, sub_zero] at hend
    have hb := (abs_le.mp hend).2
    have hstep : cumulativeSamples Z (n+2) ω = cumulativeSamples Z (n+1) ω+Z (n+1) ω := by
      simpa only [Nat.add_assoc] using cumulativeSamples_succ Z (n+1) ω
    rw [hstep] at hb
    have hmul := mul_le_mul_of_nonneg_left hmu (show (0 : ℝ) ≤ ((n+2 : ℕ) : ℝ) by positivity)
    nlinarith
  have hthreshold : ∀ j, nativePrefixFeasible (fun j => (j : ℝ)) (fun j => cumulativeSamples Z j ω)
      E 0 j (cumulativeSamples Z 0 ω) ↔ j < n+2 := by
    intro j
    constructor
    · intro hj
      by_contra hnj
      exact hr (nativePrefixFeasible_mono_end hj (by omega))
    · intro hj
      exact nativePrefixFeasible_mono_end hfit (by omega)
  simpa only [show n+2-1 = n+1 by omega] using
    nativeFirstRecording_eq_threshold (fun j => (j : ℝ)) (fun j => cumulativeSamples Z j ω) E
      (by omega : 1 < n+2) hthreshold

/-- The difficult layer at the actual first recording, with its prefix index
retained explicitly rather than erased by a default at absent recordings. -/
def nativeFirstSelectedLargeThresholdEvent {Ω : Type*} (Z : ℕ → Ω → ℝ) (E t : ℝ) : Set Ω :=
  {ω | ∃ n, nativeFirstRecording (fun j => (j : ℝ)) (fun j => cumulativeSamples Z j ω) E = n+1 ∧
    ω ∈ nativeFirstLargeThresholdEvent Z E t n}

theorem nativeFirstSelectedLargeThresholdEvent_eq_union {Ω : Type*} (Z : ℕ → Ω → ℝ) (E t : ℝ) :
    nativeFirstSelectedLargeThresholdEvent Z E t = ⋃ n, nativeFirstLargeThresholdEvent Z E t n := by
  apply Set.ext
  intro ω
  constructor
  · rintro ⟨n,_,hn⟩
    exact Set.mem_iUnion.mpr ⟨n,hn⟩
  · intro hω
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hω
    exact ⟨n,nativeFirstLargeThresholdEvent_recording Z E t n hn,hn⟩

/-- An exponential bound for the large-threshold upper-rejection layer at the
actual selected rejection. It includes the complete infinite charging sum. -/
theorem measure_nativeFirstSelectedLargeThresholdEvent_le {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} {Z : ℕ → Ω → ℝ}
    (hZ : ∀ j, Measurable (Z j)) (hi : iIndepFun Z μ)
    (hG : ∀ j, μ.map (Z j) = gaussianReal 0 1) {E : ℝ} (hE : 1 ≤ 2*E)
    {t : ℝ} (ht : 2 < t) :
    μ (nativeFirstSelectedLargeThresholdEvent Z E t) ≤
      ENNReal.ofReal (gaussianChargingConstant*gaussianChargingCutoffConstant*Real.exp (-t/8)) := by
  rw [nativeFirstSelectedLargeThresholdEvent_eq_union]
  exact measure_nativeFirstLargeThreshold_union_le hZ hi hG hE ht

end SwingRepair
