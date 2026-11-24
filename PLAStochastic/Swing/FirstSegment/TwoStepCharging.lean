import PLAStochastic.Swing.DenseSampling.CarriedPrefix.StoppedHistoryConditional
import PLAStochastic.Swing.FirstSegment.DurationMeasurability
import PLAStochastic.Swing.Gaussian.Tail.SelectedExcess
import PLAStochastic.Swing.Gaussian.Tail.ChargingEstimates

/-! # Two-step charging at the actual first native rejection

A proxy accepts one sample below the upper rejection threshold and rejects on
the following sample. Its first rejection index is proved from the actual
maximal-prefix rule. Distinct prefixes therefore produce disjoint proxy
events; summing the probability comparison never introduces an expected
number of inspected prefixes.
-/
noncomputable section
open Classical
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- The old upper endpoint fits the proxy sample, remains an upper bound on
all feasible slopes, and the next increment rejects from above. -/
theorem native_first_upper_proxy (y : ℕ → ℝ) {E u d : ℝ} {n : ℕ}
    (hn : 1 ≤ n) (hd : 0 ≤ d) (hdE : d ≤ 2*E)
    (hfit : feasibleSlope (Finset.Icc 1 n) (fun j => (j : ℝ)) y 0 (y 0) E u)
    (hmax : ∀ m, feasibleSlope (Finset.Icc 1 n) (fun j => (j : ℝ)) y 0 (y 0) E m → m ≤ u)
    (hnext : y (n+1) = y 0+((n+1 : ℕ) : ℝ)*u+E-d)
    (hrej : u+d < y (n+2)-y (n+1)) :
    nativePrefixFeasible (fun j => (j : ℝ)) y E 0 (n+1) (y 0) ∧
      ¬ nativePrefixFeasible (fun j => (j : ℝ)) y E 0 (n+2) (y 0) ∧
      nativeFirstRecording (fun j => (j : ℝ)) y E = n+1 := by
  have hpass : feasibleSlope (Finset.Icc 1 (n+1)) (fun j => (j : ℝ)) y 0 (y 0) E u := by
    intro j hj
    have hj' := Finset.mem_Icc.mp hj
    by_cases hjn : j ≤ n
    · exact hfit j (Finset.mem_Icc.mpr ⟨hj'.1,hjn⟩)
    · have he : j = n+1 := by omega
      subst j
      rw [hnext]
      simp only [sub_zero]
      rw [abs_le]
      constructor <;> nlinarith
  have hp : nativePrefixFeasible (fun j => (j : ℝ)) y E 0 (n+1) (y 0) := by
    refine ⟨u,?_⟩
    simpa only [Nat.cast_zero] using! hpass
  have hr : ¬ nativePrefixFeasible (fun j => (j : ℝ)) y E 0 (n+2) (y 0) := by
    rintro ⟨m,hm⟩
    have hmold : feasibleSlope (Finset.Icc 1 n) (fun j => (j : ℝ)) y 0 (y 0) E m := by
      intro j hj
      have hj' := Finset.mem_Icc.mp hj
      simpa only [Nat.cast_zero] using! hm j (Finset.mem_Icc.mpr ⟨hj'.1,by omega⟩)
    have hmu := hmax m hmold
    have hmend := hm (n+2) (Finset.mem_Icc.mpr ⟨by omega,le_rfl⟩)
    simp only [Nat.cast_zero, sub_zero] at hmend
    have hbound := (abs_le.mp hmend).2
    rw [hnext] at hrej
    have hmul := mul_le_mul_of_nonneg_left hmu (show (0 : ℝ) ≤ (n+2 : ℕ) by positivity)
    push_cast at hrej hmul hbound
    nlinarith
  refine ⟨hp,hr,?_⟩
  have hthreshold : ∀ j, nativePrefixFeasible (fun j => (j : ℝ)) y E 0 j (y 0) ↔ j < n+2 := by
    intro j
    constructor
    · intro hj
      by_contra hnj
      exact hr (nativePrefixFeasible_mono_end hj (by omega))
    · intro hj
      exact nativePrefixFeasible_mono_end hp (by omega)
  simpa only [show n+2-1 = n+1 by omega] using
    nativeFirstRecording_eq_threshold (fun j => (j : ℝ)) y E (by omega : 1 < n+2) hthreshold

/-- At any accepted prefix the final upper cone endpoint is a feasible slope
and bounds every feasible slope, with no assumption on the selected SSE fit. -/
theorem native_first_upper_endpoint_spec (y : ℕ → ℝ) (E : ℝ) {n : ℕ} (hn : 1 ≤ n)
    (hfit : nativePrefixFeasible (fun j => (j : ℝ)) y E 0 n (y 0)) :
    let u := nativeConeUpper (Finset.Icc 1 n) (Finset.nonempty_Icc.mpr hn)
      (fun j => (j : ℝ)) y 0 (y 0) E
    feasibleSlope (Finset.Icc 1 n) (fun j => (j : ℝ)) y 0 (y 0) E u ∧
      ∀ m, feasibleSlope (Finset.Icc 1 n) (fun j => (j : ℝ)) y 0 (y 0) E m → m ≤ u := by
  let samples := Finset.Icc 1 n
  have hne : samples.Nonempty := Finset.nonempty_Icc.mpr hn
  have ht : ∀ i ∈ samples, (0 : ℝ) < (i : ℝ) := by
    intro i hi
    have := (Finset.mem_Icc.mp hi).1
    exact_mod_cast (show 0 < i by omega)
  have hb := (nativeCone_nonempty_iff samples hne (fun j => (j : ℝ)) y 0 (y 0) E ht).mp (by
    simpa only [nativePrefixFeasible, Nat.zero_add, Nat.cast_zero] using! hfit)
  constructor
  · exact (nativeCone_mem_iff samples hne (fun j => (j : ℝ)) y 0 (y 0) E _ ht).mp ⟨hb,le_rfl⟩
  · intro m hm
    exact ((nativeCone_mem_iff samples hne (fun j => (j : ℝ)) y 0 (y 0) E m ht).mpr hm).2

/-- The same two-step construction uses the actual old endpoint of the native
cone, rather than an arbitrary bound on its slope. -/
theorem native_first_upper_proxy_at_endpoint (y : ℕ → ℝ) {E d : ℝ} {n : ℕ}
    (hn : 1 ≤ n) (hd : 0 ≤ d) (hdE : d ≤ 2*E)
    (hfit : nativePrefixFeasible (fun j => (j : ℝ)) y E 0 n (y 0))
    (hnext : y (n+1) = y 0+((n+1 : ℕ) : ℝ)*
      nativeConeUpper (Finset.Icc 1 n) (Finset.nonempty_Icc.mpr hn)
        (fun j => (j : ℝ)) y 0 (y 0) E+E-d)
    (hrej : nativeConeUpper (Finset.Icc 1 n) (Finset.nonempty_Icc.mpr hn)
      (fun j => (j : ℝ)) y 0 (y 0) E+d < y (n+2)-y (n+1)) :
    nativeFirstRecording (fun j => (j : ℝ)) y E = n+1 := by
  have hs := native_first_upper_endpoint_spec y E hn hfit
  exact (native_first_upper_proxy y hn hd hdE hs.1 hs.2 hnext hrej).2.2

/-- The actual proxy event: the first prospective increment lands between
one-half and one below the upper threshold, then the next increment rejects
from above. The index n+1 is positive by construction. -/
def nativeFirstUpperProxyEvent {Ω : Type*} (Y : ℕ → Ω → ℝ) (E : ℝ) (n : ℕ) : Set Ω :=
  {ω | let b := n+1
       let u := nativeConeUpper (Finset.Icc 1 b) (Finset.nonempty_Icc.mpr (by omega))
         (fun j => (j : ℝ)) (fun j => Y j ω) 0 (Y 0 ω) E
       let d := Y 0 ω+((b+1 : ℕ) : ℝ)*u+E-Y (b+1) ω
       nativePrefixFeasible (fun j => (j : ℝ)) (fun j => Y j ω) E 0 b (Y 0 ω) ∧
         d ∈ Icc (1/2) 1 ∧ u+d < Y (b+2) ω-Y (b+1) ω}

theorem nativeFirstUpperProxyEvent_recording {Ω : Type*} (Y : ℕ → Ω → ℝ)
    {E : ℝ} (hE : 1 ≤ 2*E) (n : ℕ) {ω : Ω} (hω : ω ∈ nativeFirstUpperProxyEvent Y E n) :
    nativeFirstRecording (fun j => (j : ℝ)) (fun j => Y j ω) E = n+2 := by
  dsimp only [nativeFirstUpperProxyEvent, Set.mem_ofPred_eq] at hω
  obtain ⟨hfit,hd,hrej⟩ := hω
  have hh := native_first_upper_proxy_at_endpoint (fun j => Y j ω)
    (by omega : 1 ≤ n+1) (by linarith [hd.1]) (hd.2.trans hE) hfit (by ring) hrej
  simpa only [Nat.add_assoc] using hh

/-- The proxies are disjoint because each forces a different actual first
recording, including its accepted-sample versus rejection-sample index shift. -/
theorem nativeFirstUpperProxyEvent_pairwiseDisjoint {Ω : Type*} (Y : ℕ → Ω → ℝ)
    {E : ℝ} (hE : 1 ≤ 2*E) : Pairwise (fun n m => Disjoint (nativeFirstUpperProxyEvent Y E n) (nativeFirstUpperProxyEvent Y E m)) := by
  intro n m hnm
  apply Set.disjoint_left.mpr
  intro ω hn hm
  have h₁ := nativeFirstUpperProxyEvent_recording Y hE n hn
  have h₂ := nativeFirstUpperProxyEvent_recording Y hE m hm
  exact hnm (by omega)

/-- Countable charging against disjoint events. The bound contains no count of
prefixes, finite or expected; only the total probability of the proxies. -/
theorem measure_iUnion_le_of_disjoint_charging {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {A B : ℕ → Set Ω} {c : ℝ≥0∞}
    (hB : ∀ n, MeasurableSet (B n)) (hd : Pairwise (fun n m => Disjoint (B n) (B m)))
    (hcharge : ∀ n, μ (A n) ≤ c*μ (B n)) : μ (⋃ n, A n) ≤ c := by
  calc
    μ (⋃ n, A n) ≤ ∑' n, μ (A n) := measure_iUnion_le _
    _ ≤ ∑' n, c*μ (B n) := ENNReal.tsum_le_tsum hcharge
    _ = c*(∑' n, μ (B n)) := ENNReal.tsum_mul_left
    _ = c*μ (⋃ n, B n) := by rw [measure_iUnion hd hB]
    _ ≤ c*1 := mul_le_mul_right (prob_le_one (μ := μ)) _
    _ = c := mul_one _

theorem measurableSet_nativeFirstUpperProxyEvent {Ω : Type*} [MeasurableSpace Ω]
    (Y : ℕ → Ω → ℝ) (hY : ∀ j, Measurable (Y j)) (E : ℝ) (n : ℕ) :
    MeasurableSet (nativeFirstUpperProxyEvent Y E n) := by
  let u (ω : Ω) := nativeConeUpper (Finset.Icc 1 (n+1)) (Finset.nonempty_Icc.mpr (by omega))
    (fun j => (j : ℝ)) (fun j => Y j ω) 0 (Y 0 ω) E
  have hu : Measurable u := measurable_nativeConeUpper _ _ _ Y 0 E (hY 0) (fun j _ => hY j)
  have hd : Measurable (fun ω => Y 0 ω+((n+2 : ℕ) : ℝ)*u ω+E-Y (n+2) ω) :=
    (((hY 0).add (hu.const_mul _)).add_const E).sub (hY (n+2))
  have hp := nativePrefixFeasible_measurableSet (fun j => (j : ℝ))
    (fun i j hj => by simpa using! (Nat.cast_lt.mpr hj : (i : ℝ) < (j : ℝ))) Y E 0 (n+1) (by omega) (hY 0) (fun j _ => hY j)
  exact hp.inter (((measurableSet_le measurable_const hd).inter
    (measurableSet_le hd measurable_const)).inter
      (measurableSet_lt (hu.add hd) ((hY (n+3)).sub (hY (n+2)))))

/-- A local probability charge against the genuine two-step proxy can be
summed over every possible prefix without a factor E[J]. -/
theorem native_first_upper_proxy_charging {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ j, Measurable (Y j)) {E : ℝ} (hE : 1 ≤ 2*E)
    {A : ℕ → Set Ω} {c : ℝ≥0∞}
    (hcharge : ∀ n, μ (A n) ≤ c*μ (nativeFirstUpperProxyEvent Y E n)) :
    μ (⋃ n, A n) ≤ c :=
  measure_iUnion_le_of_disjoint_charging (measurableSet_nativeFirstUpperProxyEvent Y hY E)
    (nativeFirstUpperProxyEvent_pairwiseDisjoint Y hE) hcharge

/-- Exact integral of a measurable event indicator. -/
theorem integral_if_one_eq_measureReal {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {A : Set Ω} [DecidablePred (fun ω => ω ∈ A)] (hA : MeasurableSet A) :
    (∫ ω, if ω ∈ A then (1 : ℝ) else 0 ∂μ) = μ.real A := by
  have he : (fun ω => if ω ∈ A then (1 : ℝ) else 0) = A.indicator (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases hω : ω ∈ A
    · rw [if_pos hω, Set.indicator_of_mem hω]
    · rw [if_neg hω, Set.indicator_of_notMem hω]
  rw [he, integral_indicator hA, setIntegral_const, smul_eq_mul, mul_one]

/-- A joint-law charging step for a past-selected threshold and two fresh
Gaussian increments. The second increment is kept in the probability space;
the past-selected rejection increment is never assigned a Gaussian law. -/
theorem independent_gaussian_two_step_charge {Ω α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → α} {Y : Ω → ℝ × ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hi : IndepFun X Y μ) (hlaw : μ.map Y = (gaussianReal 0 1).prod (gaussianReal 0 1))
    {U : Set α} (hU : MeasurableSet U) {r : α → ℝ} (hr : Measurable r)
    (M b : ℝ) (hscalar : ∀ x ∈ U, (gaussianReal 0 1).real (Ioi (r x)) ≤
      b*((gaussianReal 0 1).real (Icc (r x-1) (r x-1/2))*(gaussianReal 0 1).real (Ioi (M+1)))) :
    μ.real {ω | X ω ∈ U ∧ r (X ω) < (Y ω).1} ≤
      b*μ.real {ω | X ω ∈ U ∧ (Y ω).1 ∈ Icc (r (X ω)-1) (r (X ω)-1/2) ∧ M+1 < (Y ω).2} := by
  let F (p : α × (ℝ × ℝ)) : ℝ := if r p.1 < p.2.1 then 1 else 0
  let G (p : α × (ℝ × ℝ)) : ℝ :=
    if p.2.1 ∈ Icc (r p.1-1) (r p.1-1/2) ∧ M+1 < p.2.2 then 1 else 0
  have hFm : Measurable F := measurable_const.ite
    (measurableSet_lt (hr.comp measurable_fst) measurable_snd.fst) measurable_const
  have hGm : Measurable G := measurable_const.ite
    (((measurableSet_le ((hr.comp measurable_fst).sub_const 1) measurable_snd.fst).inter
      (measurableSet_le measurable_snd.fst ((hr.comp measurable_fst).sub_const (1/2)))).inter
        (measurableSet_lt measurable_const measurable_snd.snd)) measurable_const
  have hFb : ∀ p, |F p| ≤ 1 := by intro p; dsimp only [F]; split_ifs <;> norm_num
  have hGb : ∀ p, |G p| ≤ 1 := by intro p; dsimp only [G]; split_ifs <;> norm_num
  have hsection : ∀ x ∈ U, (∫ y, F (x,y) ∂μ.map Y) ≤ b*(∫ y, G (x,y) ∂μ.map Y)+0 := by
    intro x hx
    rw [hlaw]
    have heF : (fun y => F (x,y)) = fun y : ℝ × ℝ =>
        if y ∈ Ioi (r x) ×ˢ (Set.univ : Set ℝ) then (1 : ℝ) else 0 := by
      funext y
      simp only [F, Set.mem_prod, Set.mem_Ioi, Set.mem_univ, and_true]
    have heG : (fun y => G (x,y)) = fun y : ℝ × ℝ =>
        if y ∈ Icc (r x-1) (r x-1/2) ×ˢ Ioi (M+1) then (1 : ℝ) else 0 := rfl
    have hfv : (∫ y, F (x,y) ∂(gaussianReal 0 1).prod (gaussianReal 0 1)) =
        (gaussianReal 0 1).real (Ioi (r x)) := by
      calc
        _ = ∫ y, if y ∈ Ioi (r x) ×ˢ (Set.univ : Set ℝ) then (1 : ℝ) else 0
              ∂(gaussianReal 0 1).prod (gaussianReal 0 1) := congrArg _ heF
        _ = ((gaussianReal 0 1).prod (gaussianReal 0 1)).real (Ioi (r x) ×ˢ Set.univ) :=
          integral_if_one_eq_measureReal (measurableSet_Ioi.prod MeasurableSet.univ)
        _ = _ := by rw [measureReal_prod_prod, probReal_univ, mul_one]
    have hgv : (∫ y, G (x,y) ∂(gaussianReal 0 1).prod (gaussianReal 0 1)) =
        (gaussianReal 0 1).real (Icc (r x-1) (r x-1/2))*(gaussianReal 0 1).real (Ioi (M+1)) := by
      calc
        _ = ∫ y, if y ∈ Icc (r x-1) (r x-1/2) ×ˢ Ioi (M+1) then (1 : ℝ) else 0
              ∂(gaussianReal 0 1).prod (gaussianReal 0 1) := congrArg _ heG
        _ = ((gaussianReal 0 1).prod (gaussianReal 0 1)).real (Icc (r x-1) (r x-1/2) ×ˢ Ioi (M+1)) :=
          integral_if_one_eq_measureReal (measurableSet_Icc.prod measurableSet_Ioi)
        _ = _ := measureReal_prod_prod _ _
    rw [hfv, hgv, add_zero]
    exact hscalar x hx
  have hc := IndepFun.integral_state_guard_le hX.aemeasurable hY.aemeasurable hi hU hFm hGm
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1) hFb hGb hsection
  have hA : MeasurableSet {ω | X ω ∈ U ∧ r (X ω) < (Y ω).1} :=
    (hU.preimage hX).inter (measurableSet_lt (hr.comp hX) hY.fst)
  have hB : MeasurableSet {ω | X ω ∈ U ∧ (Y ω).1 ∈ Icc (r (X ω)-1) (r (X ω)-1/2) ∧ M+1 < (Y ω).2} :=
    (hU.preimage hX).inter (((measurableSet_le ((hr.comp hX).sub_const 1) hY.fst).inter
      (measurableSet_le hY.fst ((hr.comp hX).sub_const (1/2)))).inter
        (measurableSet_lt measurable_const hY.snd))
  have heF : (fun ω => if X ω ∈ U then F (X ω,Y ω) else 0) =
      fun ω => if ω ∈ {ω | X ω ∈ U ∧ r (X ω) < (Y ω).1} then (1 : ℝ) else 0 := by
    funext ω
    dsimp only [F, Set.mem_ofPred_eq]
    split_ifs <;> tauto
  have heG : (fun ω => if X ω ∈ U then G (X ω,Y ω) else 0) =
      fun ω => if ω ∈ {ω | X ω ∈ U ∧ (Y ω).1 ∈ Icc (r (X ω)-1) (r (X ω)-1/2) ∧ M+1 < (Y ω).2}
        then (1 : ℝ) else 0 := by
    funext ω
    dsimp only [G, Set.mem_ofPred_eq]
    split_ifs <;> tauto
  have hFL : (∫ ω, if X ω ∈ U then F (X ω,Y ω) else 0 ∂μ) =
      μ.real {ω | X ω ∈ U ∧ r (X ω) < (Y ω).1} :=
    (congrArg (fun f : Ω → ℝ => ∫ ω, f ω ∂μ) heF).trans (integral_if_one_eq_measureReal hA)
  have hGL : (∫ ω, if X ω ∈ U then G (X ω,Y ω) else 0 ∂μ) =
      μ.real {ω | X ω ∈ U ∧ (Y ω).1 ∈ Icc (r (X ω)-1) (r (X ω)-1/2) ∧ M+1 < (Y ω).2} :=
    (congrArg (fun f : Ω → ℝ => ∫ ω, f ω ∂μ) heG).trans (integral_if_one_eq_measureReal hB)
  rw [hFL, hGL, zero_mul, add_zero] at hc
  exact hc

/-- The proved Gaussian interval bound discharges the local scalar charge
uniformly on a past-selected large-threshold layer. -/
theorem independent_gaussian_two_step_charge_large_threshold {Ω α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → α} {Y : Ω → ℝ × ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hi : IndepFun X Y μ) (hlaw : μ.map Y = (gaussianReal 0 1).prod (gaussianReal 0 1))
    {U : Set α} (hU : MeasurableSet U) {r : α → ℝ} (hr : Measurable r)
    {t : ℝ} (ht : 2 < t) (hthreshold : ∀ x ∈ U, t/2 < r x) (M : ℝ) :
    μ.real {ω | X ω ∈ U ∧ r (X ω) < (Y ω).1} ≤
      (gaussianChargingConstant*Real.exp (-t/4)/(gaussianReal 0 1).real (Ioi (M+1)))*
        μ.real {ω | X ω ∈ U ∧ (Y ω).1 ∈ Icc (r (X ω)-1) (r (X ω)-1/2) ∧ M+1 < (Y ω).2} := by
  apply independent_gaussian_two_step_charge hX hY hi hlaw hU hr
  intro x hx
  have hrx : 1 < r x := by linarith [hthreshold x hx]
  have htail := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
    (gaussianReal_tail_le_charging_interval hrx)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal
    (mul_nonneg gaussianChargingConstant_pos.le (Real.exp_nonneg _))] at htail
  have he := Real.exp_le_exp.mpr (show -r x/2 ≤ -t/4 by linarith [hthreshold x hx])
  have hq : 0 < (gaussianReal 0 1).real (Ioi (M+1)) :=
    ENNReal.toReal_pos (gaussianReal_Ioi_pos _).ne' (measure_ne_top _ _)
  calc
    (gaussianReal 0 1).real (Ioi (r x)) ≤
        (gaussianChargingConstant*Real.exp (-r x/2)) *
          (gaussianReal 0 1).real (Icc (r x-1) (r x-1/2)) := htail
    _ ≤ (gaussianChargingConstant*Real.exp (-t/4)) *
          (gaussianReal 0 1).real (Icc (r x-1) (r x-1/2)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left he gaussianChargingConstant_pos.le) ENNReal.toReal_nonneg
    _ = _ := by field_simp

/-- With the paper's square-root cutoff, the large-threshold local charge has
an explicit exponential factor. -/
theorem independent_gaussian_two_step_charge_sqrt_cutoff {Ω α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → α} {Y : Ω → ℝ × ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hi : IndepFun X Y μ) (hlaw : μ.map Y = (gaussianReal 0 1).prod (gaussianReal 0 1))
    {U : Set α} (hU : MeasurableSet U) {r : α → ℝ} (hr : Measurable r)
    {t : ℝ} (ht : 2 < t) (hthreshold : ∀ x ∈ U, t/2 < r x) :
    μ.real {ω | X ω ∈ U ∧ r (X ω) < (Y ω).1} ≤
      (gaussianChargingConstant*gaussianChargingCutoffConstant*Real.exp (-t/8))*
        μ.real {ω | X ω ∈ U ∧ (Y ω).1 ∈ Icc (r (X ω)-1) (r (X ω)-1/2) ∧
          Real.sqrt t/4+1 < (Y ω).2} := by
  have hc := independent_gaussian_two_step_charge_large_threshold hX hY hi hlaw hU hr ht hthreshold
    (Real.sqrt t/4)
  have hb := gaussianCharging_cutoff_ratio (show 0 ≤ t by linarith)
  have hmul := mul_le_mul_of_nonneg_left hb gaussianChargingConstant_pos.le
  have hfactor : gaussianChargingConstant*Real.exp (-t/4)/
      (gaussianReal 0 1).real (Ioi (Real.sqrt t/4+1)) ≤
      gaussianChargingConstant*gaussianChargingCutoffConstant*Real.exp (-t/8) := by
    simpa only [Measure.real, mul_div_assoc, mul_assoc] using hmul
  exact hc.trans (mul_le_mul_of_nonneg_right hfactor ENNReal.toReal_nonneg)

/-- Two consecutive fresh increments are jointly independent of every state
measurable for the previously observed iid increments. -/
theorem iid_two_fresh_gaussians_of_history {Ω α : Type*}
    [mΩ : MeasurableSpace Ω] [MeasurableSpace α] {μ : Measure Ω}
    {Z : ℕ → Ω → ℝ} (hZ : ∀ j, Measurable (Z j)) (hi : iIndepFun Z μ)
    (hG : ∀ j, μ.map (Z j) = gaussianReal 0 1) (n : ℕ)
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
  simpa only [hG n, hG (n+1)] using hp

/-- The exponential charging bound for an arbitrary state computed from the
actual iid Gaussian past. Fresh-pair law and independence are proved here. -/
theorem iid_gaussian_two_step_charge_sqrt_cutoff {Ω α : Type*}
    [mΩ : MeasurableSpace Ω] [MeasurableSpace α] {μ : Measure Ω}
    {Z : ℕ → Ω → ℝ} (hZ : ∀ j, Measurable (Z j)) (hi : iIndepFun Z μ)
    (hG : ∀ j, μ.map (Z j) = gaussianReal 0 1) (n : ℕ)
    {X : Ω → α} (hX : Measurable[incrementIndexSpace Z (Iio n)] X)
    {U : Set α} (hU : MeasurableSet U) {r : α → ℝ} (hr : Measurable r)
    {t : ℝ} (ht : 2 < t) (hthreshold : ∀ x ∈ U, t/2 < r x) :
    μ.real {ω | X ω ∈ U ∧ r (X ω) < Z n ω} ≤
      (gaussianChargingConstant*gaussianChargingCutoffConstant*Real.exp (-t/8))*
        μ.real {ω | X ω ∈ U ∧ Z n ω ∈ Icc (r (X ω)-1) (r (X ω)-1/2) ∧
          Real.sqrt t/4+1 < Z (n+1) ω} := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hf := iid_two_fresh_gaussians_of_history hZ hi hG n hX
  exact independent_gaussian_two_step_charge_sqrt_cutoff
    (hX.mono (incrementIndexSpace_le hZ _) le_rfl) ((hZ n).prodMk (hZ (n+1)))
    hf.1 hf.2 hU hr ht hthreshold

end SwingRepair
