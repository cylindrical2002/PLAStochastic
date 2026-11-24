import PLAStochastic.Swing.StationaryScale.GoodBranch
import PLAStochastic.Swing.StationaryLimit.Slope.FiniteMoments

/-! # The complementary branch has small stationary probability

`eq:stationarybadbranch`: the complement of the favorable completion event is
covered by the failure of `eq:stationarypathgood`, i.e. by a large incoming
margin or by a large accepted fresh walk.  The walk part is the stopped maximal
estimate; the margin parts are the raw stopped-sum tail and the pathwise slope
envelope.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- The positive part of the stationary margin. -/
def nativeRestartMarginPos (E x : ℝ) : ℝ := max (E-|x|) 0

theorem measurable_nativeRestartMarginPos (E : ℝ) :
    Measurable (nativeRestartMarginPos E) :=
  ((measurable_const.sub measurable_id.abs).max measurable_const)

omit mΩ in
theorem abs_margin_lt_iff (E x t : ℝ) (ht : 0 ≤ t) :
    t < |E-abs x| ↔ t < nativeRestartMarginPos E x ∨ t < nativeRestartExcess E x := by
  unfold nativeRestartMarginPos nativeRestartExcess
  rcases le_total (|x|) E with h | h
  · rw [abs_of_nonneg (by linarith), max_eq_left (by linarith : (0:ℝ) ≤ E-|x|),
      max_eq_right (by linarith : |x|-E ≤ 0)]
    constructor
    · exact fun h' => Or.inl h'
    · rintro (h' | h') <;> [exact h'; linarith]
  · rw [abs_of_nonpos (by linarith), max_eq_right (by linarith : E-|x| ≤ 0),
      max_eq_left (by linarith : (0:ℝ) ≤ |x|-E)]
    constructor
    · intro h'
      exact Or.inr (by linarith)
    · rintro (h' | h') <;> [linarith; linarith]

/-! ### The positive margin is carried by the slope envelope -/

omit mΩ in
/-- Pathwise form of `eq:stationarymarginpositive` with the genuine Gaussian
partial-sum envelope and a unit slack, so no positivity hypothesis is needed. -/
theorem nativeRestart_marginPos_next_le (X : ℕ → Ω → ℝ) {E : ℝ} (hE : 0 ≤ E)
    (x : ℝ) (ω : Ω)
    (hW : ∀ n, |cumulativeSamples X n ω| ≤ nativeGaussianEnvelope X ω*((n : ℝ)+1))
    (hf : nativeRestartLength X E x ω ≠ ⊤) :
    nativeRestartMarginPos E (nativeRestartNext X E x ω) ≤
      5*nativeRestartExcess E x+10*nativeGaussianEnvelope X ω+10 := by
  have hG0 : 0 ≤ nativeGaussianEnvelope X ω := nativeGaussianEnvelope_nonneg X ω
  have hG1 : 0 ≤ nativeGaussianEnvelope X ω+1 := by linarith
  have hW' : ∀ n, |cumulativeSamples X n ω| ≤
      (nativeGaussianEnvelope X ω+1)*((n : ℝ)+1) := by
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ)+1 := by positivity
    have := hW n
    nlinarith
  have hc : 0 ≤ nativeRestartExcess E x := le_max_right _ _
  have hB : 0 < nativeRestartExcess E x+2*(nativeGaussianEnvelope X ω+1) := by linarith
  have hs := nativeRestart_slope_bound X hE hG1 ω hW' hB hf
  have hp := nativeRestart_margin_pos_le_slope X hE x ω hf
  have hchain : nativeRestartMarginPos E (nativeRestartNext X E x ω) ≤
      5*nativeRestartExcess E x+10*(nativeGaussianEnvelope X ω+1) := le_trans hp hs
  linarith

/-- Fixed-state bound for the positive-margin tail: either the incoming
negative margin is already large, or the fresh envelope is. -/
theorem measure_nativeRestart_marginPos_slice
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E) (x t : ℝ) :
    μ {ω | t < nativeRestartMarginPos E (nativeRestartNext X E x ω)} ≤
      {y : ℝ | (t-10)/10 < nativeRestartExcess E y}.indicator (fun _ => (1 : ℝ≥0∞)) x +
        μ {ω | (t-10)/20 < nativeGaussianEnvelope X ω} := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  by_cases hxc : (t-10)/10 < nativeRestartExcess E x
  · rw [Set.indicator_of_mem (show x ∈ {y : ℝ | (t-10)/10 < nativeRestartExcess E y} from hxc)]
    exact le_trans (prob_le_one) le_self_add
  · rw [Set.indicator_of_notMem
      (show x ∉ {y : ℝ | (t-10)/10 < nativeRestartExcess E y} from hxc), zero_add]
    have hxc' : nativeRestartExcess E x ≤ (t-10)/10 := le_of_not_gt hxc
    refine measure_mono_ae ?_
    filter_upwards [nativeRestartLength_ae_finite hX hi hG hE x,
      nativeGaussianEnvelope_bounds_ae hX hi hG] with ω hfin hW hω
    have hω' : t < nativeRestartMarginPos E (nativeRestartNext X E x ω) := hω
    have hb := nativeRestart_marginPos_next_le X hE.le x ω hW hfin
    show (t-10)/20 < nativeGaussianEnvelope X ω
    linarith

/-! ### Measurability of the survival events in the joint space -/

theorem withTop_nat_le_iff_ne (j : ℕ) (L : WithTop ℕ) :
    ((j : ℕ) : WithTop ℕ) ≤ L ↔ ∀ i : ℕ, i < j → L ≠ ((i : ℕ) : WithTop ℕ) := by
  constructor
  · intro h i hi heq
    rw [heq] at h
    have hji : j ≤ i := by exact_mod_cast h
    omega
  · intro h
    by_contra hcon
    have hlt : L < ((j : ℕ) : WithTop ℕ) := lt_of_not_ge hcon
    cases L using WithTop.recTopCoe with
    | top => exact absurd hlt (by simp)
    | coe n => exact h n (WithTop.coe_lt_coe.mp hlt) rfl

theorem measurableSet_nativeRestartLength_ge_prod (hX : ∀ j, Measurable (X j)) (E : ℝ)
    (j : ℕ) :
    MeasurableSet {p : ℝ × Ω | ((j : ℕ) : WithTop ℕ) ≤ nativeRestartLength X E p.1 p.2} := by
  have hset : {p : ℝ × Ω | ((j : ℕ) : WithTop ℕ) ≤ nativeRestartLength X E p.1 p.2} =
      (⋃ i : Fin j, {p : ℝ × Ω |
        nativeRestartLength X E p.1 p.2 = (((i : ℕ) : ℕ) : WithTop ℕ)})ᶜ := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    rw [withTop_nat_le_iff_ne]
    exact ⟨fun h i => h i i.isLt, fun h i hi => h ⟨i, hi⟩⟩
  rw [hset]
  refine MeasurableSet.compl (MeasurableSet.iUnion fun i => ?_)
  exact measurableSet_eq_fun (nativeRestartLength_measurable X hX E) measurable_const

theorem measurableSet_nativeRestartLength_top_prod (hX : ∀ j, Measurable (X j)) (E : ℝ) :
    MeasurableSet {p : ℝ × Ω | nativeRestartLength X E p.1 p.2 = ⊤} := by
  have hset : {p : ℝ × Ω | nativeRestartLength X E p.1 p.2 = ⊤} =
      ⋂ j : ℕ, {p : ℝ × Ω | ((j : ℕ) : WithTop ℕ) ≤ nativeRestartLength X E p.1 p.2} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro h j
      rw [h]
      exact le_top
    · intro h
      by_contra hcon
      cases hL : nativeRestartLength X E p.1 p.2 using WithTop.recTopCoe with
      | top => exact hcon hL
      | coe n =>
        have hn := h (n+1)
        rw [hL] at hn
        have hle : n+1 ≤ n := WithTop.coe_le_coe.mp hn
        omega
  rw [hset]
  exact MeasurableSet.iInter fun j => measurableSet_nativeRestartLength_ge_prod hX E j

/-- The joint level-crossing event of the accepted fresh walk. -/
def nativeRestartWalkExit (X : ℕ → Ω → ℝ) (E lam : ℝ) : Set (ℝ × Ω) :=
  {p | ∃ j : ℕ, ((j : ℕ) : WithTop ℕ) ≤ nativeRestartLength X E p.1 p.2 ∧
    lam < |cumulativeSamples X j p.2|}

theorem measurableSet_nativeRestartWalkExit (hX : ∀ j, Measurable (X j)) (E lam : ℝ) :
    MeasurableSet (nativeRestartWalkExit X E lam) := by
  have hset : nativeRestartWalkExit X E lam =
      ⋃ j : ℕ, ({p : ℝ × Ω | ((j : ℕ) : WithTop ℕ) ≤ nativeRestartLength X E p.1 p.2} ∩
        {p : ℝ × Ω | lam < |cumulativeSamples X j p.2|}) := by
    ext p
    simp only [nativeRestartWalkExit, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
  rw [hset]
  refine MeasurableSet.iUnion fun j => (measurableSet_nativeRestartLength_ge_prod hX E j).inter ?_
  exact measurableSet_lt measurable_const
    (((Finset.measurable_sum (Finset.range j) (fun k _ => hX k)).comp measurable_snd).abs)

/-! ### The three stationary pieces -/

theorem measure_prod_nativeRestartLength_top [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E)
    {π : Measure ℝ} [IsProbabilityMeasure π] :
    (π.prod μ) {p : ℝ × Ω | nativeRestartLength X E p.1 p.2 = ⊤} = 0 := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  rw [Measure.prod_apply (measurableSet_nativeRestartLength_top_prod hX E)]
  have hzero : ∀ x : ℝ, μ ((Prod.mk x) ⁻¹'
      {p : ℝ × Ω | nativeRestartLength X E p.1 p.2 = ⊤}) = 0 := by
    intro x
    have h0 := ae_iff.mp (nativeRestartLength_ae_finite hX hi hG hE x)
    have hset : {a | ¬ nativeRestartLength X E x a ≠ ⊤} =
        (Prod.mk x) ⁻¹' {p : ℝ × Ω | nativeRestartLength X E p.1 p.2 = ⊤} := by
      ext a
      simp
    rwa [hset] at h0
  calc
    (∫⁻ x, μ ((Prod.mk x) ⁻¹' {p : ℝ × Ω | nativeRestartLength X E p.1 p.2 = ⊤}) ∂π)
        = ∫⁻ _x : ℝ, 0 ∂π := lintegral_congr hzero
    _ = 0 := lintegral_zero

theorem measure_prod_nativeRestartWalkExit [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E)
    {π : Measure ℝ} [IsProbabilityMeasure π] {lam : ℝ} (hlam : 0 < lam) :
    (π.prod μ) (nativeRestartWalkExit X E lam) ≤
      ENNReal.ofReal ((∫ x, nativeRestartMean X μ E x ∂π)/lam^2) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hmeas : Measurable (nativeRestartMean X μ E) := nativeRestartMean_measurable hX E
  have hbounds := nativeRestartMean_bounds hX hi hG hE
  have hnonneg : ∀ x, 0 ≤ nativeRestartMean X μ E x :=
    fun x => (by norm_num : (0 : ℝ) ≤ 1).trans (hbounds x).1
  have hupper : ∀ x, nativeRestartMean X μ E x ≤ nativeRestartMeanBound E :=
    fun x => (hbounds x).2
  have hint : Integrable (nativeRestartMean X μ E) π :=
    Doeblin.integrable_bounded_reward π hmeas hnonneg hupper
  have hintd : Integrable (fun x => nativeRestartMean X μ E x/lam^2) π := hint.div_const _
  rw [Measure.prod_apply (measurableSet_nativeRestartWalkExit hX E lam)]
  calc
    (∫⁻ x, μ ((Prod.mk x) ⁻¹' nativeRestartWalkExit X E lam) ∂π)
        ≤ ∫⁻ x, ENNReal.ofReal (nativeRestartMean X μ E x/lam^2) ∂π := by
      refine lintegral_mono fun x => ?_
      have hslice : (Prod.mk x) ⁻¹' nativeRestartWalkExit X E lam =
          {ω | ∃ j : ℕ, ((j : ℕ) : WithTop ℕ) ≤ nativeRestartLength X E x ω ∧
            lam < |cumulativeSamples X j ω|} := rfl
      rw [hslice]
      have hreal := measureReal_restart_maximum_le hX hi hG hE x hlam
      calc
        μ {ω | ∃ j : ℕ, ((j : ℕ) : WithTop ℕ) ≤ nativeRestartLength X E x ω ∧
            lam < |cumulativeSamples X j ω|}
            = ENNReal.ofReal (μ.real {ω | ∃ j : ℕ,
                ((j : ℕ) : WithTop ℕ) ≤ nativeRestartLength X E x ω ∧
                  lam < |cumulativeSamples X j ω|}) :=
          (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (∫ x, nativeRestartMean X μ E x/lam^2 ∂π) :=
      (ofReal_integral_eq_lintegral_ofReal hintd
        (Filter.Eventually.of_forall fun x =>
          div_nonneg (hnonneg x) (by positivity))).symm
    _ = ENNReal.ofReal ((∫ x, nativeRestartMean X μ E x ∂π)/lam^2) := by
      rw [integral_div]

/-! ### The stationary positive-margin tail -/

theorem measure_pi_nativeRestart_marginPos_tail [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E)
    {π : Measure ℝ} [IsProbabilityMeasure π]
    (hπ : (nativeRestartKernel X μ E).Invariant π) (t : ℝ) :
    π {y | t < nativeRestartMarginPos E y} ≤
      π {y | (t-10)/10 < nativeRestartExcess E y} +
        μ {ω | (t-10)/20 < nativeGaussianEnvelope X ω} := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hB : MeasurableSet {y : ℝ | t < nativeRestartMarginPos E y} :=
    measurableSet_lt measurable_const (measurable_nativeRestartMarginPos E)
  have hA : MeasurableSet {y : ℝ | (t-10)/10 < nativeRestartExcess E y} := by
    unfold nativeRestartExcess
    exact measurableSet_lt measurable_const
      ((measurable_id.abs.sub_const E).max measurable_const)
  have hms : MeasurableSet
      {p : ℝ × Ω | t < nativeRestartMarginPos E (nativeRestartNext X E p.1 p.2)} :=
    measurableSet_lt measurable_const
      ((measurable_nativeRestartMarginPos E).comp (nativeRestartNext_measurable X hX E))
  rw [nativeRestart_invariant_measure_eq_prod hX hπ hB]
  have hpre : (fun p : ℝ × Ω => nativeRestartNext X E p.1 p.2) ⁻¹'
      {y | t < nativeRestartMarginPos E y} =
      {p : ℝ × Ω | t < nativeRestartMarginPos E (nativeRestartNext X E p.1 p.2)} := rfl
  rw [hpre, Measure.prod_apply hms]
  calc
    (∫⁻ x, μ ((Prod.mk x) ⁻¹'
        {p : ℝ × Ω | t < nativeRestartMarginPos E (nativeRestartNext X E p.1 p.2)}) ∂π)
        ≤ ∫⁻ x, ({y : ℝ | (t-10)/10 < nativeRestartExcess E y}.indicator
            (fun _ => (1 : ℝ≥0∞)) x +
              μ {ω | (t-10)/20 < nativeGaussianEnvelope X ω}) ∂π := by
      refine lintegral_mono fun x => ?_
      exact measure_nativeRestart_marginPos_slice hX hi hG hE x t
    _ = π {y | (t-10)/10 < nativeRestartExcess E y} +
          μ {ω | (t-10)/20 < nativeGaussianEnvelope X ω} := by
      rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
      congr 1
      rw [lintegral_indicator hA]
      simp

/-! ### `eq:stationarybadbranch` -/

theorem measure_prod_nativeRestart_bad_branch [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E)
    {π : Measure ℝ} [IsProbabilityMeasure π] :
    (π.prod μ) (nativeRestartFavorableSet X E)ᶜ ≤
      (π {y : ℝ | E/40 < nativeRestartMarginPos E y} +
        π {y : ℝ | E/40 < nativeRestartExcess E y}) +
        ENNReal.ofReal ((∫ x, nativeRestartMean X μ E x ∂π)/(E/40)^2) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  set S : Set ℝ := {y : ℝ | E/40 < nativeRestartMarginPos E y} ∪
    {y : ℝ | E/40 < nativeRestartExcess E y} with hSdef
  have ht40 : (0 : ℝ) ≤ E/40 := by positivity
  have hcover : (nativeRestartFavorableSet X E)ᶜ ⊆
      ({p : ℝ × Ω | nativeRestartLength X E p.1 p.2 = ⊤} ∪ (S ×ˢ (univ : Set Ω))) ∪
        nativeRestartWalkExit X E (E/40) := by
    intro p hp
    by_contra hcon
    refine hp (nativeRestartPathGood_subset_favorable X hE ?_)
    refine ⟨?_, ?_, ?_⟩
    · intro htop
      exact hcon (Or.inl (Or.inl htop))
    · by_contra hmarg
      refine hcon (Or.inl (Or.inr ⟨?_, Set.mem_univ _⟩))
      exact (abs_margin_lt_iff E p.1 (E/40) ht40).mp (lt_of_not_ge hmarg)
    · intro j hj
      by_contra hw
      exact hcon (Or.inr ⟨j, hj, lt_of_not_ge hw⟩)
  have hprodS : (π.prod μ) (S ×ˢ (univ : Set Ω)) = π S := by
    rw [Measure.prod_prod, measure_univ, mul_one]
  have hSle : π S ≤ π {y : ℝ | E/40 < nativeRestartMarginPos E y} +
      π {y : ℝ | E/40 < nativeRestartExcess E y} := measure_union_le _ _
  calc
    (π.prod μ) (nativeRestartFavorableSet X E)ᶜ
        ≤ (π.prod μ) (({p : ℝ × Ω | nativeRestartLength X E p.1 p.2 = ⊤} ∪
            (S ×ˢ (univ : Set Ω))) ∪ nativeRestartWalkExit X E (E/40)) := measure_mono hcover
    _ ≤ (π.prod μ) ({p : ℝ × Ω | nativeRestartLength X E p.1 p.2 = ⊤} ∪
            (S ×ˢ (univ : Set Ω))) + (π.prod μ) (nativeRestartWalkExit X E (E/40)) :=
      measure_union_le _ _
    _ ≤ ((π.prod μ) {p : ℝ × Ω | nativeRestartLength X E p.1 p.2 = ⊤} +
            (π.prod μ) (S ×ˢ (univ : Set Ω))) +
          (π.prod μ) (nativeRestartWalkExit X E (E/40)) :=
      add_le_add (measure_union_le _ _) le_rfl
    _ = π S + (π.prod μ) (nativeRestartWalkExit X E (E/40)) := by
      rw [measure_prod_nativeRestartLength_top hX hi hG hE, hprodS, zero_add]
    _ ≤ (π {y : ℝ | E/40 < nativeRestartMarginPos E y} +
            π {y : ℝ | E/40 < nativeRestartExcess E y}) +
          ENNReal.ofReal ((∫ x, nativeRestartMean X μ E x ∂π)/(E/40)^2) :=
      add_le_add hSle (measure_prod_nativeRestartWalkExit hX hi hG hE (by positivity))

/-! ### Quantitative form

For large tolerance every term except the stopped maximal estimate is smaller
than `E^{-2}`, so the whole complementary branch costs `K C_E / E^2`.
-/

/-- A Gaussian-type exponent dominates any inverse square. -/
theorem exp_neg_le_inv_sq {E a : ℝ} (hE : 0 < E) (ha : 2*E ≤ a) :
    Real.exp (-a) ≤ 1/E^2 := by
  have hhalf : E ≤ Real.exp (a/2) := by
    have h := Real.add_one_le_exp (a/2)
    linarith
  have hsq : (Real.exp (a/2))^2 = Real.exp a := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hE2 : E^2 ≤ Real.exp a := by
    rw [← hsq]
    nlinarith [Real.exp_pos (a/2)]
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ (by positivity) hE2

/-- The tolerance threshold beyond which all non-maximal branch terms are
below `E^{-2}`. -/
def stationaryMarginThreshold : ℝ := 5120000

def stationaryBadBranchConstant : ℝ := 1604+nativeGaussianEnvelopeTailConstant

theorem stationaryBadBranchConstant_pos : 0 < stationaryBadBranchConstant := by
  have := nativeGaussianEnvelope_tail_constant_pos
  unfold stationaryBadBranchConstant
  linarith

theorem one_le_stationary_mean [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E)
    {π : Measure ℝ} [IsProbabilityMeasure π] :
    1 ≤ ∫ x, nativeRestartMean X μ E x ∂π := by
  have hmeas : Measurable (nativeRestartMean X μ E) := nativeRestartMean_measurable hX E
  have hbounds := nativeRestartMean_bounds hX hi hG hE
  have hnonneg : ∀ x, 0 ≤ nativeRestartMean X μ E x :=
    fun x => (by norm_num : (0 : ℝ) ≤ 1).trans (hbounds x).1
  have hupper : ∀ x, nativeRestartMean X μ E x ≤ nativeRestartMeanBound E :=
    fun x => (hbounds x).2
  have hint : Integrable (nativeRestartMean X μ E) π :=
    Doeblin.integrable_bounded_reward π hmeas hnonneg hupper
  simpa using integral_mono (integrable_const (1 : ℝ)) hint (fun x => (hbounds x).1)

theorem measure_prod_nativeRestart_bad_branch_le [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ}
    (hE : stationaryMarginThreshold ≤ E)
    {π : Measure ℝ} [IsProbabilityMeasure π]
    (hπ : (nativeRestartKernel X μ E).Invariant π) :
    (π.prod μ) (nativeRestartFavorableSet X E)ᶜ ≤
      ENNReal.ofReal (stationaryBadBranchConstant*
        (∫ x, nativeRestartMean X μ E x ∂π)/E^2) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hEnum : (5120000 : ℝ) ≤ E := by simpa [stationaryMarginThreshold] using hE
  have hEpos : (0 : ℝ) < E := by linarith
  set C := ∫ x, nativeRestartMean X μ E x ∂π with hCdef
  have hC1 : 1 ≤ C := one_le_stationary_mean hX hi hG hEpos
  have hC0 : (0 : ℝ) ≤ C := by linarith
  have hE2 : (0 : ℝ) < E^2 := by positivity
  -- the three exponential comparisons
  have hexp1 : Real.exp (-(E/40)^2/2) ≤ 1/E^2 := by
    have : Real.exp (-((E/40)^2/2)) ≤ 1/E^2 :=
      exp_neg_le_inv_sq hEpos (by nlinarith)
    simpa [neg_div] using this
  have hexp2 : Real.exp (-((E/40-10)/10)^2/2) ≤ 1/E^2 := by
    have : Real.exp (-(((E/40-10)/10)^2/2)) ≤ 1/E^2 :=
      exp_neg_le_inv_sq hEpos (by nlinarith)
    simpa [neg_div] using this
  have hv1 : (1 : ℝ) ≤ (E/40-10)/20 := by linarith
  have hexp3 : Real.exp (-((E/40-10)/20)^2) ≤ 1/E^2 :=
    exp_neg_le_inv_sq hEpos (by nlinarith)
  -- the negative-margin tails
  have htail1 : π {y : ℝ | E/40 < nativeRestartExcess E y} ≤ ENNReal.ofReal (2*C/E^2) := by
    refine (measure_pi_nativeRestart_margin_raw_tail hX hi hG hEpos hπ
      (by positivity : (0 : ℝ) ≤ E/40)).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [← hCdef]
    have := mul_le_mul_of_nonneg_left hexp1 (by linarith : (0 : ℝ) ≤ 2*C)
    calc C*(2*Real.exp (-(E/40)^2/2)) = 2*C*Real.exp (-(E/40)^2/2) := by ring
      _ ≤ 2*C*(1/E^2) := this
      _ = 2*C/E^2 := by ring
  have htail2 : π {y : ℝ | (E/40-10)/10 < nativeRestartExcess E y} ≤
      ENNReal.ofReal (2*C/E^2) := by
    refine (measure_pi_nativeRestart_margin_raw_tail hX hi hG hEpos hπ
      (by linarith : (0 : ℝ) ≤ (E/40-10)/10)).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [← hCdef]
    have := mul_le_mul_of_nonneg_left hexp2 (by linarith : (0 : ℝ) ≤ 2*C)
    calc C*(2*Real.exp (-((E/40-10)/10)^2/2)) =
          2*C*Real.exp (-((E/40-10)/10)^2/2) := by ring
      _ ≤ 2*C*(1/E^2) := this
      _ = 2*C/E^2 := by ring
  have henv : μ {ω | (E/40-10)/20 < nativeGaussianEnvelope X ω} ≤
      ENNReal.ofReal (nativeGaussianEnvelopeTailConstant/E^2) := by
    have hb := nativeGaussianEnvelope_tail_bound hX hi hG hv1
    have hstep : μ.real {ω | (E/40-10)/20 < nativeGaussianEnvelope X ω} ≤
        nativeGaussianEnvelopeTailConstant/E^2 := by
      refine hb.trans ?_
      have hc := mul_le_mul_of_nonneg_left hexp3
        nativeGaussianEnvelope_tail_constant_pos.le
      calc nativeGaussianEnvelopeTailConstant*Real.exp (-((E/40-10)/20)^2)
            ≤ nativeGaussianEnvelopeTailConstant*(1/E^2) := hc
        _ = nativeGaussianEnvelopeTailConstant/E^2 := by ring
    calc
      μ {ω | (E/40-10)/20 < nativeGaussianEnvelope X ω}
          = ENNReal.ofReal (μ.real {ω | (E/40-10)/20 < nativeGaussianEnvelope X ω}) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hstep
  have hmpos : π {y : ℝ | E/40 < nativeRestartMarginPos E y} ≤
      ENNReal.ofReal (2*C/E^2) + ENNReal.ofReal (nativeGaussianEnvelopeTailConstant/E^2) :=
    (measure_pi_nativeRestart_marginPos_tail hX hi hG hEpos hπ (E/40)).trans
      (add_le_add htail2 henv)
  have hwalk : ENNReal.ofReal ((∫ x, nativeRestartMean X μ E x ∂π)/(E/40)^2) ≤
      ENNReal.ofReal (1600*C/E^2) := by
    rw [← hCdef]
    apply ENNReal.ofReal_le_ofReal
    rw [div_le_div_iff₀ (by positivity) hE2]
    nlinarith
  have hfinal := (measure_prod_nativeRestart_bad_branch hX hi hG hEpos (π := π)).trans
    (add_le_add (add_le_add hmpos htail1) hwalk)
  refine hfinal.trans ?_
  have hcenv : 0 ≤ nativeGaussianEnvelopeTailConstant :=
    nativeGaussianEnvelope_tail_constant_pos.le
  have hnn1 : (0 : ℝ) ≤ 2*C/E^2 := div_nonneg (by linarith) hE2.le
  have hnn2 : (0 : ℝ) ≤ nativeGaussianEnvelopeTailConstant/E^2 := div_nonneg hcenv hE2.le
  have hnn4 : (0 : ℝ) ≤ 1600*C/E^2 := div_nonneg (by linarith) hE2.le
  rw [← ENNReal.ofReal_add hnn1 hnn2, ← ENNReal.ofReal_add (by linarith) hnn1,
    ← ENNReal.ofReal_add (by linarith) hnn4]
  apply ENNReal.ofReal_le_ofReal
  rw [stationaryBadBranchConstant]
  have key : 2*C/E^2+nativeGaussianEnvelopeTailConstant/E^2+2*C/E^2+1600*C/E^2 =
      (1604*C+nativeGaussianEnvelopeTailConstant)/E^2 := by ring
  rw [key]
  gcongr
  nlinarith [mul_nonneg hcenv (sub_nonneg.mpr hC1)]

end SwingRepair
