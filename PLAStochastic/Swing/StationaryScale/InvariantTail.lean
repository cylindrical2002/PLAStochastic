import PLAStochastic.Swing.StationaryScale.FavorableTail
import PLAStochastic.Swing.StationaryScale.StoppedMaximal
import PLAStochastic.Swing.StationaryScale.BranchIntegration

/-! # The fixed-state restart tails integrated against the stationary law

The fixed-state estimates of `StationaryFavorableTail`, `StationaryWald` and
`StationaryMaximum` hold for every starting carry.  This file transports them
to the invariant law `π_E` of the actual restart kernel by the product
disintegration `π_E ⊗ μ` and the invariance identity
`π_E = (π_E ⊗ μ) ∘ (x,ω) ↦ x'`.  No new probabilistic estimate is assumed.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- The joint favorable completion event: some actual final index, either
rejection direction. -/
def nativeRestartFavorableSet (X : ℕ → Ω → ℝ) (E : ℝ) : Set (ℝ × Ω) :=
  ⋃ i : Bool × ℕ, nativeRestartFavorableEventAt X E i

theorem measurableSet_nativeRestartFavorableSet (hX : ∀ j, Measurable (X j)) (E : ℝ) :
    MeasurableSet (nativeRestartFavorableSet X E) :=
  MeasurableSet.iUnion (fun i => measurableSet_nativeRestartFavorableEventAt hX E i)

/-- The negative part of the next margin, jointly in the carry and the path. -/
def nativeRestartNextExcess (X : ℕ → Ω → ℝ) (E : ℝ) (p : ℝ × Ω) : ℝ :=
  nativeRestartExcess E (nativeRestartNext X E p.1 p.2)

theorem measurable_nativeRestartNextExcess (hX : ∀ j, Measurable (X j)) (E : ℝ) :
    Measurable (nativeRestartNextExcess X E) := by
  unfold nativeRestartNextExcess nativeRestartExcess
  exact (((nativeRestartNext_measurable X hX E).abs).sub_const E).max measurable_const

theorem measurableSet_nativeRestartNextExcess_gt (hX : ∀ j, Measurable (X j))
    (E t : ℝ) : MeasurableSet {p : ℝ × Ω | t < nativeRestartNextExcess X E p} :=
  measurableSet_lt measurable_const (measurable_nativeRestartNextExcess hX E)

omit mΩ in
theorem nativeRestartFavorableSet_tail_slice (X : ℕ → Ω → ℝ) (E x t : ℝ) :
    (Prod.mk x) ⁻¹'
        (nativeRestartFavorableSet X E ∩ {p | t < nativeRestartNextExcess X E p}) =
      ⋃ i : Bool × ℕ, {ω | (x,ω) ∈ nativeRestartFavorableEventAt X E i ∧
        t < max (|nativeRestartNext X E x ω|-E) 0} := by
  ext ω
  constructor
  · rintro ⟨hmem, ht⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
    exact Set.mem_iUnion.mpr ⟨i, hi, ht⟩
  · intro hω
    obtain ⟨i, hi, ht⟩ := Set.mem_iUnion.mp hω
    exact ⟨Set.mem_iUnion.mpr ⟨i, hi⟩, ht⟩

/-- The uniform favorable tail integrated against any probability law of the
starting carry.  The constant does not depend on the law. -/
theorem measure_prod_nativeRestart_favorable_tail [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ} (hE : 0 ≤ E)
    {π : Measure ℝ} [IsProbabilityMeasure π] {t : ℝ} (ht : 0 ≤ t) :
    (π.prod μ) (nativeRestartFavorableSet X E ∩
        {p | t < nativeRestartNextExcess X E p}) ≤
      ENNReal.ofReal (Real.exp (-t^2/2)) := by
  have hms : MeasurableSet (nativeRestartFavorableSet X E ∩
      {p : ℝ × Ω | t < nativeRestartNextExcess X E p}) :=
    (measurableSet_nativeRestartFavorableSet hX E).inter
      (measurableSet_nativeRestartNextExcess_gt hX E t)
  rw [Measure.prod_apply hms]
  calc
    (∫⁻ x, μ ((Prod.mk x) ⁻¹' (nativeRestartFavorableSet X E ∩
        {p | t < nativeRestartNextExcess X E p})) ∂π)
        ≤ ∫⁻ _x : ℝ, ENNReal.ofReal (Real.exp (-t^2/2)) ∂π := by
      refine lintegral_mono fun x => ?_
      rw [nativeRestartFavorableSet_tail_slice X E x t]
      exact measure_nativeRestart_favorable_tail hX hi hG hE x ht
    _ = ENNReal.ofReal (Real.exp (-t^2/2)) := by
      rw [lintegral_const, measure_univ, mul_one]

/-! ### The invariance identity in product form -/

theorem nativeRestart_invariant_measure_eq_prod [SFinite μ]
    (hX : ∀ k, Measurable (X k)) {E : ℝ} {π : Measure ℝ} [IsProbabilityMeasure π]
    (hπ : (nativeRestartKernel X μ E).Invariant π) {B : Set ℝ} (hB : MeasurableSet B) :
    π B = (π.prod μ) ((fun p : ℝ × Ω => nativeRestartNext X E p.1 p.2) ⁻¹' B) := by
  have hnext : Measurable (fun p : ℝ × Ω => nativeRestartNext X E p.1 p.2) :=
    nativeRestartNext_measurable X hX E
  have hprod : nativeRestartKernel X μ E ∘ₘ π =
      (π.prod μ).map (fun p : ℝ × Ω => nativeRestartNext X E p.1 p.2) :=
    nativeRestartKernel_comp_eq_map_prod hX E
  have hmap : Measure.map (fun p : ℝ × Ω => nativeRestartNext X E p.1 p.2) (π.prod μ) = π := by
    rw [← hprod, hπ]
  calc
    π B = (Measure.map (fun p : ℝ × Ω => nativeRestartNext X E p.1 p.2) (π.prod μ)) B := by
      rw [hmap]
    _ = (π.prod μ) ((fun p : ℝ × Ω => nativeRestartNext X E p.1 p.2) ⁻¹' B) :=
      Measure.map_apply hnext hB

omit mΩ in
/-- The tail set of the next margin is exactly the pullback of the state tail. -/
theorem nativeRestartNextExcess_preimage (X : ℕ → Ω → ℝ) (E t : ℝ) :
    (fun p : ℝ × Ω => nativeRestartNext X E p.1 p.2) ⁻¹'
        {y | t < nativeRestartExcess E y} =
      {p : ℝ × Ω | t < nativeRestartNextExcess X E p} := rfl

/-! ### The stopped-sum tail integrated against the stationary law -/

/-- Fixed-state form of `eq:stationaryrawtail` for the actual negative margin. -/
theorem measure_nativeRestart_raw_tail_state
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E) (x : ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | t < nativeRestartExcess E (nativeRestartNext X E x ω)} ≤
      ENNReal.ofReal (nativeRestartMean X μ E x*(2*Real.exp (-t^2/2))) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hmean : 0 ≤ nativeRestartMean X μ E x := by
    have hb := nativeRestartMean_bounds hX hi hG hE x
    linarith [hb.1]
  have hsub : {ω | t < nativeRestartExcess E (nativeRestartNext X E x ω)} ≤ᵐ[μ]
      {ω | t ≤ |X (nativeRestartLengthNat X E x ω-1) ω|} := by
    filter_upwards [nativeRestartLength_ae_finite hX hi hG hE x] with ω hfin hω
    have hle := nativeRestart_margin_neg_le_increment X hE.le x ω hfin
    have hω' : t < nativeRestartExcess E (nativeRestartNext X E x ω) := hω
    exact le_of_lt (lt_of_lt_of_le hω' hle)
  have hchain := (measure_mono_ae hsub).trans
    (le_of_eq (ENNReal.ofReal_toReal
      (measure_ne_top μ {ω | t ≤ |X (nativeRestartLengthNat X E x ω-1) ω|})).symm)
  refine hchain.trans (ENNReal.ofReal_le_ofReal ?_)
  exact measureReal_nativeRestart_selected_increment_tail hX hi hG hE x ht

/-- `eq:stationaryrawtail`: the stationary negative-margin tail pays only the
mean segment length. -/
theorem measure_prod_nativeRestart_raw_tail [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E)
    {π : Measure ℝ} [IsProbabilityMeasure π] {t : ℝ} (ht : 0 ≤ t) :
    (π.prod μ) {p : ℝ × Ω | t < nativeRestartNextExcess X E p} ≤
      ENNReal.ofReal ((∫ x, nativeRestartMean X μ E x ∂π)*(2*Real.exp (-t^2/2))) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hmeas : Measurable (nativeRestartMean X μ E) := nativeRestartMean_measurable hX E
  have hbounds := nativeRestartMean_bounds hX hi hG hE
  have hnonneg : ∀ x, 0 ≤ nativeRestartMean X μ E x :=
    fun x => (by norm_num : (0 : ℝ) ≤ 1).trans (hbounds x).1
  have hupper : ∀ x, nativeRestartMean X μ E x ≤ nativeRestartMeanBound E :=
    fun x => (hbounds x).2
  have hint : Integrable (nativeRestartMean X μ E) π :=
    Doeblin.integrable_bounded_reward π hmeas hnonneg hupper
  have hintc : Integrable (fun x => nativeRestartMean X μ E x*(2*Real.exp (-t^2/2))) π :=
    hint.mul_const _
  have hms : MeasurableSet {p : ℝ × Ω | t < nativeRestartNextExcess X E p} :=
    measurableSet_nativeRestartNextExcess_gt hX E t
  rw [Measure.prod_apply hms]
  have hslice : ∀ x : ℝ, (Prod.mk x) ⁻¹' {p : ℝ × Ω | t < nativeRestartNextExcess X E p} =
      {ω | t < nativeRestartExcess E (nativeRestartNext X E x ω)} := fun x => rfl
  calc
    (∫⁻ x, μ ((Prod.mk x) ⁻¹' {p : ℝ × Ω | t < nativeRestartNextExcess X E p}) ∂π)
        ≤ ∫⁻ x, ENNReal.ofReal (nativeRestartMean X μ E x*(2*Real.exp (-t^2/2))) ∂π := by
      refine lintegral_mono fun x => ?_
      rw [hslice x]
      exact measure_nativeRestart_raw_tail_state hX hi hG hE x ht
    _ = ENNReal.ofReal (∫ x, nativeRestartMean X μ E x*(2*Real.exp (-t^2/2)) ∂π) :=
      (ofReal_integral_eq_lintegral_ofReal hintc
        (Filter.Eventually.of_forall fun x =>
          mul_nonneg (hnonneg x) (by positivity))).symm
    _ = ENNReal.ofReal ((∫ x, nativeRestartMean X μ E x ∂π)*(2*Real.exp (-t^2/2))) := by
      rw [integral_mul_const]

/-- The stationary margin tail itself, obtained from invariance. -/
theorem measure_pi_nativeRestart_margin_raw_tail [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E)
    {π : Measure ℝ} [IsProbabilityMeasure π]
    (hπ : (nativeRestartKernel X μ E).Invariant π) {t : ℝ} (ht : 0 ≤ t) :
    π {y | t < nativeRestartExcess E y} ≤
      ENNReal.ofReal ((∫ x, nativeRestartMean X μ E x ∂π)*(2*Real.exp (-t^2/2))) := by
  have hB : MeasurableSet {y : ℝ | t < nativeRestartExcess E y} := by
    unfold nativeRestartExcess
    exact measurableSet_lt measurable_const
      ((measurable_id.abs.sub_const E).max measurable_const)
  rw [nativeRestart_invariant_measure_eq_prod hX hπ hB, nativeRestartNextExcess_preimage]
  exact measure_prod_nativeRestart_raw_tail hX hi hG hE ht

/-! ### The refined stationary tail

Splitting the pullback along the favorable completion event gives
`eq:stationaryrefinedtail`: a branch-free Gaussian factor plus the measure of
the complementary branch, and separately the stopped-sum alternative.
-/

theorem measure_pi_nativeRestart_margin_refined_tail [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E)
    {π : Measure ℝ} [IsProbabilityMeasure π]
    (hπ : (nativeRestartKernel X μ E).Invariant π) {t : ℝ} (ht : 0 ≤ t) :
    π {y | t < nativeRestartExcess E y} ≤
      ENNReal.ofReal (Real.exp (-t^2/2)) +
        (π.prod μ) (nativeRestartFavorableSet X E)ᶜ := by
  have hB : MeasurableSet {y : ℝ | t < nativeRestartExcess E y} := by
    unfold nativeRestartExcess
    exact measurableSet_lt measurable_const
      ((measurable_id.abs.sub_const E).max measurable_const)
  rw [nativeRestart_invariant_measure_eq_prod hX hπ hB, nativeRestartNextExcess_preimage]
  have hsplit : {p : ℝ × Ω | t < nativeRestartNextExcess X E p} ⊆
      (nativeRestartFavorableSet X E ∩ {p | t < nativeRestartNextExcess X E p}) ∪
        (nativeRestartFavorableSet X E)ᶜ := by
    intro p hp
    by_cases hg : p ∈ nativeRestartFavorableSet X E
    · exact Or.inl ⟨hg, hp⟩
    · exact Or.inr hg
  calc
    (π.prod μ) {p : ℝ × Ω | t < nativeRestartNextExcess X E p}
        ≤ (π.prod μ) ((nativeRestartFavorableSet X E ∩
            {p | t < nativeRestartNextExcess X E p}) ∪
              (nativeRestartFavorableSet X E)ᶜ) := measure_mono hsplit
    _ ≤ (π.prod μ) (nativeRestartFavorableSet X E ∩
            {p | t < nativeRestartNextExcess X E p}) +
          (π.prod μ) (nativeRestartFavorableSet X E)ᶜ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-t^2/2)) +
          (π.prod μ) (nativeRestartFavorableSet X E)ᶜ :=
      add_le_add (measure_prod_nativeRestart_favorable_tail hX hi hG hE.le ht) le_rfl

end SwingRepair
