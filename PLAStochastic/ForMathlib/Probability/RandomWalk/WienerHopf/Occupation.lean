import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.LadderHeight

/-!
# A uniform bound for the pre-ladder occupation measure on unit intervals

For a half-line type set `A`, let `u = preEntryOccupation ρ Aᶜ`, i.e.
`u(E) = ∑ₙ P(n < τ_{Aᶜ}, S_n ∈ E)`; for `A = Iic 0` this is the pre-ladder occupation measure
`u₋` of the strict ascending ladder.

* `setLIntegral_survival_compl_eq`: time reversal, `E[g(S_n); n < τ_{Aᶜ}] = E[g(S_n); n is an
  A-ladder time]`; hence `u` counts the `A`-ladder times by position.
* `preEntryOccupation_Ioc_le`: decomposing at the first `A`-ladder time in `(x - 1, x]`, every
  unit interval has `u((x - 1, x]) ≤ u(J)` with `J = (-1, 1) ∩ (A ∪ {0})`.
* `preEntryOccupation_unitWindow_le`: `u(J) ≤ e^{|θ|} (1 - E[e^{θ S_{τ_A}}; τ_A < ∞])⁻¹`
  whenever `θ x ≤ 0` on `A`.
* `preEntryOccupation_asc_Ioc_le`: for the strict ascending ladder and `θ ≥ 0`,
  `u₋((x - 1, x]) ≤ e^{θ} (1 - E[e^{θ H₋}; τ₋ < ∞])⁻¹` for every `x`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Complex Finset
open scoped ENNReal

namespace PGM.WienerHopf

variable {ρ : Measure ℝ} [IsProbabilityMeasure ρ] {A : Set ℝ}

/-- Time reversal in `ℝ≥0∞`: `E[g(S_n); n < τ_{Aᶜ}] = E[g(S_n); S_n - S_j ∈ A ∀ j < n]`. -/
theorem setLIntegral_survival_compl_eq (hAm : MeasurableSet A) {g : ℝ → ℝ≥0∞}
    (hg : Measurable g) (n : ℕ) :
    ∫⁻ ω in {ω | (n : ℕ∞) < firstEntry Aᶜ ω}, g (partialSum n ω) ∂pathLaw ρ =
      ∫⁻ ω in {ω | IsLadderTime A n ω}, g (partialSum n ω) ∂pathLaw ρ := by
  set H : (ℕ → ℝ) → ℝ≥0∞ :=
    {ω | (n : ℕ∞) < firstEntry Aᶜ ω}.indicator fun ω => g (partialSum n ω) with hH
  have hHm : Measurable H :=
    (hg.comp (measurable_partialSum n)).indicator (measurableSet_coe_lt_firstEntry hAm.compl n)
  have hpt : ∀ ω, {ω | IsLadderTime A n ω}.indicator (fun ω => g (partialSum n ω)) ω =
      H (reverse n ω) := by
    intro ω
    have hS : partialSum n (reverse n ω) = partialSum n ω := by
      rw [partialSum_reverse le_rfl, Nat.sub_self, partialSum_zero, sub_zero]
    by_cases h : IsLadderTime A n ω
    · rw [indicator_of_mem (show ω ∈ {ω | IsLadderTime A n ω} from h), hH,
        indicator_of_mem (show reverse n ω ∈ {ω | (n : ℕ∞) < firstEntry Aᶜ ω} from
          (coe_lt_firstEntry_compl_reverse_iff ω).mpr h), hS]
    · rw [indicator_of_notMem (show ω ∉ {ω | IsLadderTime A n ω} from h), hH,
        indicator_of_notMem (show reverse n ω ∉ {ω | (n : ℕ∞) < firstEntry Aᶜ ω} from
          fun h' => h ((coe_lt_firstEntry_compl_reverse_iff ω).mp h'))]
  rw [← lintegral_indicator (measurableSet_isLadderTime hAm n),
    ← lintegral_indicator (measurableSet_coe_lt_firstEntry hAm.compl n), lintegral_congr hpt,
    ← lintegral_map hHm (measurable_reverse n), (measurePreserving_reverse n).map_eq]

/-- The occupation measure counts `A`-ladder times by position. -/
theorem preEntryOccupation_compl_apply (hAm : MeasurableSet A) {E : Set ℝ}
    (hE : MeasurableSet E) :
    preEntryOccupation ρ Aᶜ E =
      ∑' n : ℕ, pathLaw ρ {ω | IsLadderTime A n ω ∧ partialSum n ω ∈ E} := by
  rw [← lintegral_indicator_one hE, lintegral_preEntryOccupation (measurable_one.indicator hE)]
  refine tsum_congr fun n => ?_
  rw [setLIntegral_survival_compl_eq hAm (measurable_one.indicator hE) n,
    ← lintegral_indicator (measurableSet_isLadderTime hAm n)]
  have hmeasV : MeasurableSet {ω | IsLadderTime A n ω ∧ partialSum n ω ∈ E} :=
    (measurableSet_isLadderTime hAm n).inter (hE.preimage (measurable_partialSum n))
  rw [← lintegral_indicator_one hmeasV]
  refine lintegral_congr fun ω => ?_
  by_cases h1 : IsLadderTime A n ω <;> by_cases h2 : partialSum n ω ∈ E <;>
    simp [h1, h2]

theorem measurable_ennreal_tsum {α : Type*} [MeasurableSpace α] {f : ℕ → α → ℝ≥0∞}
    (h : ∀ i, Measurable (f i)) : Measurable fun x => ∑' i, f i x := by
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  exact .iSup fun s => s.measurable_fun_sum fun i _ => h i

/-! ### The first ladder visit to a set -/

open Classical in
/-- The first `A`-ladder time at which the walk is in `I` (`⊤` if none). -/
def firstLadderVisit (A I : Set ℝ) (ω : ℕ → ℝ) : ℕ∞ :=
  if h : ∃ n, IsLadderTime A n ω ∧ partialSum n ω ∈ I then ((Nat.find h : ℕ) : ℕ∞) else ⊤

theorem firstLadderVisit_eq_coe_iff {I : Set ℝ} {ω : ℕ → ℝ} {k : ℕ} :
    firstLadderVisit A I ω = k ↔ (IsLadderTime A k ω ∧ partialSum k ω ∈ I) ∧
      ∀ j < k, ¬(IsLadderTime A j ω ∧ partialSum j ω ∈ I) := by
  classical
  unfold firstLadderVisit
  split_ifs with h
  · rw [Nat.cast_inj, Nat.find_eq_iff]
  · simp only [ENat.top_ne_natCast, false_iff]
    rintro ⟨hk, -⟩
    exact h ⟨k, hk⟩

theorem measurableSet_firstLadderVisit_eq (hAm : MeasurableSet A) {I : Set ℝ}
    (hI : MeasurableSet I) (k : ℕ) :
    MeasurableSet {ω | firstLadderVisit A I ω = k} := by
  have hV : ∀ j, MeasurableSet {ω | IsLadderTime A j ω ∧ partialSum j ω ∈ I} := fun j =>
    (measurableSet_isLadderTime hAm j).inter (hI.preimage (measurable_partialSum j))
  have : {ω | firstLadderVisit A I ω = k} =
      {ω | IsLadderTime A k ω ∧ partialSum k ω ∈ I} ∩
        ⋂ j ∈ Finset.range k, {ω | IsLadderTime A j ω ∧ partialSum j ω ∈ I}ᶜ := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, Finset.mem_range, mem_compl_iff]
    exact firstLadderVisit_eq_coe_iff
  rw [this]
  exact (hV k).inter (Finset.measurableSet_biInter _ fun j _ => (hV j).compl)

theorem dependsOnPrefix_firstLadderVisit_eq {I : Set ℝ} (k : ℕ) :
    DependsOnPrefix k (fun ω => ω ∈ {ω | firstLadderVisit A I ω = k}) := by
  intro ω ω' h
  have hj : ∀ j ≤ k, (IsLadderTime A j ω ∧ partialSum j ω ∈ I ↔
      IsLadderTime A j ω' ∧ partialSum j ω' ∈ I) := fun j hj => by
    have h' : ∀ i < j, ω i = ω' i := fun i hi => h i (lt_of_lt_of_le hi hj)
    rw [isLadderTime_congr h', partialSum_congr h']
  apply propext
  simp only [mem_ofPred_eq, firstLadderVisit_eq_coe_iff]
  rw [hj k le_rfl]
  exact and_congr_right fun _ => forall_congr' fun j => imp_congr_right fun hjk => by
    rw [hj j hjk.le]

/-- The unit window `(-1, 1) ∩ (A ∪ {0})` into which later visits of a unit interval fall. -/
def unitWindow (A : Set ℝ) : Set ℝ := {y | -1 < y ∧ y < 1 ∧ (y ∈ A ∨ y = 0)}

theorem measurableSet_unitWindow (hAm : MeasurableSet A) : MeasurableSet (unitWindow A) := by
  have : unitWindow A = Set.Ioo (-1 : ℝ) 1 ∩ (A ∪ {0}) := by
    ext y; simp [unitWindow, and_assoc, or_comm]
  rw [this]
  exact measurableSet_Ioo.inter (hAm.union (measurableSet_singleton 0))

/-- A later ladder visit of `(x - 1, x]` is a ladder visit of the unit window for the path
restarted at the first visit. -/
theorem isLadderTime_shift_of_visit {I : Set ℝ} {x : ℝ} (hIx : I = Ioc (x - 1) x)
    {ω : ℕ → ℝ} {k m : ℕ} (hk : IsLadderTime A k ω ∧ partialSum k ω ∈ I)
    (hn : IsLadderTime A (k + m) ω ∧ partialSum (k + m) ω ∈ I) :
    IsLadderTime A m (shift k ω) ∧ partialSum m (shift k ω) ∈ unitWindow A := by
  subst hIx
  obtain ⟨-, hk1, hk2⟩ := hk
  obtain ⟨hL, hn1, hn2⟩ := hn
  have hsh : ∀ j, partialSum j (shift k ω) = partialSum (k + j) ω - partialSum k ω :=
    fun j => partialSum_shift k j ω
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [hsh, hsh, show partialSum (k + m) ω - partialSum k ω - (partialSum (k + j) ω -
      partialSum k ω) = partialSum (k + m) ω - partialSum (k + j) ω by ring]
    exact hL (k + j) (by omega)
  · rw [hsh]
    refine ⟨by linarith, by linarith, ?_⟩
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · right; simp
    · left; exact hL k (by omega)

theorem tsum_visits_le {I : Set ℝ} {x : ℝ} (hIx : I = Ioc (x - 1) x)
    (ω : ℕ → ℝ) :
    ∑' n : ℕ, {ω | IsLadderTime A n ω ∧ partialSum n ω ∈ I}.indicator (1 : (ℕ → ℝ) → ℝ≥0∞) ω ≤
      ∑' k : ℕ, {ω | firstLadderVisit A I ω = k}.indicator (1 : (ℕ → ℝ) → ℝ≥0∞) ω *
        ∑' m : ℕ, {ω | IsLadderTime A m ω ∧ partialSum m ω ∈ unitWindow A}.indicator
          (1 : (ℕ → ℝ) → ℝ≥0∞) (shift k ω) := by
  classical
  by_cases hex : ∃ n, IsLadderTime A n ω ∧ partialSum n ω ∈ I
  · set k₀ := Nat.find hex
    have hfv : firstLadderVisit A I ω = k₀ := by
      unfold firstLadderVisit; rw [dif_pos hex]
    have hk₀ := Nat.find_spec hex
    have hbefore : ∀ n < k₀, ¬(IsLadderTime A n ω ∧ partialSum n ω ∈ I) := fun n hn =>
      Nat.find_min hex hn
    -- the visits before `k₀` vanish; reindex the rest from `k₀`
    have hreindex : ∑' n : ℕ, {ω | IsLadderTime A n ω ∧ partialSum n ω ∈ I}.indicator
        (1 : (ℕ → ℝ) → ℝ≥0∞) ω = ∑' m : ℕ, {ω | IsLadderTime A (k₀ + m) ω ∧
          partialSum (k₀ + m) ω ∈ I}.indicator (1 : (ℕ → ℝ) → ℝ≥0∞) ω := by
      refine (Function.Injective.tsum_eq (g := fun m : ℕ => k₀ + m)
        (fun a b h => by simpa using h) ?_).symm
      intro n hn
      simp only [Function.mem_support] at hn
      by_contra hlt
      simp only [Set.mem_range, not_exists] at hlt
      have hnk : n < k₀ := by
        by_contra hge
        exact hlt (n - k₀) (by omega)
      exact hn (indicator_of_notMem (show ω ∉ {ω | IsLadderTime A n ω ∧ partialSum n ω ∈ I}
        from hbefore n hnk) _)
    rw [hreindex]
    calc ∑' m : ℕ, {ω | IsLadderTime A (k₀ + m) ω ∧ partialSum (k₀ + m) ω ∈ I}.indicator
          (1 : (ℕ → ℝ) → ℝ≥0∞) ω
        ≤ ∑' m : ℕ, {ω | IsLadderTime A m ω ∧ partialSum m ω ∈ unitWindow A}.indicator
          (1 : (ℕ → ℝ) → ℝ≥0∞) (shift k₀ ω) := by
          refine ENNReal.tsum_le_tsum fun m => ?_
          by_cases hm : IsLadderTime A (k₀ + m) ω ∧ partialSum (k₀ + m) ω ∈ I
          · rw [indicator_of_mem (show ω ∈ {ω | IsLadderTime A (k₀ + m) ω ∧
              partialSum (k₀ + m) ω ∈ I} from hm),
              indicator_of_mem (show shift k₀ ω ∈ {ω | IsLadderTime A m ω ∧
                partialSum m ω ∈ unitWindow A} from isLadderTime_shift_of_visit hIx hk₀ hm)]
            simp
          · rw [indicator_of_notMem (show ω ∉ {ω | IsLadderTime A (k₀ + m) ω ∧
              partialSum (k₀ + m) ω ∈ I} from hm)]
            exact bot_le
      _ = {ω | firstLadderVisit A I ω = k₀}.indicator (1 : (ℕ → ℝ) → ℝ≥0∞) ω *
          ∑' m : ℕ, {ω | IsLadderTime A m ω ∧ partialSum m ω ∈ unitWindow A}.indicator
            (1 : (ℕ → ℝ) → ℝ≥0∞) (shift k₀ ω) := by
          rw [indicator_of_mem (show ω ∈ {ω | firstLadderVisit A I ω = k₀} from hfv),
            Pi.one_apply, one_mul]
      _ ≤ _ := ENNReal.le_tsum (f := fun k : ℕ =>
          {ω | firstLadderVisit A I ω = k}.indicator (1 : (ℕ → ℝ) → ℝ≥0∞) ω *
            ∑' m : ℕ, {ω | IsLadderTime A m ω ∧ partialSum m ω ∈ unitWindow A}.indicator
              (1 : (ℕ → ℝ) → ℝ≥0∞) (shift k ω)) k₀
  · push Not at hex
    have : ∀ n : ℕ, {ω | IsLadderTime A n ω ∧ partialSum n ω ∈ I}.indicator
        (1 : (ℕ → ℝ) → ℝ≥0∞) ω = 0 := fun n =>
      indicator_of_notMem (fun h => hex n h.1 h.2) _
    simp only [this, tsum_zero]
    exact bot_le

/-- **Unit intervals**: `u((x - 1, x]) ≤ u((-1, 1) ∩ (A ∪ {0}))` for the occupation measure
`u = preEntryOccupation ρ Aᶜ`. -/
theorem preEntryOccupation_Ioc_le (hAm : MeasurableSet A) (x : ℝ) :
    preEntryOccupation ρ Aᶜ (Ioc (x - 1) x) ≤ preEntryOccupation ρ Aᶜ (unitWindow A) := by
  set I := Ioc (x - 1) x
  have hI : MeasurableSet I := measurableSet_Ioc
  have hJ := measurableSet_unitWindow hAm
  have hV : ∀ (E : Set ℝ), MeasurableSet E → ∀ n : ℕ,
      MeasurableSet {ω | IsLadderTime A n ω ∧ partialSum n ω ∈ E} := fun E hE n =>
    (measurableSet_isLadderTime hAm n).inter (hE.preimage (measurable_partialSum n))
  rw [preEntryOccupation_compl_apply hAm hI, preEntryOccupation_compl_apply hAm hJ]
  have hG : Measurable fun ω : ℕ → ℝ => ∑' m : ℕ,
      {ω | IsLadderTime A m ω ∧ partialSum m ω ∈ unitWindow A}.indicator
        (1 : (ℕ → ℝ) → ℝ≥0∞) ω :=
    measurable_ennreal_tsum fun m => measurable_one.indicator (hV _ hJ m)
  calc ∑' n : ℕ, pathLaw ρ {ω | IsLadderTime A n ω ∧ partialSum n ω ∈ I}
      = ∫⁻ ω, ∑' n : ℕ, {ω | IsLadderTime A n ω ∧ partialSum n ω ∈ I}.indicator
          (1 : (ℕ → ℝ) → ℝ≥0∞) ω ∂pathLaw ρ := by
        rw [lintegral_tsum fun n => (measurable_one.indicator (hV _ hI n)).aemeasurable]
        exact tsum_congr fun n => (lintegral_indicator_one (hV _ hI n)).symm
    _ ≤ ∫⁻ ω, ∑' k : ℕ, {ω | firstLadderVisit A I ω = k}.indicator (1 : (ℕ → ℝ) → ℝ≥0∞) ω *
          ∑' m : ℕ, {ω | IsLadderTime A m ω ∧ partialSum m ω ∈ unitWindow A}.indicator
            (1 : (ℕ → ℝ) → ℝ≥0∞) (shift k ω) ∂pathLaw ρ :=
        lintegral_mono fun ω => tsum_visits_le rfl ω
    _ = ∑' k : ℕ, pathLaw ρ {ω | firstLadderVisit A I ω = k} *
          ∑' m : ℕ, pathLaw ρ {ω | IsLadderTime A m ω ∧ partialSum m ω ∈ unitWindow A} := by
        rw [lintegral_tsum (f := fun (k : ℕ) ω => {ω | firstLadderVisit A I ω = (k : ℕ∞)}.indicator
          (1 : (ℕ → ℝ) → ℝ≥0∞) ω * ∑' m : ℕ, {ω | IsLadderTime A m ω ∧
            partialSum m ω ∈ unitWindow A}.indicator (1 : (ℕ → ℝ) → ℝ≥0∞) (shift k ω))
          fun k => ((measurable_one.indicator
          (measurableSet_firstLadderVisit_eq hAm hI k)).mul
          (hG.comp (measurable_shift k))).aemeasurable]
        refine tsum_congr fun k => ?_
        rw [lintegral_mul_shift (measurable_one.indicator
          (measurableSet_firstLadderVisit_eq hAm hI k))
          ((dependsOnPrefix_firstLadderVisit_eq k).indicator fun _ _ _ => rfl) hG,
          lintegral_indicator_one (measurableSet_firstLadderVisit_eq hAm hI k),
          lintegral_tsum fun m => (measurable_one.indicator (hV _ hJ m)).aemeasurable]
        congr 1
        exact tsum_congr fun m => lintegral_indicator_one (hV _ hJ m)
    _ = (∑' k : ℕ, pathLaw ρ {ω | firstLadderVisit A I ω = k}) *
          ∑' m : ℕ, pathLaw ρ {ω | IsLadderTime A m ω ∧ partialSum m ω ∈ unitWindow A} :=
        ENNReal.tsum_mul_right
    _ ≤ 1 * ∑' m : ℕ, pathLaw ρ {ω | IsLadderTime A m ω ∧ partialSum m ω ∈ unitWindow A} := by
        gcongr
        rw [← measure_iUnion (fun i j hij => Set.disjoint_left.mpr fun ω hi hj => hij (by
          simp only [mem_ofPred_eq] at hi hj; exact_mod_cast hi.symm.trans hj))
          (fun k => measurableSet_firstLadderVisit_eq hAm hI k)]
        exact prob_le_one
    _ = _ := one_mul _

/-- **The unit window has bounded occupation**:
`u((-1, 1) ∩ (A ∪ {0})) ≤ e^{|θ|} (1 - E[e^{θ S_{τ_A}}; τ_A < ∞])⁻¹` when `θ x ≤ 0` on `A`. -/
theorem preEntryOccupation_unitWindow_le (hAm : MeasurableSet A) (hA : IsLadderSet A)
    {θ : ℝ} (hθ : ∀ x ∈ A, θ * x ≤ 0) (hF : expEntryMass ρ A θ < 1) :
    preEntryOccupation ρ Aᶜ (unitWindow A) ≤
      ENNReal.ofReal (Real.exp |θ| * (1 - expEntryMass ρ A θ)⁻¹) := by
  have hJ := measurableSet_unitWindow hAm
  set d : ℕ → ℝ := fun n => ∫ ω in {ω | (n : ℕ∞) < firstEntry Aᶜ ω},
    Real.exp (θ * partialSum n ω) ∂pathLaw ρ
  have hd0 : ∀ n, 0 ≤ d n := fun n => integral_nonneg fun _ => (Real.exp_pos _).le
  have hmem : ∀ n : ℕ, ∀ ω ∈ {ω | (n : ℕ∞) < firstEntry Aᶜ ω},
      θ * partialSum n ω ≤ 0 := fun n ω hω => by
    rcases partialSum_mem_of_lt_firstEntry (B := Aᶜ) hω with h' | h'
    · exact hθ _ (by simpa using h')
    · rw [h', mul_zero]
  have hint : ∀ n : ℕ, IntegrableOn (fun ω => Real.exp (θ * partialSum n ω))
      {ω | (n : ℕ∞) < firstEntry Aᶜ ω} (pathLaw ρ) := fun n => by
    refine Measure.integrableOn_of_bounded (M := 1) (measure_ne_top _ _) (by fun_prop)
      ((ae_restrict_iff' (measurableSet_coe_lt_firstEntry hAm.compl n)).mpr
        (Filter.Eventually.of_forall fun ω hω => ?_))
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
    exact hmem n ω hω
  have hpart := sum_survival_exp_le (ρ := ρ) hAm hA hθ hF
  have hsum : Summable d := summable_of_sum_range_le hd0 hpart
  have htsum : ∑' n, d n ≤ (1 - expEntryMass ρ A θ)⁻¹ := Real.tsum_le_of_sum_range_le hd0 hpart
  -- `1_J(y) ≤ e^{|θ|} e^{θ y}` on the unit window
  have hwin : ∀ y, (unitWindow A).indicator (1 : ℝ → ℝ≥0∞) y ≤
      ENNReal.ofReal (Real.exp |θ| * Real.exp (θ * y)) := by
    intro y
    by_cases hy : y ∈ unitWindow A
    · rw [indicator_of_mem hy, Pi.one_apply, ← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← Real.exp_add, Real.one_le_exp_iff]
      obtain ⟨h1, h2, -⟩ := hy
      have : |θ * y| ≤ |θ| := by
        rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (abs_le.mpr ⟨h1.le, h2.le⟩)
      linarith [neg_abs_le (θ * y)]
    · rw [indicator_of_notMem hy]; exact bot_le
  rw [← lintegral_indicator_one hJ, lintegral_preEntryOccupation (measurable_one.indicator hJ)]
  calc ∑' n : ℕ, ∫⁻ ω in {ω | (n : ℕ∞) < firstEntry Aᶜ ω},
        (unitWindow A).indicator 1 (partialSum n ω) ∂pathLaw ρ
      ≤ ∑' n : ℕ, ∫⁻ ω in {ω | (n : ℕ∞) < firstEntry Aᶜ ω},
        ENNReal.ofReal (Real.exp |θ| * Real.exp (θ * partialSum n ω)) ∂pathLaw ρ :=
        ENNReal.tsum_le_tsum fun n => lintegral_mono fun ω => hwin _
    _ = ∑' n : ℕ, ENNReal.ofReal (Real.exp |θ| * d n) := by
        refine tsum_congr fun n => ?_
        rw [← ofReal_integral_eq_lintegral_ofReal ((hint n).const_mul _)
          (Filter.Eventually.of_forall fun _ => by positivity), integral_const_mul]
    _ = ENNReal.ofReal (∑' n, Real.exp |θ| * d n) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (Real.exp_pos _).le (hd0 n))
          (hsum.mul_left _)).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [tsum_mul_left]
        exact mul_le_mul_of_nonneg_left htsum (Real.exp_pos _).le

/-- **Uniform unit-interval bound for the strict ascending ladder** (`θ ≥ 0`):
`u₋((x - 1, x]) ≤ e^{θ} (1 - E[e^{θ H₋}; τ₋ < ∞])⁻¹` for every `x`, where
`u₋(E) = ∑ₙ P(n < τ₊, S_n ∈ E)`. -/
theorem preEntryOccupation_asc_Ioc_le {θ : ℝ} (hθ : 0 ≤ θ)
    (hF : expEntryMass ρ (Iic 0) θ < 1) (x : ℝ) :
    preEntryOccupation ρ (Ioi 0) (Ioc (x - 1) x) ≤
      ENNReal.ofReal (Real.exp θ * (1 - expEntryMass ρ (Iic 0) θ)⁻¹) := by
  have hθA : ∀ y ∈ Iic (0 : ℝ), θ * y ≤ 0 := fun y hy => mul_nonpos_of_nonneg_of_nonpos hθ hy
  have h1 := preEntryOccupation_Ioc_le (ρ := ρ) (measurableSet_Iic (a := (0 : ℝ))) x
  have h2 := preEntryOccupation_unitWindow_le (ρ := ρ) measurableSet_Iic isLadderSet_Iic hθA hF
  rw [compl_Iic, abs_of_nonneg hθ] at *
  exact h1.trans h2

end PGM.WienerHopf
