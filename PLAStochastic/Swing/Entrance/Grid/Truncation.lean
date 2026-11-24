import PLAStochastic.Swing.Entrance.Grid.Coupling
import PLAStochastic.Swing.Entrance.Grid.Measurability
import PLAStochastic.Swing.FrozenCarry.Interior.GoodTail
import Mathlib.MeasureTheory.Integral.Indicator

/-!
# High probability of the truncation event, (E7)

For every `ε > 0` there are `δ > 0` and `M` such that, for all large budgets `E`,
`P(¬ entranceGood (entrancePath X ·) E δ M) ≤ ε`, where `entranceGood` is the `𝓕_τ`-measurable
event `δ E² ≤ τ ≤ M E²`, `|E β| ≤ M`, `d_E/2 ≤ D ≤ d_E` (review item G3). The proof:

* the macroscopic part `δ E² ≤ τ ≤ M E²`, `|E β| ≤ M` follows from the almost sure limits
  `τ/E² → σ ∈ (0, ∞)` and `E β → m_*` under the exact Brownian coupling, by dominated
  convergence, once `δ` and `M` are chosen from the laws of `σ` and `m_*`;
* deterministically, the macroscopic part and `|X_{τ-1}| ≤ d_E/4` give
  `D = D_prev + β̃ - X̃_τ > d_E - d_E/4 - d_E/4` by (E8);
* a union bound over the first `M E² + 1` standard Gaussian increments makes
  `max |X_i| > d_E/4` have probability at most `(M E² + 1) · 2 exp(-√E/32) → 0`.

The event depends only on the increment sequence, so the bound holds for every iid standard
Gaussian increment sequence (`entranceGood_prob_gaussian`).
-/

open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology

namespace SwingRepair

noncomputable section

/-- The macroscopic part of the truncation event: a finite cut with `δ E² ≤ τ ≤ M E²` and
`|E β| ≤ M`. -/
def entranceMacroGood (y : ℕ → ℝ) (E δ M : ℝ) : Prop :=
  ∃ n : ℕ, entranceCut y E = n ∧ δ * E ^ 2 ≤ n ∧ (n : ℝ) ≤ M * E ^ 2 ∧
    |E * entranceFrozenSlope y E n| ≤ M

/-- The macroscopic truncation and a small increment at the cut give `d_E/2 ≤ D ≤ d_E`. -/
theorem entranceGood_of_macroGood {y : ℕ → ℝ} {E δ M : ℝ} (hy0 : y 0 = 0) (hE : 1 ≤ E)
    (hM : 4 * M ≤ E) {n : ℕ} (hn : entranceCut y E = n) (hδ : δ * E ^ 2 ≤ n)
    (hnM : (n : ℝ) ≤ M * E ^ 2) (hβ : |E * entranceFrozenSlope y E n| ≤ M)
    (hinc : |y n - y (n - 1)| ≤ entranceCutLevel E / 4) : entranceGood y E δ M := by
  have hE0 : 0 ≤ E := by linarith
  have h2E := entranceCutLevel_lt_two_mul hE
  refine ⟨n, hn, hδ, hnM, hβ, ?_, entranceCut_width_le hn⟩
  have hstep := entranceCut_width_step hy0 hE0 h2E hn
  have hprev := entranceCut_reflected_prev hy0 hE0 h2E hn
  have hd1 : 1 ≤ entranceCutLevel E := Real.one_le_rpow hE (by norm_num)
  have hs : |entranceSide y E n| = 1 := abs_entranceSide n
  have hEpos : 0 < E := by linarith
  have hβE : |entranceFrozenSlope y E n| ≤ 1 / 4 := by
    have h1 : E * |entranceFrozenSlope y E n| ≤ M := by
      rwa [abs_mul, abs_of_pos hEpos] at hβ
    by_contra h
    push Not at h
    nlinarith
  have hsβ : |entranceSide y E n * entranceFrozenSlope y E n| ≤ entranceCutLevel E / 4 := by
    rw [abs_mul, hs, one_mul]
    linarith
  have hsy : |entranceSide y E n * y n - entranceSide y E n * y (n - 1)| ≤
      entranceCutLevel E / 4 := by
    rw [← mul_sub, abs_mul, hs, one_mul]
    exact hinc
  have h1 := neg_abs_le (entranceSide y E n * entranceFrozenSlope y E n)
  have h2 := le_abs_self (entranceSide y E n * y n - entranceSide y E n * y (n - 1))
  rw [hstep]
  linarith

theorem measurableSet_entranceMacroGood {Ω : Type*} [MeasurableSpace Ω] {Y : Ω → ℕ → ℝ}
    (hY : ∀ n, Measurable fun ω => Y ω n) (E δ M : ℝ) :
    MeasurableSet {ω | entranceMacroGood (Y ω) E δ M} := by
  rw [measurableSet_setOfPred]
  unfold entranceMacroGood
  refine Measurable.exists fun n => ?_
  refine (measurableSet_setOfPred.mp (measurableSet_entranceCut_eq hY E n)).and
    (measurable_const.and (measurable_const.and ?_))
  exact measurableSet_setOfPred.mp (measurableSet_le
    (measurable_const.mul (measurable_entranceFrozenSlope hY E n)).abs measurable_const)

/-- The Gaussian union bound `(M x² + 1) · 2 exp(-(x^{1/4}/4)²/2)` tends to zero. -/
theorem tendsto_entranceTailBound (M : ℝ) :
    Tendsto (fun x : ℝ => (M * x ^ 2 + 1) * (2 * Real.exp (-(entranceCutLevel x / 4) ^ 2 / 2)))
      atTop (𝓝 0) := by
  set g : ℝ → ℝ := fun w => (M * 32 ^ 4 * w ^ 4 + 1) * (2 * Real.exp (-w)) with hg
  have hgl : Tendsto g atTop (𝓝 0) := by
    have h4 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4
    have h0 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0
    have h := (h4.const_mul (2 * M * 32 ^ 4)).add (h0.const_mul 2)
    simp only [mul_zero, add_zero] at h
    refine h.congr fun w => ?_
    simp only [hg, pow_zero, one_mul]
    ring
  have hv : Tendsto (fun x : ℝ => x ^ (1 / 4 : ℝ)) atTop atTop := tendsto_rpow_atTop (by norm_num)
  have hw : Tendsto (fun x : ℝ => (x ^ (1 / 4 : ℝ)) ^ 2 / 32) atTop atTop :=
    ((tendsto_pow_atTop two_ne_zero).comp hv).atTop_div_const (by norm_num)
  apply (hgl.comp hw).congr'
  filter_upwards [eventually_ge_atTop 0] with x hx
  have hx8 : (x ^ (1 / 4 : ℝ)) ^ 8 = x ^ 2 := by
    rw [← Real.rpow_mul_natCast hx]
    norm_num
  unfold entranceCutLevel
  simp only [Function.comp_apply, hg]
  rw [← hx8]
  have he : -(x ^ (1 / 4 : ℝ) / 4) ^ 2 / 2 = -((x ^ (1 / 4 : ℝ)) ^ 2 / 32) := by ring
  rw [he]
  ring

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- Union bound for the first `⌊M E²⌋₊ + 1` coupled increments exceeding `d_E / 4`. -/
theorem measure_coupled_increment_tail_le (hB : IsBrownianReal B μ) {E : ℝ≥0} (hE : 1 ≤ E)
    {M : ℝ} (hM : 0 ≤ M) :
    μ (⋃ i ∈ Finset.range (⌊M * (E : ℝ) ^ 2⌋₊ + 1),
        {ω | entranceCutLevel E / 4 < |normalizedMeshIncrement B (gaussianBudgetMesh E) i ω|}) ≤
      ENNReal.ofReal ((M * (E : ℝ) ^ 2 + 1) *
        (2 * Real.exp (-(entranceCutLevel E / 4) ^ 2 / 2))) := by
  have : IsProbabilityMeasure μ := hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  set z := entranceCutLevel E / 4
  have hz : 0 ≤ z := div_nonneg (entranceCutLevel_nonneg E.coe_nonneg) (by norm_num)
  set c := 2 * Real.exp (-z ^ 2 / 2)
  have hone : ∀ i, μ {ω | z < |normalizedMeshIncrement B (gaussianBudgetMesh E) i ω|} ≤
      ENNReal.ofReal c := by
    intro i
    have hL := normalizedMeshIncrement_hasLaw hB.toIsPreBrownianReal (gaussianBudgetMesh E)
      (gaussianBudgetMesh_ne_zero hE) i
    have hm : MeasurableSet {x : ℝ | z ≤ |x|} := measurableSet_le measurable_const measurable_abs
    calc μ {ω | z < |normalizedMeshIncrement B (gaussianBudgetMesh E) i ω|}
        ≤ μ {ω | z ≤ |normalizedMeshIncrement B (gaussianBudgetMesh E) i ω|} :=
          measure_mono fun ω hω => by
            simp only [mem_ofPred_eq] at hω ⊢
            exact hω.le
      _ = gaussianReal 0 1 {x : ℝ | z ≤ |x|} := hL.measure_eq (p := fun x => z ≤ |x|) hm
      _ = ENNReal.ofReal ((gaussianReal 0 1).real {x : ℝ | z ≤ |x|}) :=
          (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal c := by
          apply ENNReal.ofReal_le_ofReal
          have := gaussianReal_absolute_tail_bound 1 hz
          simpa only [NNReal.coe_one, mul_one] using this
  have hc : 0 ≤ c := by positivity
  calc μ (⋃ i ∈ Finset.range (⌊M * (E : ℝ) ^ 2⌋₊ + 1),
        {ω | z < |normalizedMeshIncrement B (gaussianBudgetMesh E) i ω|})
      ≤ ∑ i ∈ Finset.range (⌊M * (E : ℝ) ^ 2⌋₊ + 1),
          μ {ω | z < |normalizedMeshIncrement B (gaussianBudgetMesh E) i ω|} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ i ∈ Finset.range (⌊M * (E : ℝ) ^ 2⌋₊ + 1), ENNReal.ofReal c :=
        Finset.sum_le_sum fun i _ => hone i
    _ = ENNReal.ofReal (((⌊M * (E : ℝ) ^ 2⌋₊ + 1 : ℕ) : ℝ) * c) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ENNReal.ofReal_mul (p := ((⌊M * (E : ℝ) ^ 2⌋₊ + 1 : ℕ) : ℝ)) (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((M * (E : ℝ) ^ 2 + 1) * c) := by
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_right _ hc
        push_cast
        have := Nat.floor_le (show 0 ≤ M * (E : ℝ) ^ 2 by positivity)
        linarith

/-- (E7) under the exact Brownian coupling: the truncation event has probability at least
`1 - ε` for all large budgets. -/
theorem entranceGood_coupled_prob (hB : IsBrownianReal B μ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ > 0, ∃ M : ℝ, ∀ᶠ E : ℝ≥0 in atTop,
      μ {ω | ¬ entranceGood (entrancePath (normalizedMeshIncrement B (gaussianBudgetMesh E)) ω)
        E δ M} ≤ ε := by
  have : IsProbabilityMeasure μ := hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hε3 : 0 < ε / 3 := ENNReal.div_pos_iff.mpr ⟨hε.ne', by norm_num⟩
  -- a measurable version of the coupled grid path
  set Z : ℝ≥0 → Ω → ℕ → ℝ := fun E ω => entranceGridPath (continuousBrownianPath hB ω) E with hZdef
  have hZ : ∀ E n, Measurable fun ω => Z E ω n := fun E n =>
    measurable_const.mul ((continuous_eval_const _).measurable.comp
      (measurable_continuousBrownianPath hB))
  have hYZ : ∀ᵐ ω ∂μ, ∀ E : ℝ≥0,
      entrancePath (normalizedMeshIncrement B (gaussianBudgetMesh E)) ω = Z E ω := by
    filter_upwards [continuousBrownianPath_ae_eq hB, hB.cont, hB.eval_zero_ae_eq_zero]
      with ω hW hc hz E
    rw [entrancePath_normalizedMesh B E ω hc hz, hZdef]
    simp only
    rw [hW]
  have hlim := entrance_coupled_limits_ae hB
  -- measurable versions of the pinch `σ` and the slope `m_*`
  have hσ : AEMeasurable (fun ω => entrancePinch (processPath B ω)) μ := by
    refine aemeasurable_of_tendsto_metrizable_ae'
      (f := fun (k : ℕ) ω => ((entranceCut (Z k ω) ((k : ℝ≥0) : ℝ)).toNat : ℝ) /
        ((k : ℝ≥0) : ℝ) ^ 2) (fun k => ?_) ?_
    · exact (measurable_at_entranceCut (hZ k) ((k : ℝ≥0) : ℝ)
        (g := fun j _ => (j : ℝ) / ((k : ℝ≥0) : ℝ) ^ 2) (fun _ => measurable_const)).aemeasurable
    · filter_upwards [hlim, hYZ] with ω hω hω'
      have h := hω.2.1.comp tendsto_natCast_atTop_atTop
      simp only [Function.comp_def, hω'] at h
      exact h
  have hm : AEMeasurable (fun ω => entranceSlope (processPath B ω)) μ := by
    refine aemeasurable_of_tendsto_metrizable_ae'
      (f := fun (k : ℕ) ω => ((k : ℝ≥0) : ℝ) * entranceFrozenSlope (Z k ω) ((k : ℝ≥0) : ℝ)
        (entranceCut (Z k ω) ((k : ℝ≥0) : ℝ)).toNat) (fun k => ?_) ?_
    · exact (measurable_at_entranceCut (hZ k) ((k : ℝ≥0) : ℝ)
        (g := fun j ω => ((k : ℝ≥0) : ℝ) * entranceFrozenSlope (Z k ω) ((k : ℝ≥0) : ℝ) j)
        (fun j => measurable_const.mul (measurable_entranceFrozenSlope (hZ k) _ j))).aemeasurable
    · filter_upwards [hlim, hYZ] with ω hω hω'
      have h := hω.2.2.2.2.1.comp tendsto_natCast_atTop_atTop
      simp only [Function.comp_def, hω'] at h
      exact h
  set σ' := hσ.mk _ with hσ'def
  set m' := hm.mk _ with hm'def
  -- choose the truncation levels from the laws of `σ` and `m_*`
  set Lc : ℕ → Set Ω := fun k =>
    {ω | ¬ ((1 : ℝ) / (k + 1) < σ' ω ∧ σ' ω < k ∧ |m' ω| < k)} with hLcdef
  have hLc_meas : ∀ k, MeasurableSet (Lc k) := by
    intro k
    rw [hLcdef, measurableSet_setOfPred]
    refine Measurable.not (Measurable.and ?_ (Measurable.and ?_ ?_))
    · exact measurableSet_setOfPred.mp (measurableSet_lt measurable_const hσ.measurable_mk)
    · exact measurableSet_setOfPred.mp (measurableSet_lt hσ.measurable_mk measurable_const)
    · exact measurableSet_setOfPred.mp (measurableSet_lt hm.measurable_mk.abs measurable_const)
  have hLc_anti : Antitone Lc := by
    intro k k' hkk' ω hω h
    apply hω
    have hk : (k : ℝ) ≤ k' := by exact_mod_cast hkk'
    refine ⟨lt_of_le_of_lt ?_ h.1, h.2.1.trans_le hk, h.2.2.trans_le hk⟩
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hLc_inter : μ (⋂ k, Lc k) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [EntranceRegular.ae_brownian hB, hσ.ae_eq_mk] with ω hreg hσω
    obtain ⟨_, _, σ, hr⟩ := hreg
    have hpos : 0 < σ' ω := by
      rw [hσ'def, ← hσω, hr.pinch_eq]
      exact hr.pos_real
    obtain ⟨k, hk⟩ := exists_nat_gt (max (1 / σ' ω) (max (σ' ω) |m' ω|))
    intro hω
    apply mem_iInter.mp hω k
    refine ⟨?_, (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hk),
      (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hk)⟩
    rw [one_div_lt (by positivity) hpos]
    linarith [(le_max_left _ _).trans_lt hk]
  have hLc_lim : Tendsto (fun k => μ (Lc k)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (fun k => (hLc_meas k).nullMeasurableSet) hLc_anti
      ⟨0, measure_ne_top μ _⟩
    rw [hLc_inter] at h
    exact h
  obtain ⟨k, hk⟩ := ((tendsto_order.1 hLc_lim).2 _ hε3).exists
  refine ⟨1 / ((k : ℝ) + 1), by positivity, (k : ℝ), ?_⟩
  set δ : ℝ := 1 / ((k : ℝ) + 1) with hδdef
  set M : ℝ := (k : ℝ) with hMdef
  have hM0 : 0 ≤ M := Nat.cast_nonneg k
  -- the macroscopic failure has vanishing probability on `(Lc k)ᶜ`
  set As : ℝ≥0 → Set Ω := fun E => {ω | ¬ entranceMacroGood (Z E ω) E δ M} ∩ (Lc k)ᶜ
    with hAsdef
  have hAs_meas : ∀ E, MeasurableSet (As E) := fun E =>
    (measurableSet_entranceMacroGood (hZ E) E δ M).compl.inter (hLc_meas k).compl
  have hAs_lim : Tendsto (fun E => μ (As E)) atTop (𝓝 0) := by
    have h := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure (μ := μ) (L := atTop)
      (A := (∅ : Set Ω)) MeasurableSet.empty hAs_meas ?_
    · rwa [measure_empty] at h
    filter_upwards [hlim, hYZ, hσ.ae_eq_mk, hm.ae_eq_mk] with ω hω hω' hσω hmω
    obtain ⟨hfin, hcut, _, _, hfrozen, _⟩ := hω
    simp only [hω'] at hfin hcut hfrozen
    by_cases hL : ω ∈ Lc k
    · exact Eventually.of_forall fun E => by simp [hAsdef, hL]
    · have hL' : (1 : ℝ) / (k + 1) < σ' ω ∧ σ' ω < k ∧ |m' ω| < k := by
        simpa [hLcdef] using hL
      rw [hσ'def, ← hσω] at hL'
      rw [hm'def, ← hmω] at hL'
      have habs := ((continuous_abs.tendsto _).comp hfrozen).eventually_lt_const hL'.2.2
      filter_upwards [hfin, hcut.eventually_const_lt hL'.1, hcut.eventually_lt_const hL'.2.1,
        habs, eventually_ge_atTop 1] with E hf hlo hhi hab hE1
      have hEpos : (0 : ℝ) < (E : ℝ) ^ 2 := by
        have : (1 : ℝ) ≤ E := by exact_mod_cast hE1
        positivity
      have hmg : entranceMacroGood (Z E ω) E δ M := by
        refine ⟨(entranceCut (Z E ω) E).toNat, (ENat.natCast_toNat hf).symm, ?_, ?_, ?_⟩
        · have := (lt_div_iff₀ hEpos).mp hlo
          exact this.le
        · have := (div_lt_iff₀ hEpos).mp hhi
          exact this.le
        · exact hab.le
      simp only [mem_empty_iff_false, iff_false]
      exact fun h => h.1 hmg
  -- the increment tail has vanishing probability
  have htail_lim : Tendsto (fun E : ℝ≥0 => ENNReal.ofReal ((M * (E : ℝ) ^ 2 + 1) *
      (2 * Real.exp (-(entranceCutLevel E / 4) ^ 2 / 2)))) atTop (𝓝 0) := by
    have h := ENNReal.tendsto_ofReal ((tendsto_entranceTailBound M).comp
      (NNReal.tendsto_coe_atTop.mpr tendsto_id))
    rw [ENNReal.ofReal_zero] at h
    exact h
  filter_upwards [(tendsto_order.1 hAs_lim).2 _ hε3, (tendsto_order.1 htail_lim).2 _ hε3,
    eventually_ge_atTop 1, eventually_ge_atTop (4 * k : ℝ≥0)] with E hAs htail hE1 hE4
  have hE1' : (1 : ℝ) ≤ E := by exact_mod_cast hE1
  have hE4' : 4 * M ≤ E := by
    have : ((4 * k : ℝ≥0) : ℝ) ≤ E := by exact_mod_cast hE4
    simpa [hMdef] using this
  set X := normalizedMeshIncrement B (gaussianBudgetMesh E) with hXdef
  set T := ⋃ i ∈ Finset.range (⌊M * (E : ℝ) ^ 2⌋₊ + 1),
    {ω | entranceCutLevel E / 4 < |X i ω|} with hTdef
  -- deterministic inclusion
  have hsub : {ω | ¬ entranceGood (entrancePath X ω) E δ M} ⊆
      {ω | ¬ entranceMacroGood (entrancePath X ω) E δ M} ∪ T := by
    intro ω hω
    by_contra hcon
    simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hcon
    obtain ⟨⟨n, hn, hδn, hnM, hβ⟩, hT⟩ := hcon
    apply hω
    have h2 := entranceCut_ge_two (entranceCutLevel_lt_two_mul hE1') hn
    refine entranceGood_of_macroGood (cumulativeSamples_zero X ω) hE1' hE4' hn hδn hnM hβ ?_
    have hstep : entrancePath X ω n - entrancePath X ω (n - 1) = X (n - 1) ω := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      simp only [entrancePath, Nat.add_sub_cancel, cumulativeSamples_succ]
      ring
    rw [hstep]
    have hmem : n - 1 ∈ Finset.range (⌊M * (E : ℝ) ^ 2⌋₊ + 1) := by
      have := Nat.le_floor hnM
      rw [Finset.mem_range]
      omega
    by_contra hbig
    push Not at hbig
    exact hT (mem_biUnion hmem hbig)
  have hmacro : μ {ω | ¬ entranceMacroGood (entrancePath X ω) E δ M} =
      μ {ω | ¬ entranceMacroGood (Z E ω) E δ M} := by
    apply measure_congr
    filter_upwards [hYZ] with ω hω
    change (¬ entranceMacroGood (entrancePath (normalizedMeshIncrement B (gaussianBudgetMesh E)) ω)
      E δ M) = (¬ entranceMacroGood (Z E ω) E δ M)
    rw [hω E]
  calc μ {ω | ¬ entranceGood (entrancePath X ω) E δ M}
      ≤ μ ({ω | ¬ entranceMacroGood (entrancePath X ω) E δ M} ∪ T) := measure_mono hsub
    _ ≤ μ {ω | ¬ entranceMacroGood (entrancePath X ω) E δ M} + μ T := measure_union_le _ _
    _ ≤ (μ (As E) + μ (Lc k)) + μ T := by
        rw [hmacro]
        gcongr
        calc μ {ω | ¬ entranceMacroGood (Z E ω) E δ M} ≤ μ (As E ∪ Lc k) := by
              apply measure_mono
              intro ω hω
              by_cases hL : ω ∈ Lc k
              · exact Or.inr hL
              · exact Or.inl ⟨hω, hL⟩
          _ ≤ μ (As E) + μ (Lc k) := measure_union_le _ _
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by
        exact add_le_add (add_le_add hAs.le hk.le)
          ((measure_coupled_increment_tail_le hB hE1 hM0).trans htail.le)
    _ = ε := ENNReal.add_thirds ε

/-- (E7) for an arbitrary iid standard Gaussian increment sequence: the truncation event is an
event of the increment law, which is the law of the coupled Brownian mesh increments. -/
theorem entranceGood_prob_gaussian {Ξ : Type*} [MeasurableSpace Ξ] {ν : Measure Ξ}
    {X : ℕ → Ξ → ℝ} (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X ν)
    (hG : ∀ n, ν.map (X n) = gaussianReal 0 1) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ > 0, ∃ M : ℝ, ∀ᶠ E : ℝ≥0 in atTop,
      ν {ξ | ¬ entranceGood (entrancePath X ξ) E δ M} ≤ ε := by
  obtain ⟨δ, hδ, M, hev⟩ := entranceGood_coupled_prob isBrownianReal_canonicalBrownian hε
  refine ⟨δ, hδ, M, ?_⟩
  filter_upwards [hev, eventually_ge_atTop 1] with E hE hE1
  have hseq := identDistrib_gaussian_mesh_sequence (fun n => (hX n).aemeasurable) hi hG
    isBrownianReal_canonicalBrownian.toIsPreBrownianReal (gaussianBudgetMesh E)
    (gaussianBudgetMesh_ne_zero hE1)
  have hcoord : ∀ n, Measurable fun x : ℕ → ℝ => entrancePath (fun (k : ℕ) (x : ℕ → ℝ) => x k) x n := by
    intro n
    change Measurable fun x : ℕ → ℝ => ∑ k ∈ Finset.range n, x k
    exact Finset.measurable_sum _ fun k _ => measurable_pi_apply k
  have hS := (measurableSet_entranceGood hcoord (E : ℝ) δ M).compl
  have heq := ProbabilityTheory.IdentDistrib.measure_mem_eq hseq hS
  calc ν {ξ | ¬ entranceGood (entrancePath X ξ) E δ M}
      = ν ((fun ξ n => X n ξ) ⁻¹'
          {x : ℕ → ℝ | entranceGood (entrancePath (fun (k : ℕ) (x : ℕ → ℝ) => x k) x) E δ M}ᶜ) := rfl
    _ = canonicalPreBrownianMeasure ((fun ω n => normalizedMeshIncrement canonicalBrownian
          (gaussianBudgetMesh E) n ω) ⁻¹'
          {x : ℕ → ℝ | entranceGood (entrancePath (fun (k : ℕ) (x : ℕ → ℝ) => x k) x) E δ M}ᶜ) := heq
    _ ≤ ε := hE

end

end SwingRepair
