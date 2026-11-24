import PLAStochastic.Swing.ConstantEvaluation.Fluctuation.PathReversal

/-! # The duality lemma for the Gaussian ladder height (roadmap 1.3)

Let `S_n = W_n + a n` with `a > 0`, `τ = inf{n ≥ 1 : S_n > 0}` and `H_a = S_τ` the first
strict ascending ladder height.  Write `S'_m = S_{m+1} - S_1` for the walk of the shifted
increments `X_1, X_2, …`, `I' = inf_m S'_m`, and `Y = X_0 + a + I' = inf_{n≥1} S_n`.

* `{τ = m+1}` is `{S_j ≤ 0 ∀ j ≤ m} ∩ {S_{m+1} > 0}`; on it `H_a = S_{m+1}`.
* Path reversal (`lintegral_nonposPrefix_eq_terminalRecord`) turns the prefix event into
  `E_m = {S'_m ≤ S'_j ∀ j < m}` (a weak descending ladder epoch of `S'`).
* At a fixed `m`, the event `L_m = {S'_{m+i} > S'_m ∀ i ≥ 1}` is independent of
  `σ(X_0, …, X_m)` and has probability `p = P(S_i > 0 ∀ i ≥ 1)`; `E_m ∩ L_m` is exactly the
  event that `m` is the last minimiser of `S'`, which happens for exactly one `m` a.s.

Summing over `m` gives the **duality lemma**

  `p · 𝔼 f(H_a) = 𝔼 [f(Y) 1_{Y > 0}]`  for every measurable `f : ℝ → ℝ≥0∞`,

which is `eq:newconstantheightdensity` in integrated form.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-! ### The shifted walk -/

/-- `S'_m = S_{m+1} - S_1`, the drifted walk of the increments `X_1, X_2, …`. -/
def shiftWalk (X : ℕ → Ω → ℝ) (a : ℝ) (m : ℕ) (ω : Ω) : ℝ :=
  gaussianDriftWalk (fun k ω => X (1 + k) ω) 0 a m ω

/-- `I' = inf_m S'_m`, written through the maximum of the negated shifted walk. -/
def shiftInf (X : ℕ → Ω → ℝ) (a : ℝ) (ω : Ω) : ℝ :=
  -driftMaximum (fun k ω => -X (1 + k) ω) a ω

omit [MeasurableSpace Ω] in
theorem shiftWalk_zero (a : ℝ) (ω : Ω) : shiftWalk X a 0 ω = 0 := by
  simp [shiftWalk, gaussianDriftWalk, cumulativeSamples]

omit [MeasurableSpace Ω] in
theorem gaussianDriftWalk_succ_eq_shiftWalk (a : ℝ) (m : ℕ) (ω : Ω) :
    gaussianDriftWalk X 0 a (m + 1) ω = X 0 ω + a + shiftWalk X a m ω := by
  simp only [shiftWalk, gaussianDriftWalk, cumulativeSamples, Finset.sum_range_succ', zero_add,
    Nat.cast_succ]
  have : ∀ k, X (k + 1) ω = X (1 + k) ω := fun k => by rw [add_comm]
  simp only [this]
  ring

omit [MeasurableSpace Ω] in
theorem negDriftWalk_neg_shift (a : ℝ) (j : ℕ) (ω : Ω) :
    negDriftWalk (fun k ω => -X (1 + k) ω) a j ω = -shiftWalk X a j ω := by
  simp only [negDriftWalk_eq, shiftWalk, gaussianDriftWalk, cumulativeSamples,
    Finset.sum_neg_distrib, zero_add]
  ring

omit [MeasurableSpace Ω] in
/-- `S'_{m+i} - S'_m` is the walk of the increments `X_{m+1}, X_{m+2}, …`. -/
theorem shiftWalk_add_sub (a : ℝ) (m i : ℕ) (ω : Ω) :
    shiftWalk X a (m + i) ω - shiftWalk X a m ω =
      gaussianDriftWalk (fun k ω => X (1 + m + k) ω) 0 a i ω := by
  simp only [shiftWalk, gaussianDriftWalk, cumulativeSamples, zero_add]
  have hsplit := Finset.sum_range_add_sum_Ico (fun k => X (1 + k) ω) (Nat.le_add_right m i)
  have hIco : ∑ k ∈ Finset.Ico m (m + i), X (1 + k) ω = ∑ k ∈ Finset.range i, X (1 + m + k) ω := by
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [add_assoc]
  push_cast
  linarith

theorem shiftWalk_measurable (hX : ∀ n, Measurable (X n)) (a : ℝ) (m : ℕ) :
    Measurable (shiftWalk X a m) :=
  gaussianDriftWalk_measurable (fun k => hX (1 + k)) 0 a m

theorem shiftInf_measurable (hX : ∀ n, Measurable (X n)) (a : ℝ) :
    Measurable (shiftInf X a) :=
  (driftMaximum_measurable (fun k => (hX (1 + k)).neg) a).neg

omit [MeasurableSpace Ω] in
theorem shiftWalk_measurable_in {S : Set ℕ} {m : ℕ} (hS : ∀ k < m, 1 + k ∈ S) (a : ℝ) :
    Measurable[incrementIndexSpace X S] (shiftWalk X a m) := by
  let : MeasurableSpace Ω := incrementIndexSpace X S
  unfold shiftWalk gaussianDriftWalk cumulativeSamples
  apply Measurable.add_const
  apply Measurable.const_add
  exact Finset.measurable_sum _ (fun k hk => incrementIndexSpace_eval (hS k (Finset.mem_range.mp hk)))

omit [MeasurableSpace Ω] in
theorem futureWalk_measurable_in (a : ℝ) (m i : ℕ) :
    Measurable[incrementIndexSpace X (Ioi m)]
      (gaussianDriftWalk (fun k ω => X (1 + m + k) ω) 0 a i) := by
  let : MeasurableSpace Ω := incrementIndexSpace X (Ioi m)
  unfold gaussianDriftWalk cumulativeSamples
  apply Measurable.add_const
  apply Measurable.const_add
  exact Finset.measurable_sum _ (fun k _ => incrementIndexSpace_eval (show 1 + m + k ∈ Ioi m by
    simp only [mem_Ioi]; omega))

/-! ### Descending ladder epochs, the strict future, and the last minimiser -/

/-- `E_m`: `m` is a weak descending ladder epoch of `S'`. -/
def weakDescentSet (X : ℕ → Ω → ℝ) (a : ℝ) (m : ℕ) : Set Ω :=
  {ω | ∀ j < m, shiftWalk X a m ω ≤ shiftWalk X a j ω}

/-- `L_m`: after `m` the walk `S'` stays strictly above `S'_m`. -/
def strictFutureSet (X : ℕ → Ω → ℝ) (a : ℝ) (m : ℕ) : Set Ω :=
  {ω | ∀ i, 1 ≤ i → 0 < gaussianDriftWalk (fun k ω => X (1 + m + k) ω) 0 a i ω}

/-- `m` is the last minimiser of `S'`. -/
def lastMinSet (X : ℕ → Ω → ℝ) (a : ℝ) (m : ℕ) : Set Ω :=
  {ω | (∀ j, shiftWalk X a m ω ≤ shiftWalk X a j ω) ∧
    ∀ j, m < j → shiftWalk X a m ω < shiftWalk X a j ω}

/-- The walk of `X` itself stays positive at all times `≥ 1`. -/
def posWalkSet (X : ℕ → Ω → ℝ) (a : ℝ) : Set Ω :=
  {ω | ∀ i, 1 ≤ i → 0 < gaussianDriftWalk X 0 a i ω}

omit [MeasurableSpace Ω] in
theorem weakDescentSet_inter_strictFutureSet (a : ℝ) (m : ℕ) :
    weakDescentSet X a m ∩ strictFutureSet X a m = lastMinSet X a m := by
  ext ω
  simp only [weakDescentSet, strictFutureSet, lastMinSet, mem_inter_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨hE, hL⟩
    have hgt : ∀ j, m < j → shiftWalk X a m ω < shiftWalk X a j ω := by
      intro j hj
      have := hL (j - m) (by omega)
      rw [← shiftWalk_add_sub] at this
      have hmj : m + (j - m) = j := by omega
      rw [hmj] at this
      linarith
    refine ⟨fun j => ?_, hgt⟩
    rcases lt_trichotomy j m with h | h | h
    · exact hE j h
    · rw [h]
    · exact (hgt j h).le
  · rintro ⟨hall, hgt⟩
    refine ⟨fun j _ => hall j, fun i hi => ?_⟩
    rw [← shiftWalk_add_sub]
    have := hgt (m + i) (by omega)
    linarith

omit [MeasurableSpace Ω] in
theorem lastMinSet_disjoint (a : ℝ) {m m' : ℕ} (h : m ≠ m') :
    Disjoint (lastMinSet X a m) (lastMinSet X a m') := by
  rw [Set.disjoint_left]
  intro ω hm hm'
  simp only [lastMinSet, mem_ofPred_eq] at hm hm'
  rcases lt_or_gt_of_ne h with hlt | hlt
  · have h1 := hm.2 m' hlt
    have h2 := hm'.1 m
    linarith
  · have h1 := hm'.2 m hlt
    have h2 := hm.1 m'
    linarith

theorem measurableSet_weakDescentSet (hX : ∀ n, Measurable (X n)) (a : ℝ) (m : ℕ) :
    MeasurableSet (weakDescentSet X a m) := by
  have : weakDescentSet X a m = ⋂ j, ⋂ (_ : j < m), {ω | shiftWalk X a m ω ≤ shiftWalk X a j ω} := by
    ext ω; simp [weakDescentSet]
  rw [this]
  exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    measurableSet_le (shiftWalk_measurable hX a m) (shiftWalk_measurable hX a j)

theorem measurableSet_lastMinSet (hX : ∀ n, Measurable (X n)) (a : ℝ) (m : ℕ) :
    MeasurableSet (lastMinSet X a m) := by
  have : lastMinSet X a m = (⋂ j, {ω | shiftWalk X a m ω ≤ shiftWalk X a j ω}) ∩
      ⋂ j, ⋂ (_ : m < j), {ω | shiftWalk X a m ω < shiftWalk X a j ω} := by
    ext ω; simp [lastMinSet]
  rw [this]
  exact (MeasurableSet.iInter fun j =>
      measurableSet_le (shiftWalk_measurable hX a m) (shiftWalk_measurable hX a j)).inter
    (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      measurableSet_lt (shiftWalk_measurable hX a m) (shiftWalk_measurable hX a j))

omit [MeasurableSpace Ω] in
theorem weakDescentSet_measurable_in (a : ℝ) (m : ℕ) :
    MeasurableSet[incrementIndexSpace X (Iic m)] (weakDescentSet X a m) := by
  let : MeasurableSpace Ω := incrementIndexSpace X (Iic m)
  have : weakDescentSet X a m = ⋂ j, ⋂ (_ : j < m), {ω | shiftWalk X a m ω ≤ shiftWalk X a j ω} := by
    ext ω; simp [weakDescentSet]
  rw [this]
  refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun hj => measurableSet_le ?_ ?_
  · exact shiftWalk_measurable_in (fun k hk => by simp only [mem_Iic]; omega) a
  · exact shiftWalk_measurable_in (fun k hk => by simp only [mem_Iic]; omega) a

omit [MeasurableSpace Ω] in
theorem strictFutureSet_measurable_in (a : ℝ) (m : ℕ) :
    MeasurableSet[incrementIndexSpace X (Ioi m)] (strictFutureSet X a m) := by
  let : MeasurableSpace Ω := incrementIndexSpace X (Ioi m)
  have : strictFutureSet X a m = ⋂ i, ⋂ (_ : 1 ≤ i),
      {ω | 0 < gaussianDriftWalk (fun k ω => X (1 + m + k) ω) 0 a i ω} := by
    ext ω; simp [strictFutureSet]
  rw [this]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
    measurableSet_lt measurable_const (futureWalk_measurable_in a m i)

theorem measurableSet_strictFutureSet (hX : ∀ n, Measurable (X n)) (a : ℝ) (m : ℕ) :
    MeasurableSet (strictFutureSet X a m) :=
  incrementIndexSpace_le hX _ _ (strictFutureSet_measurable_in a m)

/-- The canonical positivity set on sequence space. -/
def canonicalPosWalkSet (a : ℝ) : Set (ℕ → ℝ) :=
  {v | ∀ i, 1 ≤ i → 0 < gaussianDriftWalk (fun k (w : ℕ → ℝ) => w k) 0 a i v}

theorem measurableSet_canonicalPosWalkSet (a : ℝ) : MeasurableSet (canonicalPosWalkSet a) := by
  have : canonicalPosWalkSet a = ⋂ i, ⋂ (_ : 1 ≤ i),
      {v : ℕ → ℝ | 0 < gaussianDriftWalk (fun k (w : ℕ → ℝ) => w k) 0 a i v} := by
    ext v; simp [canonicalPosWalkSet]
  rw [this]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
    measurableSet_lt measurable_const
      (gaussianDriftWalk_measurable (fun k => measurable_pi_apply k) 0 a i)

theorem measurableSet_posWalkSet (hX : ∀ n, Measurable (X n)) (a : ℝ) :
    MeasurableSet (posWalkSet X a) :=
  (measurableSet_canonicalPosWalkSet a).preimage (measurable_pi_lambda _ hX)

/-- `μ(L_m) = p` by shift invariance. -/
theorem measure_strictFutureSet (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (a : ℝ) (m : ℕ) :
    μ (strictFutureSet X a m) = μ (posWalkSet X a) := by
  obtain ⟨hX', hi', hG'⟩ := iidGaussian_shift hX hi hG (1 + m)
  have h := iidGaussian_measure_functional_eq hX' hi' hG' hX hi hG
    (measurableSet_canonicalPosWalkSet a)
  exact h

/-! ### The last minimiser exists almost surely -/

theorem lastMinSet_exists_ae (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) :
    ∀ᵐ ω ∂μ, ∃ m, ω ∈ lastMinSet X a m := by
  obtain ⟨hX', hi', hG'⟩ := iidGaussian_shift hX hi hG 1
  filter_upwards [gaussianDriftWalk_strongLaw hX' hi' hG' 0 a] with ω hω
  change Tendsto (fun n : ℕ => shiftWalk X a n ω / n) atTop (𝓝 a) at hω
  have hev : ∀ᶠ n : ℕ in atTop, a / 2 < shiftWalk X a n ω / n :=
    hω (Ioi_mem_nhds (by linarith))
  obtain ⟨N, hN⟩ := (hev.and (eventually_ge_atTop 1)).exists_forall_of_atTop
  have hpos : ∀ n, N ≤ n → 0 < shiftWalk X a n ω := by
    intro n hn
    obtain ⟨h1, h2⟩ := hN n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast h2
    have := (lt_div_iff₀ hnpos).mp h1
    nlinarith
  have hN1 : 1 ≤ N := (hN N le_rfl).2
  -- global minimisers all lie in `range N`
  set T := (Finset.range N).filter (fun n => ∀ j, shiftWalk X a n ω ≤ shiftWalk X a j ω) with hT
  have hglob : ∀ n, (∀ j, shiftWalk X a n ω ≤ shiftWalk X a j ω) → n < N := by
    intro n hn
    by_contra hcon
    push Not at hcon
    have h1 := hn 0
    rw [shiftWalk_zero] at h1
    have h2 := hpos n hcon
    linarith
  have hne : T.Nonempty := by
    obtain ⟨n₀, hn₀mem, hn₀⟩ := Finset.exists_min_image (Finset.range N)
      (fun n => shiftWalk X a n ω) ⟨0, Finset.mem_range.mpr (by omega)⟩
    refine ⟨n₀, Finset.mem_filter.mpr ⟨hn₀mem, fun j => ?_⟩⟩
    by_cases hj : j < N
    · exact hn₀ j (Finset.mem_range.mpr hj)
    · push Not at hj
      have h1 := hn₀ 0 (Finset.mem_range.mpr (by omega))
      rw [shiftWalk_zero] at h1
      exact h1.trans (hpos j hj).le
  refine ⟨T.max' hne, ?_⟩
  have hmem := Finset.max'_mem T hne
  have hmem' := Finset.mem_filter.mp hmem
  refine ⟨hmem'.2, fun j hj => ?_⟩
  by_contra hcon
  push Not at hcon
  have hjmin : ∀ i, shiftWalk X a j ω ≤ shiftWalk X a i ω := fun i => hcon.trans (hmem'.2 i)
  have hjT : j ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hglob j hjmin), hjmin⟩
  have := Finset.le_max' T j hjT
  omega

omit [MeasurableSpace Ω] in
/-- On `lastMinSet m`, `S'_m = I'`. -/
theorem shiftWalk_eq_shiftInf_of_lastMin {a : ℝ} {m : ℕ} {ω : Ω} (h : ω ∈ lastMinSet X a m) :
    shiftWalk X a m ω = shiftInf X a ω := by
  simp only [lastMinSet, mem_ofPred_eq] at h
  unfold shiftInf driftMaximum
  simp_rw [negDriftWalk_neg_shift]
  have hle : ∀ j, -shiftWalk X a j ω ≤ -shiftWalk X a m ω := fun j => neg_le_neg (h.1 j)
  have : (⨆ j, -shiftWalk X a j ω) = -shiftWalk X a m ω :=
    le_antisymm (ciSup_le hle) (le_ciSup ⟨_, forall_mem_range.mpr hle⟩ m)
  rw [this, neg_neg]

omit [MeasurableSpace Ω] in
/-- The last-minimiser indicators sum to the value at the infimum. -/
theorem tsum_lastMinSet_indicator {a : ℝ} {ω : Ω} (h : ∃ m, ω ∈ lastMinSet X a m)
    (g : ℝ → ℝ → ℝ≥0∞) :
    ∑' m : ℕ, (lastMinSet X a m).indicator (fun ω => g (X 0 ω) (shiftWalk X a m ω)) ω =
      g (X 0 ω) (shiftInf X a ω) := by
  obtain ⟨m₀, hm₀⟩ := h
  rw [tsum_eq_single m₀ (fun m hm => Set.indicator_of_notMem (fun hmem =>
    Set.disjoint_left.mp (lastMinSet_disjoint a hm) hmem hm₀) _)]
  rw [Set.indicator_of_mem hm₀, shiftWalk_eq_shiftInf_of_lastMin hm₀]

/-! ### Independence at a fixed epoch -/

theorem lintegral_lastMinSet_eq (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (a : ℝ) (m : ℕ) {g : ℝ → ℝ → ℝ≥0∞} (hg : Measurable (Function.uncurry g)) :
    ∫⁻ ω, (lastMinSet X a m).indicator (fun ω => g (X 0 ω) (shiftWalk X a m ω)) ω ∂μ =
      (∫⁻ ω, (weakDescentSet X a m).indicator (fun ω => g (X 0 ω) (shiftWalk X a m ω)) ω ∂μ) *
        μ (strictFutureSet X a m) := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  rw [← weakDescentSet_inter_strictFutureSet]
  have hpt : ∀ ω, (weakDescentSet X a m ∩ strictFutureSet X a m).indicator
      (fun ω => g (X 0 ω) (shiftWalk X a m ω)) ω =
      (weakDescentSet X a m).indicator (fun ω => g (X 0 ω) (shiftWalk X a m ω)) ω *
        (strictFutureSet X a m).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
    intro ω
    by_cases hE : ω ∈ weakDescentSet X a m <;> by_cases hL : ω ∈ strictFutureSet X a m <;>
      simp [Set.indicator, hE, hL]
  simp_rw [hpt]
  have hdis : Disjoint (Iic m) (Ioi m) := Iic_disjoint_Ioi le_rfl
  have hind : Indep (incrementIndexSpace X (Iic m)) (incrementIndexSpace X (Ioi m)) μ :=
    indep_iSup_of_disjoint (fun k => (hX k).comap_le) hi.iIndep hdis
  have hfm : Measurable[incrementIndexSpace X (Iic m)]
      ((weakDescentSet X a m).indicator (fun ω => g (X 0 ω) (shiftWalk X a m ω))) := by
    let : MeasurableSpace Ω := incrementIndexSpace X (Iic m)
    refine Measurable.indicator ?_ (weakDescentSet_measurable_in a m)
    have h0 : Measurable[incrementIndexSpace X (Iic m)] (X 0) :=
      incrementIndexSpace_eval (show 0 ∈ Iic m by simp)
    have hm := shiftWalk_measurable_in (X := X) (S := Iic m) (m := m)
      (fun k hk => by simp only [mem_Iic]; omega) a
    exact hg.comp (h0.prodMk hm)
  have hgm : Measurable[incrementIndexSpace X (Ioi m)]
      ((strictFutureSet X a m).indicator (fun _ => (1 : ℝ≥0∞))) := by
    let : MeasurableSpace Ω := incrementIndexSpace X (Ioi m)
    exact measurable_const.indicator (strictFutureSet_measurable_in a m)
  rw [lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    (incrementIndexSpace_le hX _) (incrementIndexSpace_le hX _) hind hfm hgm,
    show (∫⁻ ω, (strictFutureSet X a m).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂μ) =
      μ (strictFutureSet X a m) from
      lintegral_indicator_one (measurableSet_strictFutureSet hX a m)]

/-! ### From the ladder height to the descending epochs -/

omit [MeasurableSpace Ω] in
/-- `{τ = m+1} = {S_j ≤ 0 ∀ j ≤ m} ∩ {S_{m+1} > 0}`. -/
theorem ladderTime_eq_succ_iff (a : ℝ) (m : ℕ) (ω : Ω) :
    gaussianAscendingLadderTime X a ω = ((m + 1 : ℕ) : WithTop ℕ) ↔
      ω ∈ nonposPrefixSet X a (m + 1) ∩ {ω | 0 < gaussianDriftWalk X 0 a (m + 1) ω} := by
  rw [gaussianAscendingLadderTime, gaussianHalfLineExit_eq_succ_iff]
  simp only [gaussianHalfLineExitSlice, gaussianHalfLineSurvives, nonposPrefixSet,
    gaussianDriftWalk_reflect_neg_drift, mem_inter_iff, mem_ofPred_eq, neg_lt_zero,
    Left.nonneg_neg_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun j hj => h1 j (by omega), h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun j hj => h1 j (by omega), h2⟩

theorem lintegral_ladderHeight_eq_tsum (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) (f : ℝ → ℝ≥0∞) :
    ∫⁻ ω, f (gaussianAscendingLadderHeight X a ω) ∂μ =
      ∑' m : ℕ, ∫⁻ ω, (nonposPrefixSet X a (m + 1)).indicator
        (fun ω => (Ioi 0).indicator f (gaussianDriftWalk X 0 a (m + 1) ω)) ω ∂μ := by
  set A : ℕ → Set Ω := fun m => {ω | gaussianAscendingLadderTime X a ω = ((m + 1 : ℕ) : WithTop ℕ)}
    with hA
  have hAeq : ∀ m, A m = nonposPrefixSet X a (m + 1) ∩ {ω | 0 < gaussianDriftWalk X 0 a (m + 1) ω} := by
    intro m; ext ω; exact ladderTime_eq_succ_iff a m ω
  have hAmeas : ∀ m, MeasurableSet (A m) := by
    intro m
    rw [hAeq]
    exact (measurableSet_nonposPrefixSet hX a (m + 1)).inter
      (measurableSet_lt measurable_const (gaussianDriftWalk_measurable hX 0 a (m + 1)))
  have hdisj : Pairwise (Function.onFun Disjoint A) := by
    intro m m' hmm'
    rw [Function.onFun, Set.disjoint_left]
    intro ω h1 h2
    simp only [hA, mem_ofPred_eq] at h1 h2
    rw [h1] at h2
    have : m + 1 = m' + 1 := by exact_mod_cast h2
    exact hmm' (by omega)
  have hunion : ∀ᵐ ω ∂μ, ω ∈ ⋃ m, A m := by
    filter_upwards [gaussianAscendingLadderTime_finite_ae hX hi hG ha] with ω hω
    have hpos := gaussianAscendingLadderTime_pos (X := X) a ω
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hω
    have hn1 : 1 ≤ n := by
      rw [← hn] at hpos
      have : (0 : ℕ) < n := WithTop.coe_pos.mp hpos
      omega
    refine mem_iUnion.mpr ⟨n - 1, ?_⟩
    simp only [hA, mem_ofPred_eq]
    rw [← hn]
    have h' : n - 1 + 1 = n := by omega
    rw [h']
    rfl
  calc ∫⁻ ω, f (gaussianAscendingLadderHeight X a ω) ∂μ
      = ∫⁻ ω in ⋃ m, A m, f (gaussianAscendingLadderHeight X a ω) ∂μ := by
        rw [Measure.restrict_eq_self_of_ae_mem hunion]
    _ = ∑' m, ∫⁻ ω in A m, f (gaussianAscendingLadderHeight X a ω) ∂μ :=
        lintegral_iUnion hAmeas hdisj _
    _ = ∑' m, ∫⁻ ω in A m, (Ioi 0).indicator f (gaussianDriftWalk X 0 a (m + 1) ω) ∂μ := by
        refine tsum_congr fun m => setLIntegral_congr_fun (hAmeas m) fun ω hω => ?_
        have hτ : gaussianAscendingLadderTime X a ω = ((m + 1 : ℕ) : WithTop ℕ) := hω
        have hne : gaussianAscendingLadderTime X a ω ≠ ⊤ := by rw [hτ]; exact WithTop.coe_ne_top
        rw [gaussianAscendingLadderHeight_eq_position hne, hτ]
        have huntop : ((((m + 1 : ℕ) : WithTop ℕ)).untopD 0) = m + 1 := rfl
        rw [huntop]
        have hpos : 0 < gaussianDriftWalk X 0 a (m + 1) ω := ((hAeq m ▸ hω).2)
        rw [Set.indicator_of_mem (show gaussianDriftWalk X 0 a (m + 1) ω ∈ Ioi 0 from hpos)]
    _ = ∑' m, ∫⁻ ω, (nonposPrefixSet X a (m + 1)).indicator
          (fun ω => (Ioi 0).indicator f (gaussianDriftWalk X 0 a (m + 1) ω)) ω ∂μ := by
        refine tsum_congr fun m => ?_
        rw [← lintegral_indicator (hAmeas m)]
        refine lintegral_congr fun ω => ?_
        rw [hAeq]
        by_cases h1 : ω ∈ nonposPrefixSet X a (m + 1)
        · by_cases h2 : 0 < gaussianDriftWalk X 0 a (m + 1) ω
          · rw [Set.indicator_of_mem (show ω ∈ nonposPrefixSet X a (m + 1) ∩
                {ω | 0 < gaussianDriftWalk X 0 a (m + 1) ω} from ⟨h1, h2⟩),
              Set.indicator_of_mem h1]
          · rw [Set.indicator_of_notMem (fun h => h2 h.2), Set.indicator_of_mem h1,
              Set.indicator_of_notMem (show gaussianDriftWalk X 0 a (m + 1) ω ∉ Ioi 0 from h2)]
        · rw [Set.indicator_of_notMem (fun h => h1 h.1), Set.indicator_of_notMem h1]

omit [MeasurableSpace Ω] in
theorem terminalRecordSet_succ (a : ℝ) (m : ℕ) :
    terminalRecordSet X a (m + 1) = weakDescentSet X a m := by
  ext ω
  simp only [terminalRecordSet, weakDescentSet, mem_ofPred_eq]
  constructor
  · intro h j hj
    have := h (j + 1) (by omega) (by omega)
    rw [gaussianDriftWalk_succ_eq_shiftWalk, gaussianDriftWalk_succ_eq_shiftWalk] at this
    linarith
  · intro h k hk1 hkm
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [gaussianDriftWalk_succ_eq_shiftWalk, gaussianDriftWalk_succ_eq_shiftWalk]
    rcases lt_or_eq_of_le (show j ≤ m by omega) with hj | hj
    · linarith [h j hj]
    · rw [hj]

/-! ### The duality lemma -/

/-- **Duality lemma**: `p · 𝔼 f(H_a) = 𝔼[f(Y) 1_{Y>0}]` with `Y = X_0 + a + I'`. -/
theorem ladder_duality (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    μ (posWalkSet X a) * ∫⁻ ω, f (gaussianAscendingLadderHeight X a ω) ∂μ =
      ∫⁻ ω, (Ioi 0).indicator f (X 0 ω + a + shiftInf X a ω) ∂μ := by
  set g : ℝ → ℝ → ℝ≥0∞ := fun x s => (Ioi 0).indicator f (x + a + s) with hgdef
  have hg : Measurable (Function.uncurry g) := by
    have : Function.uncurry g = fun q : ℝ × ℝ => (Ioi 0).indicator f (q.1 + a + q.2) := by
      funext q; rfl
    rw [this]
    exact (hf.indicator measurableSet_Ioi).comp ((measurable_fst.add_const a).add measurable_snd)
  have hfi : Measurable ((Ioi 0).indicator f) := hf.indicator measurableSet_Ioi
  rw [lintegral_ladderHeight_eq_tsum hX hi hG ha f]
  -- reversal at each `m`
  have hrev : ∀ m : ℕ, ∫⁻ ω, (nonposPrefixSet X a (m + 1)).indicator
      (fun ω => (Ioi 0).indicator f (gaussianDriftWalk X 0 a (m + 1) ω)) ω ∂μ =
      ∫⁻ ω, (weakDescentSet X a m).indicator (fun ω => g (X 0 ω) (shiftWalk X a m ω)) ω ∂μ := by
    intro m
    rw [lintegral_nonposPrefix_eq_terminalRecord hX hi hG a (m + 1) hfi, terminalRecordSet_succ]
    refine lintegral_congr fun ω => ?_
    simp only [hgdef, gaussianDriftWalk_succ_eq_shiftWalk]
  simp_rw [hrev]
  rw [← ENNReal.tsum_mul_left]
  have hterm : ∀ m : ℕ, μ (posWalkSet X a) *
      ∫⁻ ω, (weakDescentSet X a m).indicator (fun ω => g (X 0 ω) (shiftWalk X a m ω)) ω ∂μ =
      ∫⁻ ω, (lastMinSet X a m).indicator (fun ω => g (X 0 ω) (shiftWalk X a m ω)) ω ∂μ := by
    intro m
    rw [lintegral_lastMinSet_eq hX hi a m hg, measure_strictFutureSet hX hi hG a m, mul_comm]
  simp_rw [hterm]
  rw [← lintegral_tsum]
  · refine lintegral_congr_ae ?_
    filter_upwards [lastMinSet_exists_ae hX hi hG ha] with ω hω
    exact tsum_lastMinSet_indicator hω g
  · intro m
    refine Measurable.aemeasurable ?_
    refine Measurable.indicator ?_ (measurableSet_lastMinSet hX a m)
    exact hg.comp ((hX 0).prodMk (shiftWalk_measurable hX a m))

end SwingRepair
