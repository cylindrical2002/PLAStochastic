import PLAStochastic.Swing.StationaryLimit.Slope.Limiting

/-! # Early-slope localization

`eq:earlyslopelocalization` localizes the random slope `A_r` of `app:limit` in
the first `J` observations, uniformly over `|r| ≤ K₀`: on an event of
probability close to one the infinite supremum is attained inside the prefix
and lies in a fixed compact positive interval `[2δ,M]`.

The deterministic half is exact: the prefix maximum, the prefix bound at the
two extreme margins and the sublinear tail estimate force `A_r = A_{r,J}` for
every `|r| ≤ K₀` simultaneously.  The probabilistic half chooses the three
constants in the paper's order from the already-proved positivity of `A_r` and
the strong law.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*}

/-- The `n`-th slope ratio of `eq:leadingslope`, with the paper's index shift
`i = n+1`. -/
def swingSlopeTerm (X : ℕ → Ω → ℝ) (r : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (cumulativeSamples X n ω - r)/((n : ℝ)+1)

/-- `A_{r,J}`: the maximum of the slope ratios over the first `J+1` indices. -/
def swingEarlySlope (X : ℕ → Ω → ℝ) (r : ℝ) : ℕ → Ω → ℝ
  | 0 => swingSlopeTerm X r 0
  | (J+1) => fun ω => max (swingEarlySlope X r J ω) (swingSlopeTerm X r (J+1) ω)

/-- The sublinear tail quantity of `eq:earlyslopelocalization`. -/
def swingSlopeTail (X : ℕ → Ω → ℝ) (K₀ : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (|cumulativeSamples X n ω| + K₀)/((n : ℝ)+1)

theorem swingSlopeTerm_le_tail (X : ℕ → Ω → ℝ) {K₀ r : ℝ} (hr : |r| ≤ K₀) (n : ℕ) (ω : Ω) :
    swingSlopeTerm X r n ω ≤ swingSlopeTail X K₀ n ω := by
  have hpos : (0 : ℝ) < (n : ℝ)+1 := by positivity
  refine div_le_div_of_nonneg_right ?_ hpos.le
  have h1 : cumulativeSamples X n ω ≤ |cumulativeSamples X n ω| := le_abs_self _
  have h2 : -r ≤ K₀ := by
    have := neg_le_of_neg_le ((neg_le_abs r).trans hr)
    linarith [(neg_abs_le r).trans (le_refl _), abs_le.mp hr |>.1]
  linarith

theorem swingSlopeTerm_le_swingEarlySlope (X : ℕ → Ω → ℝ) (r : ℝ) (ω : Ω) :
    ∀ {J n : ℕ}, n ≤ J → swingSlopeTerm X r n ω ≤ swingEarlySlope X r J ω := by
  intro J
  induction J with
  | zero =>
    intro n hn
    have : n = 0 := Nat.le_zero.mp hn
    rw [this]
    exact le_rfl
  | succ J ih =>
    intro n hn
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hn) with h | h
    · exact le_trans (ih (Nat.lt_succ_iff.mp h)) (le_max_left _ _)
    · rw [h]
      exact le_max_right _ _

theorem swingEarlySlope_mem (X : ℕ → Ω → ℝ) (r : ℝ) (ω : Ω) :
    ∀ J : ℕ, ∃ n ≤ J, swingEarlySlope X r J ω = swingSlopeTerm X r n ω := by
  intro J
  induction J with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ J ih =>
    obtain ⟨n, hn, hval⟩ := ih
    rcases le_total (swingEarlySlope X r J ω) (swingSlopeTerm X r (J+1) ω) with h | h
    · exact ⟨J+1, le_rfl, by
        show max (swingEarlySlope X r J ω) (swingSlopeTerm X r (J+1) ω) = _
        rw [max_eq_right h]⟩
    · exact ⟨n, hn.trans (Nat.le_succ J), by
        show max (swingEarlySlope X r J ω) (swingSlopeTerm X r (J+1) ω) = _
        rw [max_eq_left h]
        exact hval⟩

theorem swingEarlySlope_mono (X : ℕ → Ω → ℝ) (r : ℝ) (ω : Ω) :
    Monotone (fun J => swingEarlySlope X r J ω) := by
  intro i j hij
  obtain ⟨n, hn, hval⟩ := swingEarlySlope_mem X r ω i
  show swingEarlySlope X r i ω ≤ swingEarlySlope X r j ω
  rw [hval]
  exact swingSlopeTerm_le_swingEarlySlope X r ω (hn.trans hij)

theorem swingEarlySlope_antitone_margin (X : ℕ → Ω → ℝ) (ω : Ω) (J : ℕ)
    {r r' : ℝ} (h : r ≤ r') : swingEarlySlope X r' J ω ≤ swingEarlySlope X r J ω := by
  obtain ⟨n, hn, hval⟩ := swingEarlySlope_mem X r' ω J
  rw [hval]
  refine le_trans ?_ (swingSlopeTerm_le_swingEarlySlope X r ω hn)
  have hpos : (0 : ℝ) < (n : ℝ)+1 := by positivity
  exact div_le_div_of_nonneg_right (by linarith) hpos.le

/-- If the prefix maximum already dominates every ratio, the infinite
supremum equals it. -/
theorem swingLimitingSlope_eq_swingEarlySlope {X : ℕ → Ω → ℝ} {r : ℝ} {J : ℕ} {ω : Ω}
    (hub : ∀ n : ℕ, swingSlopeTerm X r n ω ≤ swingEarlySlope X r J ω) :
    swingLimitingSlope X r ω = swingEarlySlope X r J ω := by
  obtain ⟨n, _, hval⟩ := swingEarlySlope_mem X r ω J
  have hgreat : IsGreatest (Set.range (fun m : ℕ => swingSlopeTerm X r m ω))
      (swingEarlySlope X r J ω) := by
    refine ⟨⟨n, hval.symm⟩, ?_⟩
    rintro y ⟨m, rfl⟩
    exact hub m
  show sSup (Set.range (fun m : ℕ => swingSlopeTerm X r m ω)) = _
  exact hgreat.csSup_eq

/-! ### The localization event -/

/-- `eq:earlyslopelocalization`. -/
def swingEarlySlopeGood (X : ℕ → Ω → ℝ) (K₀ δ M : ℝ) (J : ℕ) : Set Ω :=
  {ω | 2*δ ≤ swingEarlySlope X K₀ J ω ∧ swingEarlySlope X (-K₀) J ω ≤ M ∧
    ∀ n : ℕ, J < n → swingSlopeTail X K₀ n ω < δ}

/-- On the localization event the random slope is the prefix maximum and lies
in `[2δ,M]`, simultaneously for every margin with `|r| ≤ K₀`. -/
theorem swingEarlySlope_localization {X : ℕ → Ω → ℝ} {K₀ δ M : ℝ} {J : ℕ} {ω : Ω}
    (hδ : 0 < δ) (hω : ω ∈ swingEarlySlopeGood X K₀ δ M J) {r : ℝ} (hr : |r| ≤ K₀) :
    swingLimitingSlope X r ω = swingEarlySlope X r J ω ∧
      2*δ ≤ swingLimitingSlope X r ω ∧ swingLimitingSlope X r ω ≤ M := by
  obtain ⟨h1, h2, h3⟩ := hω
  obtain ⟨hrl, hru⟩ := abs_le.mp hr
  have hlow : swingEarlySlope X K₀ J ω ≤ swingEarlySlope X r J ω :=
    swingEarlySlope_antitone_margin X ω J hru
  have hhigh : swingEarlySlope X r J ω ≤ swingEarlySlope X (-K₀) J ω :=
    swingEarlySlope_antitone_margin X ω J hrl
  have hub : ∀ n : ℕ, swingSlopeTerm X r n ω ≤ swingEarlySlope X r J ω := by
    intro n
    rcases le_or_gt n J with hn | hn
    · exact swingSlopeTerm_le_swingEarlySlope X r ω hn
    · have ht := h3 n hn
      have hle := swingSlopeTerm_le_tail X hr n ω
      linarith
  have heq := swingLimitingSlope_eq_swingEarlySlope hub
  refine ⟨heq, ?_, ?_⟩
  · rw [heq]; linarith
  · rw [heq]; linarith

/-! ### Measurability -/

variable [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

theorem cumulativeSamples_measurable (hX : ∀ n, Measurable (X n)) (n : ℕ) :
    Measurable (cumulativeSamples X n) :=
  Finset.measurable_sum _ (fun k _ => hX k)

theorem swingSlopeTerm_measurable (hX : ∀ n, Measurable (X n)) (r : ℝ) (n : ℕ) :
    Measurable (swingSlopeTerm X r n) :=
  ((cumulativeSamples_measurable hX n).sub_const r).div_const _

theorem swingSlopeTail_measurable (hX : ∀ n, Measurable (X n)) (K₀ : ℝ) (n : ℕ) :
    Measurable (swingSlopeTail X K₀ n) :=
  (((cumulativeSamples_measurable hX n).abs).add_const K₀).div_const _

theorem swingEarlySlope_measurable (hX : ∀ n, Measurable (X n)) (r : ℝ) :
    ∀ J : ℕ, Measurable (swingEarlySlope X r J)
  | 0 => swingSlopeTerm_measurable hX r 0
  | (J+1) => (swingEarlySlope_measurable hX r J).max (swingSlopeTerm_measurable hX r (J+1))

/-! ### The sublinear tail -/

omit [MeasurableSpace Ω] in
theorem swingSlopeTail_nonneg (X : ℕ → Ω → ℝ) {K₀ : ℝ} (hK₀ : 0 ≤ K₀) (n : ℕ) (ω : Ω) :
    0 ≤ swingSlopeTail X K₀ n ω := by
  refine div_nonneg ?_ (by positivity)
  have := abs_nonneg (cumulativeSamples X n ω)
  linarith

theorem swingSlopeTail_tendsto_zero_ae
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {K₀ : ℝ} (hK₀ : 0 ≤ K₀) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => swingSlopeTail X K₀ n ω) atTop (𝓝 0) := by
  filter_upwards [gaussianDriftWalk_strongLaw hX hi hG 0 0] with ω hω
  have hW : Tendsto (fun n : ℕ => cumulativeSamples X n ω / (n : ℝ)) atTop (𝓝 0) := by
    refine hω.congr (fun n => ?_)
    simp [gaussianDriftWalk]
  have habs : Tendsto (fun n : ℕ => |cumulativeSamples X n ω| / (n : ℝ)) atTop (𝓝 0) := by
    have habs0 := hW.abs
    simp only [abs_zero] at habs0
    refine habs0.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n _
    rw [abs_div, abs_of_nonneg (show (0:ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)]
  have hK : Tendsto (fun n : ℕ => K₀/((n : ℝ)+1)) atTop (𝓝 0) := by
    refine tendsto_const_nhds.div_atTop ?_
    exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hsum : Tendsto (fun n : ℕ => |cumulativeSamples X n ω| / (n : ℝ) + K₀/((n : ℝ)+1))
      atTop (𝓝 0) := by
    simpa only [add_zero] using habs.add hK
  refine squeeze_zero' (Eventually.of_forall (fun n => swingSlopeTail_nonneg X hK₀ n ω)) ?_ hsum
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hle : |cumulativeSamples X n ω| / ((n : ℝ)+1) ≤ |cumulativeSamples X n ω| / (n : ℝ) :=
    div_le_div_of_nonneg_left (abs_nonneg _) hn0 (by linarith)
  have hsplit : swingSlopeTail X K₀ n ω =
      |cumulativeSamples X n ω| / ((n : ℝ)+1) + K₀/((n : ℝ)+1) := by
    rw [swingSlopeTail, add_div]
  rw [hsplit]
  linarith

/-! ### Choosing the three constants -/

theorem exists_measure_compl_le [IsFiniteMeasure μ]
    {s : ℕ → Set Ω} (hmeas : ∀ n, MeasurableSet (s n)) (hmono : Monotone s)
    (hae : ∀ᵐ ω ∂μ, ∃ n, ω ∈ s n) {e : ℝ≥0∞} (he : 0 < e) :
    ∃ n, μ (s n)ᶜ ≤ e := by
  have hanti : Antitone (fun n => (s n)ᶜ) := fun i j hij => Set.compl_subset_compl.2 (hmono hij)
  have hnull : μ (⋂ n, (s n)ᶜ) = 0 := by
    have hset : (⋂ n, (s n)ᶜ) = {ω | ¬ ∃ n, ω ∈ s n} := by
      ext ω
      simp
    rw [hset, ← ae_iff]
    exact hae
  have htend := tendsto_measure_iInter_atTop (μ := μ)
    (fun n => ((hmeas n).compl).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  rw [hnull] at htend
  obtain ⟨n, hn⟩ := (htend.eventually_lt_const he).exists
  exact ⟨n, hn.le⟩

theorem swingEarlySlopeGood_measurableSet (hX : ∀ n, Measurable (X n))
    (K₀ δ M : ℝ) (J : ℕ) : MeasurableSet (swingEarlySlopeGood X K₀ δ M J) := by
  have hset : swingEarlySlopeGood X K₀ δ M J =
      {ω | 2*δ ≤ swingEarlySlope X K₀ J ω} ∩
        ({ω | swingEarlySlope X (-K₀) J ω ≤ M} ∩
          ⋂ n : ℕ, ⋂ _ : J < n, {ω | swingSlopeTail X K₀ n ω < δ}) := by
    ext ω
    simp only [swingEarlySlopeGood, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [hset]
  refine (measurableSet_le measurable_const (swingEarlySlope_measurable hX K₀ J)).inter ?_
  refine (measurableSet_le (swingEarlySlope_measurable hX (-K₀) J) measurable_const).inter ?_
  exact MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ =>
    measurableSet_lt (swingSlopeTail_measurable hX K₀ n) measurable_const

/-- The probabilistic half of `eq:earlyslopelocalization`: for every error
budget there are `δ>0`, `M` and `J` making the localization event that
likely. -/
theorem exists_swingEarlySlopeGood
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {K₀ : ℝ} (hK₀ : 0 ≤ K₀)
    {e : ℝ≥0∞} (he : 0 < e) :
    ∃ (δ M : ℝ) (J : ℕ), 0 < δ ∧ μ (swingEarlySlopeGood X K₀ δ M J)ᶜ ≤ e := by
  have hprob := hi.isProbabilityMeasure
  have he3 : (0 : ℝ≥0∞) < e/3 := ENNReal.div_pos he.ne' (by norm_num)
  -- the prefix maximum is eventually bounded below by a positive rational
  set T : ℕ → Set Ω := fun k => {ω | 2*(1/((k : ℝ)+1)) ≤ swingEarlySlope X K₀ k ω} with hTdef
  have hTmeas : ∀ k, MeasurableSet (T k) := fun k =>
    measurableSet_le measurable_const (swingEarlySlope_measurable hX K₀ k)
  have hTmono : Monotone T := by
    intro i j hij ω hω
    have h1 : 2*(1/((j : ℝ)+1)) ≤ 2*(1/((i : ℝ)+1)) := by
      have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
      have : (1 : ℝ)/((j : ℝ)+1) ≤ 1/((i : ℝ)+1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      linarith
    have h2 : swingEarlySlope X K₀ i ω ≤ swingEarlySlope X K₀ j ω :=
      swingEarlySlope_mono X K₀ ω hij
    have h3 : 2*(1/((i : ℝ)+1)) ≤ swingEarlySlope X K₀ i ω := hω
    show 2*(1/((j : ℝ)+1)) ≤ swingEarlySlope X K₀ j ω
    linarith
  have hTae : ∀ᵐ ω ∂μ, ∃ k, ω ∈ T k := by
    filter_upwards [swingLimitingSlope_pos_ae hX hi hG K₀] with ω hω
    have hsup : (0 : ℝ) < sSup (Set.range (fun m : ℕ => swingSlopeTerm X K₀ m ω)) := hω
    obtain ⟨y, hy_mem, hy⟩ := exists_lt_of_lt_csSup (Set.range_nonempty _) hsup
    obtain ⟨n, rfl⟩ := hy_mem
    obtain ⟨k, hk⟩ := exists_nat_gt (2/swingSlopeTerm X K₀ n ω)
    refine ⟨max n k, ?_⟩
    have hterm : 0 < swingSlopeTerm X K₀ n ω := hy
    have hkr : (k : ℝ) ≤ ((max n k : ℕ) : ℝ) := by exact_mod_cast Nat.le_max_right n k
    have hmul : 2 < (k : ℝ) * swingSlopeTerm X K₀ n ω := by
      rw [div_lt_iff₀ hterm] at hk
      linarith
    have h2 : 2*(1/(((max n k : ℕ) : ℝ)+1)) ≤ swingSlopeTerm X K₀ n ω := by
      rw [mul_one_div, div_le_iff₀ (by positivity)]
      nlinarith
    have h1 : swingSlopeTerm X K₀ n ω ≤ swingEarlySlope X K₀ (max n k) ω :=
      swingSlopeTerm_le_swingEarlySlope X K₀ ω (le_max_left _ _)
    show 2*(1/(((max n k : ℕ) : ℝ)+1)) ≤ swingEarlySlope X K₀ (max n k) ω
    linarith
  obtain ⟨k, hk⟩ := exists_measure_compl_le hTmeas hTmono hTae he3
  set δ : ℝ := 1/((k : ℝ)+1) with hδdef
  have hδ : 0 < δ := by positivity
  -- the sublinear tail
  set U : ℕ → Set Ω := fun J => {ω | ∀ n : ℕ, J < n → swingSlopeTail X K₀ n ω < δ} with hUdef
  have hUmeas : ∀ J, MeasurableSet (U J) := by
    intro J
    have hset : U J = ⋂ n : ℕ, ⋂ _ : J < n, {ω | swingSlopeTail X K₀ n ω < δ} := by
      ext ω
      simp only [hUdef, Set.mem_ofPred_eq, Set.mem_iInter]
    rw [hset]
    exact MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ =>
      measurableSet_lt (swingSlopeTail_measurable hX K₀ n) measurable_const
  have hUmono : Monotone U := by
    intro i j hij ω hω n hn
    exact hω n (lt_of_le_of_lt hij hn)
  have hUae : ∀ᵐ ω ∂μ, ∃ J, ω ∈ U J := by
    filter_upwards [swingSlopeTail_tendsto_zero_ae hX hi hG hK₀] with ω hω
    obtain ⟨J, hJ⟩ := (hω.eventually_lt_const hδ).exists_forall_of_atTop
    exact ⟨J, fun n hn => hJ n hn.le⟩
  obtain ⟨J₂, hJ₂⟩ := exists_measure_compl_le hUmeas hUmono hUae he3
  set J : ℕ := max k J₂ with hJdef
  -- the prefix bound at the extreme margin
  set V : ℕ → Set Ω := fun q => {ω | swingEarlySlope X (-K₀) J ω ≤ (q : ℝ)} with hVdef
  have hVmeas : ∀ q, MeasurableSet (V q) := fun q =>
    measurableSet_le (swingEarlySlope_measurable hX (-K₀) J) measurable_const
  have hVmono : Monotone V := by
    intro i j hij ω hω
    have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    have : swingEarlySlope X (-K₀) J ω ≤ (i : ℝ) := hω
    show swingEarlySlope X (-K₀) J ω ≤ (j : ℝ)
    linarith
  have hVae : ∀ᵐ ω ∂μ, ∃ q, ω ∈ V q := by
    filter_upwards with ω
    obtain ⟨q, hq⟩ := exists_nat_ge (swingEarlySlope X (-K₀) J ω)
    exact ⟨q, hq⟩
  obtain ⟨q, hq⟩ := exists_measure_compl_le hVmeas hVmono hVae he3
  refine ⟨δ, (q : ℝ), J, hδ, ?_⟩
  -- the good event contains the intersection of the three chosen events
  have hsub : T k ∩ U J ∩ V q ⊆ swingEarlySlopeGood X K₀ δ (q : ℝ) J := by
    rintro ω ⟨⟨hT, hU⟩, hV⟩
    refine ⟨?_, hV, hU⟩
    have h1 : 2*δ ≤ swingEarlySlope X K₀ k ω := hT
    have h2 : swingEarlySlope X K₀ k ω ≤ swingEarlySlope X K₀ J ω :=
      swingEarlySlope_mono X K₀ ω (le_max_left _ _)
    linarith
  have hUJ : μ (U J)ᶜ ≤ e/3 :=
    le_trans (measure_mono (Set.compl_subset_compl.2 (hUmono (le_max_right k J₂)))) hJ₂
  have hbound : μ (swingEarlySlopeGood X K₀ δ (q : ℝ) J)ᶜ ≤ e/3 + e/3 + e/3 := by
    refine le_trans (measure_mono (Set.compl_subset_compl.2 hsub)) ?_
    rw [Set.compl_inter, Set.compl_inter]
    refine le_trans (measure_union_le _ _) ?_
    exact add_le_add (le_trans (measure_union_le _ _) (add_le_add hk hUJ)) hq
  refine hbound.trans ?_
  rw [ENNReal.div_add_div_same, ENNReal.div_add_div_same]
  exact ENNReal.div_le_of_le_mul (by rw [show e*3 = e+e+e by ring])

end SwingRepair
