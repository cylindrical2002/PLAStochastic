import PLAStochastic.Swing.StationaryLimit.Slope.EarlyLocalization

/-!
# Early-slope localization with a prescribed upper tolerance

The ordinary localization theorem only returns some positive `δ`.  Later
budget arguments sometimes choose a smaller error scale in advance.  This
module repeats the monotone-event selection with one extra lower bound on the
index, yielding `δ ≤ d` without changing the good-event estimate.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem exists_swingEarlySlopeGood_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {K₀ : ℝ} (hK₀ : 0 ≤ K₀)
    {e : ℝ≥0∞} (he : 0 < e) {d : ℝ} (hd : 0 < d) :
    ∃ (δ M : ℝ) (J : ℕ), 0 < δ ∧ δ ≤ d ∧
      μ (swingEarlySlopeGood X K₀ δ M J)ᶜ ≤ e := by
  have hprob := hi.isProbabilityMeasure
  have he3 : (0 : ℝ≥0∞) < e / 3 := ENNReal.div_pos he.ne' (by norm_num)
  -- The prefix maximum eventually exceeds a positive rational.  We retain
  -- the old threshold event and enlarge its index after the measure choice.
  set T : ℕ → Set Ω :=
    fun k => {ω | 2 * (1 / ((k : ℝ) + 1)) ≤ swingEarlySlope X K₀ k ω}
      with hTdef
  have hTmeas : ∀ k, MeasurableSet (T k) := fun k =>
    measurableSet_le measurable_const (swingEarlySlope_measurable hX K₀ k)
  have hTmono : Monotone T := by
    intro i j hij ω hω
    have h1 : 2 * (1 / ((j : ℝ) + 1)) ≤
        2 * (1 / ((i : ℝ) + 1)) := by
      have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
      have hdiv : (1 : ℝ) / ((j : ℝ) + 1) ≤
          1 / ((i : ℝ) + 1) := by
        exact one_div_le_one_div_of_le (by positivity) (by linarith)
      linarith
    have h2 : swingEarlySlope X K₀ i ω ≤
        swingEarlySlope X K₀ j ω := swingEarlySlope_mono X K₀ ω hij
    have h3 : 2 * (1 / ((i : ℝ) + 1)) ≤
        swingEarlySlope X K₀ i ω := hω
    show 2 * (1 / ((j : ℝ) + 1)) ≤
      swingEarlySlope X K₀ j ω
    linarith
  have hTae : ∀ᵐ ω ∂μ, ∃ k, ω ∈ T k := by
    filter_upwards [swingLimitingSlope_pos_ae hX hi hG K₀] with ω hω
    have hsup : (0 : ℝ) <
        sSup (Set.range (fun m : ℕ => swingSlopeTerm X K₀ m ω)) := hω
    obtain ⟨y, hy_mem, hy⟩ := exists_lt_of_lt_csSup (Set.range_nonempty _) hsup
    obtain ⟨n, rfl⟩ := hy_mem
    obtain ⟨k, hk⟩ := exists_nat_gt (2 / swingSlopeTerm X K₀ n ω)
    refine ⟨max n k, ?_⟩
    have hterm : 0 < swingSlopeTerm X K₀ n ω := hy
    have hkr : (k : ℝ) ≤ ((max n k : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_max_right n k
    have hmul : 2 < (k : ℝ) * swingSlopeTerm X K₀ n ω := by
      rw [div_lt_iff₀ hterm] at hk
      linarith
    have h2 : 2 * (1 / (((max n k : ℕ) : ℝ) + 1)) ≤
        swingSlopeTerm X K₀ n ω := by
      rw [mul_one_div, div_le_iff₀ (by positivity)]
      nlinarith
    have h1 : swingSlopeTerm X K₀ n ω ≤
        swingEarlySlope X K₀ (max n k) ω :=
      swingSlopeTerm_le_swingEarlySlope X K₀ ω (le_max_left _ _)
    show 2 * (1 / (((max n k : ℕ) : ℝ) + 1)) ≤
      swingEarlySlope X K₀ (max n k) ω
    linarith
  obtain ⟨k₀, hk₀⟩ := exists_measure_compl_le hTmeas hTmono hTae he3
  -- Force the selected threshold below the prescribed `d`.
  obtain ⟨kd, hkd⟩ := exists_nat_gt (1 / d)
  let k : ℕ := max k₀ kd
  have hk_ge : k₀ ≤ k := Nat.le_max_left _ _
  have hkT : μ (T k)ᶜ ≤ e / 3 := by
    exact (measure_mono (Set.compl_subset_compl.2 (hTmono hk_ge))).trans hk₀
  have hδd : 1 / ((k : ℝ) + 1) ≤ d := by
    have hkd' : (1 / d : ℝ) < (kd : ℝ) := by exact_mod_cast hkd
    have hkd'' : (kd : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast (Nat.le_max_right k₀ kd)
    have hkpos : 0 < (k : ℝ) + 1 := by positivity
    apply (div_le_iff₀ hkpos).2
    have hmul_kd : 1 < d * (kd : ℝ) := by
      have hmul := (div_lt_iff₀ hd).mp hkd'
      nlinarith
    nlinarith
  let δ : ℝ := 1 / ((k : ℝ) + 1)
  have hδ : 0 < δ := by positivity
  have hδ_le : δ ≤ d := by simpa [δ] using hδd
  -- The sublinear tail is selected at the smaller threshold `δ`.
  set U : ℕ → Set Ω :=
    fun J => {ω | ∀ n : ℕ, J < n → swingSlopeTail X K₀ n ω < δ}
      with hUdef
  have hUmeas : ∀ J, MeasurableSet (U J) := by
    intro J
    have hset : U J = ⋂ n : ℕ, ⋂ _ : J < n,
        {ω | swingSlopeTail X K₀ n ω < δ} := by
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
  let J : ℕ := max k J₂
  -- The upper extreme margin is bounded by an integer cutoff.
  set V : ℕ → Set Ω :=
    fun q => {ω | swingEarlySlope X (-K₀) J ω ≤ (q : ℝ)} with hVdef
  have hVmeas : ∀ q, MeasurableSet (V q) := fun q =>
    measurableSet_le (swingEarlySlope_measurable hX (-K₀) J) measurable_const
  have hVmono : Monotone V := by
    intro i j hij ω hω
    have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    have hi' : swingEarlySlope X (-K₀) J ω ≤ (i : ℝ) := hω
    show swingEarlySlope X (-K₀) J ω ≤ (j : ℝ)
    linarith
  have hVae : ∀ᵐ ω ∂μ, ∃ q, ω ∈ V q := by
    filter_upwards with ω
    obtain ⟨q, hq⟩ := exists_nat_ge (swingEarlySlope X (-K₀) J ω)
    exact ⟨q, hq⟩
  obtain ⟨q, hq⟩ := exists_measure_compl_le hVmeas hVmono hVae he3
  refine ⟨δ, (q : ℝ), J, hδ, hδ_le, ?_⟩
  have hsub : T k ∩ U J ∩ V q ⊆
      swingEarlySlopeGood X K₀ δ (q : ℝ) J := by
    rintro ω ⟨⟨hT, hU⟩, hV⟩
    refine ⟨?_, hV, hU⟩
    have h1 : 2 * δ ≤ swingEarlySlope X K₀ k ω := hT
    have h2 : swingEarlySlope X K₀ k ω ≤
        swingEarlySlope X K₀ J ω :=
      swingEarlySlope_mono X K₀ ω (le_max_left _ _)
    linarith
  have hUJ : μ (U J)ᶜ ≤ e / 3 := by
    exact le_trans
      (measure_mono (Set.compl_subset_compl.2
        (hUmono (Nat.le_max_right k J₂)))) hJ₂
  have hbound : μ (swingEarlySlopeGood X K₀ δ (q : ℝ) J)ᶜ ≤
      e / 3 + e / 3 + e / 3 := by
    refine le_trans (measure_mono (Set.compl_subset_compl.2 hsub)) ?_
    rw [Set.compl_inter, Set.compl_inter]
    refine le_trans (measure_union_le _ _) ?_
    exact add_le_add (le_trans (measure_union_le _ _) (add_le_add hkT hUJ)) hq
  refine hbound.trans ?_
  rw [ENNReal.div_add_div_same, ENNReal.div_add_div_same]
  exact ENNReal.div_le_of_le_mul (by rw [show e * 3 = e + e + e by ring])

theorem exists_swingEarlySlopeGood_real_nonneg_le
    {X : ℕ → Ω → ℝ}
    (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {K : ℝ} (hK : 0 ≤ K) {ε d : ℝ} (hε : 0 < ε) (hd : 0 < d) :
    ∃ (δ M : ℝ) (J : ℕ), 0 < δ ∧ δ ≤ d ∧ 0 ≤ M ∧ 1 ≤ J ∧
      μ.real (swingEarlySlopeGood X K δ M (J - 1))ᶜ ≤ ε := by
  obtain ⟨δ, M, J₀, hδ, hδd, hbad⟩ :=
    exists_swingEarlySlopeGood_le (μ := μ) hX hi hG hK
      (e := ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε) hd
  let M' : ℝ := max M 0
  have hM' : 0 ≤ M' := by
    dsimp [M']
    exact le_max_right _ _
  have hsub : swingEarlySlopeGood X K δ M (J₀) ⊆
      swingEarlySlopeGood X K δ M' J₀ := by
    intro ω hω
    rcases hω with ⟨hlo, hupp, htail⟩
    refine ⟨hlo, hupp.trans (le_max_left _ _), htail⟩
  have hcomp :
      (swingEarlySlopeGood X K δ M' J₀)ᶜ ⊆
        (swingEarlySlopeGood X K δ M J₀)ᶜ :=
    Set.compl_subset_compl.mpr hsub
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  refine ⟨δ, M', J₀ + 1, hδ, hδd, hM', Nat.succ_le_succ (Nat.zero_le _), ?_⟩
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbad
  have hreal' : μ.real (swingEarlySlopeGood X K δ M J₀)ᶜ ≤ ε := by
    simpa [Measure.real, ENNReal.toReal_ofReal (le_of_lt hε)] using hreal
  exact (measureReal_mono hcomp (measure_ne_top μ _)).trans hreal'

end SwingRepair
