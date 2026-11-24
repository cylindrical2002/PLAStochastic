import PLAStochastic.Swing.Ladder.ZeroDrift.LadderLaw

/-!
# Regeneration of the zero-drift ladder epochs

The regeneration results of `Swing.Ladder.Law.EpochRegeneration`,
`Swing.Ladder.Renewal.LadderPointCount`, `OvershootIdentity` and `RecordValues` are stated
for a positive drift, but the drift enters only through the almost sure finiteness of the
first ladder epoch.  This file restates them under that finiteness hypothesis and then
specializes to the zero drift, where the hypothesis is the a.s. finiteness of the first
strict ascending ladder epoch of the zero-drift walk:

* the successive strict ascending ladder heights are i.i.d. with law `ν₀`;
* the `n`-th ladder level has law `ν₀^{*n}` and the renewal measure `ladderRenewalMeasure ν₀`
  is the expected number of ladder levels in a set;
* the ladder levels exceed every level a.s.;
* the overshoot of the walk above a level `b ≥ 0` is the ladder overshoot, and its tail is
  the residual-life integral `renewalOvershootTail ν₀ b t`.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical MeasureTheory
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

theorem gaussianAscendingLadderIndex_finite_ae_of {a : ℝ}
    (hfin : ∀ᵐ ω ∂μ, gaussianAscendingLadderTime X a ω ≠ ⊤) :
    ∀ᵐ ω ∂μ, gaussianAscendingLadderIndex X a ω ≠ ⊤ :=
  hfin.mono fun _ hω => gaussianAscendingLadderIndex_ne_top X a hω

section Regeneration

variable [IsProbabilityMeasure μ]

theorem ladderSequenceRestart_identDistrib_of
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ}
    (hfin : ∀ᵐ ω ∂μ, gaussianAscendingLadderTime X a ω ≠ ⊤) :
    IdentDistrib (fun ω => ladderSequenceRestart a (fun k => X k ω))
      (fun ω (j : ℕ) => X j ω) μ μ :=
  stoppedSequence_identDistrib hX hi (gaussianIncrements_identDistrib hX hG)
    (gaussianAscendingLadderIndex_isStoppingTime hX a)
    (gaussianAscendingLadderIndex_finite_ae_of hfin)

theorem ladderSequenceSplit_indep_of
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ}
    (hfin : ∀ᵐ ω ∂μ, gaussianAscendingLadderTime X a ω ≠ ⊤) :
    IndepFun (fun ω => ladderSequenceHeight a (fun k => X k ω))
      (fun ω => ladderSequenceRestart a (fun k => X k ω)) μ := by
  have hτ := gaussianAscendingLadderIndex_isStoppingTime hX a
  have hH : Measurable[hτ.measurableSpace] (gaussianAscendingLadderHeight X a) :=
    gaussianAscendingLadderHeight_measurable_stopped hX a
  exact indep_of_indep_of_le_left
    (stoppedSequence_indep_stopped hX hi (gaussianIncrements_identDistrib hX hG) hτ
      (gaussianAscendingLadderIndex_finite_ae_of hfin)).symm hH.comap_le

/-- All strict ascending ladder heights are mutually independent. -/
theorem gaussianLadderHeights_iIndepFun_of
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ}
    (hfin : ∀ᵐ ω ∂μ, gaussianAscendingLadderTime X a ω ≠ ⊤) :
    iIndepFun (gaussianLadderHeightAt X a) μ :=
  regenerativeFactors_iIndepFun (ladderSequenceHeight_measurable a)
    (ladderSequenceRestart_measurable a) (measurable_pi_lambda _ hX)
    (ladderSequenceRestart_identDistrib_of hX hi hG hfin)
    (ladderSequenceSplit_indep_of hX hi hG hfin)

/-- Each ladder height has the first ladder-height law. -/
theorem gaussianLadderHeightAt_map_of
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ}
    (hfin : ∀ᵐ ω ∂μ, gaussianAscendingLadderTime X a ω ≠ ⊤) (n : ℕ) :
    μ.map (gaussianLadderHeightAt X a n) = gaussianAscendingLadderLaw X μ a :=
  (regenerativeFactor_identDistrib (ladderSequenceHeight_measurable a)
    (ladderSequenceRestart_measurable a) (measurable_pi_lambda _ hX)
    (ladderSequenceRestart_identDistrib_of hX hi hG hfin) n).map_eq

theorem gaussianLadderStep_indep_of
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ}
    (hfin : ∀ᵐ ω ∂μ, gaussianAscendingLadderTime X a ω ≠ ⊤) (n : ℕ) :
    IndepFun (gaussianLadderSum X a n) (gaussianLadderHeightAt X a n) μ := by
  have h := (gaussianLadderHeights_iIndepFun_of hX hi hG hfin).indepFun_finsetSum_of_notMem
    (fun k => gaussianLadderHeightAt_measurable hX a k)
    (s := Finset.range n) (i := n) (by simp)
  have heq : (∑ j ∈ Finset.range n, gaussianLadderHeightAt X a j) = gaussianLadderSum X a n := by
    funext ω
    simp [gaussianLadderSum, Finset.sum_apply]
  rwa [heq] at h

/-- The `n`-th ladder level has the `n`-fold convolution of the ladder law. -/
theorem gaussianLadderSum_map_of
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ}
    (hfin : ∀ᵐ ω ∂μ, gaussianAscendingLadderTime X a ω ≠ ⊤) (n : ℕ) :
    μ.map (gaussianLadderSum X a n) = measureConvPow (gaussianAscendingLadderLaw X μ a) n := by
  induction n with
  | zero =>
    rw [measureConvPow_zero]
    have : gaussianLadderSum X a 0 = fun _ : Ω => (0 : ℝ) := funext (fun ω => by simp)
    rw [this, Measure.map_const]
    simp
  | succ n ih =>
    have hfun : gaussianLadderSum X a (n + 1) =
        fun ω => gaussianLadderSum X a n ω + gaussianLadderHeightAt X a n ω :=
      funext (fun ω => gaussianLadderSum_succ X a n ω)
    rw [hfun, map_add_of_indepFun (gaussianLadderSum_measurable hX a n)
      (gaussianLadderHeightAt_measurable hX a n) (gaussianLadderStep_indep_of hX hi hG hfin n), ih,
      gaussianLadderHeightAt_map_of hX hi hG hfin n, measureConvPow_succ]

/-- The renewal measure of the ladder law is the expected number of ladder levels. -/
theorem ladderRenewalMeasure_eq_tsum_ladderSum_of
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ}
    (hfin : ∀ᵐ ω ∂μ, gaussianAscendingLadderTime X a ω ≠ ⊤)
    {A : Set ℝ} (hA : MeasurableSet A) :
    ladderRenewalMeasure (gaussianAscendingLadderLaw X μ a) A =
      ∑' n : ℕ, μ {ω | gaussianLadderSum X a n ω ∈ A} := by
  rw [ladderRenewalMeasure_apply _ hA]
  refine tsum_congr fun n => ?_
  rw [← gaussianLadderSum_map_of hX hi hG hfin n,
    Measure.map_apply (gaussianLadderSum_measurable hX a n) hA]
  rfl

/-- If the renewal measure is finite on bounded intervals, the ladder levels exceed every
bound almost surely. -/
theorem gaussianLadderSum_exists_gt_ae_of
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ}
    (hfin : ∀ᵐ ω ∂μ, gaussianAscendingLadderTime X a ω ≠ ⊤)
    (hU : ∀ b : ℝ, ladderRenewalMeasure (gaussianAscendingLadderLaw X μ a) (Icc 0 b) ≠ ⊤) :
    ∀ᵐ ω ∂μ, ∀ b : ℝ, ∃ n : ℕ, b < gaussianLadderSum X a n ω := by
  have hkey : ∀ k : ℕ, ∀ᵐ ω ∂μ, ∃ n : ℕ, (k : ℝ) < gaussianLadderSum X a n ω := by
    intro k
    have hsum : (∑' n : ℕ, μ {ω | gaussianLadderSum X a n ω ∈ Icc (0 : ℝ) (k : ℝ)}) ≠ ⊤ := by
      rw [← ladderRenewalMeasure_eq_tsum_ladderSum_of hX hi hG hfin measurableSet_Icc]
      exact hU k
    have hbc := measure_limsup_atTop_eq_zero (μ := μ)
      (s := fun n => {ω | gaussianLadderSum X a n ω ∈ Icc (0 : ℝ) (k : ℝ)}) hsum
    have hae : ∀ᵐ ω ∂μ, ω ∉ Filter.limsup
        (fun n => {ω | gaussianLadderSum X a n ω ∈ Icc (0 : ℝ) (k : ℝ)}) atTop := by
      rw [ae_iff]
      simpa using hbc
    filter_upwards [hae] with ω hω
    by_contra hcon
    have hcon' : ∀ n : ℕ, gaussianLadderSum X a n ω ≤ (k : ℝ) := by
      intro n
      by_contra hn
      exact hcon ⟨n, lt_of_not_ge hn⟩
    apply hω
    rw [Filter.limsup_eq_iInf_iSup_of_nat]
    refine Set.mem_iInter.mpr fun m => ?_
    refine Set.mem_iUnion.mpr ⟨m, ?_⟩
    refine Set.mem_iUnion.mpr ⟨Nat.le_refl m, ?_⟩
    exact ⟨gaussianLadderSum_nonneg X a m ω, hcon' m⟩
  rw [← ae_all_iff] at hkey
  filter_upwards [hkey] with ω hω b
  obtain ⟨k, hk⟩ := exists_nat_gt b
  obtain ⟨n, hn⟩ := hω k
  exact ⟨n, lt_trans hk hn⟩

theorem gaussianLadderStep_measure_of
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ}
    (hfin : ∀ᵐ ω ∂μ, gaussianAscendingLadderTime X a ω ≠ ⊤) (b t : ℝ) (n : ℕ) :
    μ ({ω | gaussianLadderSum X a n ω ≤ b} ∩ {ω | b + t < gaussianLadderSum X a (n + 1) ω}) =
      ∫⁻ s in Icc (0 : ℝ) b, (gaussianAscendingLadderLaw X μ a) (Ioi (b + t - s))
        ∂(measureConvPow (gaussianAscendingLadderLaw X μ a) n) := by
  have hset : {ω | gaussianLadderSum X a n ω ≤ b} ∩
      {ω | b + t < gaussianLadderSum X a (n + 1) ω} =
      {ω | gaussianLadderSum X a n ω ≤ b} ∩
        {ω | b + t < gaussianLadderSum X a n ω + gaussianLadderHeightAt X a n ω} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, gaussianLadderSum_succ]
  rw [hset, measure_le_and_lt_add_of_indepFun (gaussianLadderSum_measurable hX a n)
    (gaussianLadderHeightAt_measurable hX a n)
    (gaussianLadderStep_indep_of hX hi hG hfin n) b (b + t),
    gaussianLadderHeightAt_map_of hX hi hG hfin n, gaussianLadderSum_map_of hX hi hG hfin n]
  have hnull : (measureConvPow (gaussianAscendingLadderLaw X μ a) n) (Iio (0 : ℝ)) = 0 := by
    rw [← gaussianLadderSum_map_of hX hi hG hfin n,
      Measure.map_apply (gaussianLadderSum_measurable hX a n) measurableSet_Iio]
    have hempty : (gaussianLadderSum X a n) ⁻¹' (Iio (0 : ℝ)) = (∅ : Set Ω) := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_empty_iff_false, iff_false, not_lt]
      exact gaussianLadderSum_nonneg X a n ω
    rw [hempty, measure_empty]
  have hae : Iic b =ᵐ[measureConvPow (gaussianAscendingLadderLaw X μ a) n] Icc (0 : ℝ) b := by
    rw [ae_eq_set]
    constructor
    · have hdiff : Iic b \ Icc (0 : ℝ) b ⊆ Iio (0 : ℝ) := by
        intro x hx
        have h1 : x ≤ b := hx.1
        have h2 : ¬ (0 ≤ x ∧ x ≤ b) := hx.2
        show x < 0
        by_contra hcon
        exact h2 ⟨le_of_not_gt hcon, h1⟩
      exact measure_mono_null hdiff hnull
    · have hempty2 : Icc (0 : ℝ) b \ Iic b = (∅ : Set ℝ) := by
        ext x
        simp only [Set.mem_sdiff, Set.mem_Icc, Set.mem_Iic, Set.mem_empty_iff_false, iff_false,
          not_and, not_not]
        rintro ⟨-, h2⟩
        exact h2
      rw [hempty2, measure_empty]
  rw [Measure.restrict_congr_set hae]

/-- The overshoot tail of the ladder levels is the residual-life integral. -/
theorem gaussianLadderOvershoot_tail_eq_of
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ}
    (hfin : ∀ᵐ ω ∂μ, gaussianAscendingLadderTime X a ω ≠ ⊤)
    (hU : ∀ b : ℝ, ladderRenewalMeasure (gaussianAscendingLadderLaw X μ a) (Icc 0 b) ≠ ⊤)
    {b t : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) :
    μ {ω | t < gaussianLadderOvershoot X a b ω} =
      renewalOvershootTail (gaussianAscendingLadderLaw X μ a) b t := by
  set ν := gaussianAscendingLadderLaw X μ a with hνdef
  set E : ℕ → Set Ω := fun n => {ω | gaussianLadderSum X a n ω ≤ b} ∩
    {ω | b + t < gaussianLadderSum X a (n + 1) ω} with hEdef
  have hEmeas : ∀ n, MeasurableSet (E n) := by
    intro n
    exact (measurableSet_le (gaussianLadderSum_measurable hX a n) measurable_const).inter
      (measurableSet_lt measurable_const (gaussianLadderSum_measurable hX a (n + 1)))
  have hdisj : Pairwise (Function.onFun Disjoint E) := by
    intro m n hmn
    rw [Function.onFun, Set.disjoint_left]
    intro ω hm hn
    rcases lt_or_gt_of_ne hmn with h | h
    · have hmono := gaussianLadderSum_monotone X a ω (show m + 1 ≤ n by omega)
      have h1 : b + t < gaussianLadderSum X a (m + 1) ω := hm.2
      have h2 : gaussianLadderSum X a n ω ≤ b := hn.1
      linarith
    · have hmono := gaussianLadderSum_monotone X a ω (show n + 1 ≤ m by omega)
      have h1 : b + t < gaussianLadderSum X a (n + 1) ω := hn.2
      have h2 : gaussianLadderSum X a m ω ≤ b := hm.1
      linarith
  have hae : {ω | t < gaussianLadderOvershoot X a b ω} =ᵐ[μ] (⋃ n, E n) := by
    filter_upwards [gaussianLadderSum_exists_gt_ae_of hX hi hG hfin hU] with ω hω
    have hiff := gaussianLadderOvershoot_gt_iff X a hb ht (hω b)
    refine propext ?_
    show t < gaussianLadderOvershoot X a b ω ↔ ω ∈ ⋃ n, E n
    rw [Set.mem_iUnion]
    exact hiff
  calc μ {ω | t < gaussianLadderOvershoot X a b ω}
      = μ (⋃ n, E n) := measure_congr hae
    _ = ∑' n : ℕ, μ (E n) := measure_iUnion hdisj hEmeas
    _ = ∑' n : ℕ, ∫⁻ s in Icc (0 : ℝ) b, ν (Ioi (b + t - s)) ∂(measureConvPow ν n) := by
      refine tsum_congr fun n => ?_
      rw [hEdef, hνdef]
      exact gaussianLadderStep_measure_of hX hi hG hfin b t n
    _ = ∫⁻ s in Icc (0 : ℝ) b, ν (Ioi (b + t - s)) ∂(ladderRenewalMeasure ν) := by
      rw [ladderRenewalMeasure, Measure.restrict_sum _ measurableSet_Icc, lintegral_sum_measure]
    _ = renewalOvershootTail ν b t := rfl

theorem ladderSequence_iterate_finite_ae_of
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ}
    (hfin : ∀ᵐ ω ∂μ, gaussianAscendingLadderTime X a ω ≠ ⊤) :
    ∀ᵐ ω ∂μ, ∀ n : ℕ,
      gaussianAscendingLadderTime (fun k (v : ℕ → ℝ) => v k) a
        ((ladderSequenceRestart a)^[n] (fun k => X k ω)) ≠ ⊤ := by
  rw [ae_all_iff]
  intro n
  have hmeas : MeasurableSet {w : ℕ → ℝ |
      gaussianAscendingLadderTime (fun k (v : ℕ → ℝ) => v k) a w ≠ ⊤} :=
    (measurableSet_eq_fun
      (gaussianAscendingLadderTime_measurable (fun k => measurable_pi_apply k) a)
      measurable_const).compl
  have hstate := regenerativeState_identDistrib (ladderSequenceRestart_measurable a)
    (measurable_pi_lambda _ hX) (ladderSequenceRestart_identDistrib_of hX hi hG hfin) n
  exact hstate.symm.ae_snd hmeas hfin

/-- The overshoot of the walk above `b ≥ 0` has the residual-life tail. -/
theorem gaussianWalkOvershoot_tail_eq_of
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ}
    (hfin : ∀ᵐ ω ∂μ, gaussianAscendingLadderTime X a ω ≠ ⊤)
    (hU : ∀ b : ℝ, ladderRenewalMeasure (gaussianAscendingLadderLaw X μ a) (Icc 0 b) ≠ ⊤)
    {b t : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) :
    μ {ω | t < gaussianWalkOvershoot X a b ω} =
      renewalOvershootTail (gaussianAscendingLadderLaw X μ a) b t := by
  have hcong : {ω | t < gaussianWalkOvershoot X a b ω} =ᵐ[μ]
      {ω | t < gaussianLadderOvershoot X a b ω} := by
    filter_upwards [ladderSequence_iterate_finite_ae_of hX hi hG hfin,
      gaussianLadderSum_exists_gt_ae_of hX hi hG hfin hU] with ω hfin' hex
    have hω := gaussianWalkOvershoot_eq_ladder X a hb hfin' (hex b)
    refine propext ?_
    show t < gaussianWalkOvershoot X a b ω ↔ t < gaussianLadderOvershoot X a b ω
    rw [hω]
  rw [measure_congr hcong]
  exact gaussianLadderOvershoot_tail_eq_of hX hi hG hfin hU hb ht

end Regeneration

/-! ### The zero drift -/

section ZeroDrift

variable [IsProbabilityMeasure μ]

/-- The zero-drift ladder levels are the record values of the walk: the `n`-th ladder
level is the walk at the `n`-th ladder epoch. -/
theorem gaussianZeroLadderSum_eq_walk_ae
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    ∀ᵐ ω ∂μ, ∀ n : ℕ, cumulativeSamples X (ladderSequenceEpoch 0 n (fun k => X k ω)) ω =
      gaussianLadderSum X 0 n ω := by
  filter_upwards [ladderSequence_iterate_finite_ae_of hX hi hG
    (gaussianAscendingLadderTime_zero_finite_ae hX hi hG)] with ω hω n
  have h := ladderSequence_walk_epoch_eq 0 n (fun k => X k ω) hω
  rw [← gaussianDriftWalk_eq_sequence] at h
  simpa [gaussianDriftWalk, gaussianLadderSum_eq_sequence] using h

theorem gaussianZeroLadderSum_exists_gt_ae
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    ∀ᵐ ω ∂μ, ∀ b : ℝ, ∃ n : ℕ, b < gaussianLadderSum X 0 n ω :=
  gaussianLadderSum_exists_gt_ae_of hX hi hG (gaussianAscendingLadderTime_zero_finite_ae hX hi hG)
    (gaussianAscendingLadderLaw_zero_spreadOut hX hi hG).renewal_Icc_ne_top

/-- **The overshoot renewal identity at zero drift**: for `b, t ≥ 0`,
`P(W_{T_b} - b > t) = ∫_{[0,b]} ν₀((b+t-s,∞)) U₀(ds)`. -/
theorem gaussianZeroWalkOvershoot_tail_eq
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {b t : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) :
    μ {ω | t < gaussianWalkOvershoot X 0 b ω} =
      renewalOvershootTail (gaussianAscendingLadderLaw X μ 0) b t :=
  gaussianWalkOvershoot_tail_eq_of hX hi hG (gaussianAscendingLadderTime_zero_finite_ae hX hi hG)
    (gaussianAscendingLadderLaw_zero_spreadOut hX hi hG).renewal_Icc_ne_top hb ht

/-- The zero-drift walk exceeds every level almost surely. -/
theorem gaussianZeroWalk_exists_gt_ae
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    ∀ᵐ ω ∂μ, ∀ b : ℝ, ∃ m : ℕ, b < cumulativeSamples X m ω := by
  filter_upwards [gaussianZeroLadderSum_exists_gt_ae hX hi hG,
    gaussianZeroLadderSum_eq_walk_ae hX hi hG] with ω hex hwalk b
  obtain ⟨n, hn⟩ := hex b
  exact ⟨ladderSequenceEpoch 0 n (fun k => X k ω), by rw [hwalk n]; exact hn⟩

end ZeroDrift

end SwingRepair
