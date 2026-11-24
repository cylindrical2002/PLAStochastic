import PLAStochastic.Swing.ConstantEvaluation.Fluctuation.SparreAndersenDrifted
import PLAStochastic.ForMathlib.Probability.RandomWalk.Fluctuation.SpitzerBaxterExponential
import PLAStochastic.Swing.ConstantEvaluation.Fluctuation.LadderDuality

/-! # Spitzer's formula for the atom `p_a = P(M_a = 0)` (roadmap 1.4, step 2)

For the drift `-a` walk `S_n = W_n - a n` and `T_n` the first argmax of `S_0, …, S_n`:

* `{T_n = k} = {S_i < S_k ∀ i < k} ∩ {S_i - S_k ≤ 0 ∀ k ≤ i ≤ n}`, the two events being
  independent with the second having the law of `{T_{n-k} = 0}` (`measure_argmax_eq_mul`);
* `∑_k P(T_n = k) = 1` and `∑_k k P(T_n = k) = 𝔼T_n = ∑_{j ≤ n} P(S_j > 0)` (Sparre Andersen).

With `A_k = P(T_k = k)`, `B_m = P(T_m = 0) ↓ p_a`, `P_j = P(S_j > 0) = Φ(-a√j)`, the analytic
theorem `spitzer_limit_of_factorisation` yields

  `p_a = P(S_n ≤ 0 ∀ n) = exp(-∑_{n ≥ 1} Φ(-a√n)/n)`   (`eq:newconstantp`),

and by reflection `μ(posWalkSet X a) = p_a` (`measure_posWalkSet_eq_spitzer`).
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SwingRepair
open Fluctuation

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-! ### The event `{T_n = k}` -/

omit [MeasurableSpace Ω] in
theorem driftArgmaxUpTo_eq_iff' (a : ℝ) (n k : ℕ) (ω : Ω) :
    driftArgmaxUpTo X a n ω = k ↔
      k ≤ n ∧ (∀ i < k, negDriftWalk X a i ω < negDriftWalk X a k ω) ∧
        ∀ i, k ≤ i → i ≤ n → negDriftWalk X a i ω ≤ negDriftWalk X a k ω := by
  rw [driftArgmaxUpTo_eq_iff]
  simp only [IsFirstArgmax, List.length_range]
  constructor
  · rintro ⟨hk, h1, h2⟩
    refine ⟨hk, fun i hi => ?_, fun i hki hin => ?_⟩
    · have := h1 i hi
      rwa [psum_driftIncrement_of_le a (by omega), psum_driftIncrement_of_le a hk] at this
    · have := h2 i
      rwa [psum_driftIncrement_of_le a hin, psum_driftIncrement_of_le a hk] at this
  · rintro ⟨hk, h1, h2⟩
    refine ⟨hk, fun i hi => ?_, fun i => ?_⟩
    · rw [psum_driftIncrement_of_le a (by omega), psum_driftIncrement_of_le a hk]
      exact h1 i hi
    · rw [psum_driftIncrement, psum_driftIncrement_of_le a hk]
      rcases lt_or_ge i k with hik | hik
      · rw [min_eq_left (by omega)]
        exact (h1 i hik).le
      · exact h2 (min i n) (le_min hik hk) (min_le_right i n)

/-- `{S_i < S_k ∀ i < k}`: `k` is a strict ascending record epoch. -/
def strictRecordSet (X : ℕ → Ω → ℝ) (a : ℝ) (k : ℕ) : Set Ω :=
  {ω | ∀ i < k, negDriftWalk X a i ω < negDriftWalk X a k ω}

/-- `{S_{k+i} - S_k ≤ 0 ∀ i ≤ m}`, written through the increments `X_k, X_{k+1}, …`. -/
def futureNonposSet (X : ℕ → Ω → ℝ) (a : ℝ) (k m : ℕ) : Set Ω :=
  {ω | ∀ i ≤ m, negDriftWalk (fun j ω => X (k + j) ω) a i ω ≤ 0}

omit [MeasurableSpace Ω] in
theorem negDriftWalk_add_sub (a : ℝ) (k i : ℕ) (ω : Ω) :
    negDriftWalk X a (k + i) ω - negDriftWalk X a k ω =
      negDriftWalk (fun j ω => X (k + j) ω) a i ω := by
  simp only [negDriftWalk_eq, cumulativeSamples, Finset.sum_range_add, Nat.cast_add]
  ring

omit [MeasurableSpace Ω] in
theorem argmax_eq_self_iff (a : ℝ) (k : ℕ) (ω : Ω) :
    driftArgmaxUpTo X a k ω = k ↔ ω ∈ strictRecordSet X a k := by
  rw [driftArgmaxUpTo_eq_iff']
  simp only [strictRecordSet, mem_ofPred_eq, le_refl, true_and]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, fun i hki hik => ?_⟩
    have : i = k := le_antisymm hik hki
    rw [this]

omit [MeasurableSpace Ω] in
theorem argmax_eq_zero_iff (a : ℝ) (m : ℕ) (ω : Ω) :
    driftArgmaxUpTo X a m ω = 0 ↔ ω ∈ futureNonposSet X a 0 m := by
  rw [driftArgmaxUpTo_eq_iff']
  have h0 : negDriftWalk X a 0 ω = 0 := negDriftWalk_zero X a ω
  have hsh : ∀ i, negDriftWalk (fun j ω => X (0 + j) ω) a i ω = negDriftWalk X a i ω := by
    intro i; simp only [zero_add]
  constructor
  · rintro ⟨_, _, h⟩
    intro i hi
    show negDriftWalk (fun j ω => X (0 + j) ω) a i ω ≤ 0
    rw [hsh, ← h0]
    exact h i (Nat.zero_le i) hi
  · intro h
    have h' : ∀ i ≤ m, negDriftWalk (fun j ω => X (0 + j) ω) a i ω ≤ 0 := h
    refine ⟨Nat.zero_le m, fun i hi => absurd hi (Nat.not_lt_zero i), fun i _ hi => ?_⟩
    have := h' i hi
    rw [hsh] at this
    rw [h0]; exact this

omit [MeasurableSpace Ω] in
theorem argmax_eq_iff_inter (a : ℝ) {n k : ℕ} (hk : k ≤ n) (ω : Ω) :
    driftArgmaxUpTo X a n ω = k ↔
      ω ∈ strictRecordSet X a k ∩ futureNonposSet X a k (n - k) := by
  rw [driftArgmaxUpTo_eq_iff']
  simp only [strictRecordSet, futureNonposSet, mem_inter_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨_, h1, h2⟩
    refine ⟨h1, fun i hi => ?_⟩
    rw [← negDriftWalk_add_sub]
    have := h2 (k + i) (Nat.le_add_right k i) (by omega)
    linarith
  · rintro ⟨h1, h2⟩
    refine ⟨hk, h1, fun i hki hin => ?_⟩
    have := h2 (i - k) (by omega)
    rw [← negDriftWalk_add_sub] at this
    have hik : k + (i - k) = i := by omega
    rw [hik] at this
    linarith

/-! ### Measurability and independence -/

omit [MeasurableSpace Ω] in
theorem negDriftWalk_measurable_in {S : Set ℕ} {n : ℕ} (hS : ∀ j < n, j ∈ S) (a : ℝ) :
    Measurable[incrementIndexSpace X S] (negDriftWalk X a n) := by
  let : MeasurableSpace Ω := incrementIndexSpace X S
  unfold negDriftWalk gaussianDriftWalk cumulativeSamples
  apply Measurable.add_const
  apply Measurable.const_add
  exact Finset.measurable_sum _ (fun j hj => incrementIndexSpace_eval (hS j (Finset.mem_range.mp hj)))

omit [MeasurableSpace Ω] in
theorem strictRecordSet_measurable_in (a : ℝ) (k : ℕ) :
    MeasurableSet[incrementIndexSpace X (Iio k)] (strictRecordSet X a k) := by
  let : MeasurableSpace Ω := incrementIndexSpace X (Iio k)
  have : strictRecordSet X a k =
      ⋂ i, ⋂ (_ : i < k), {ω | negDriftWalk X a i ω < negDriftWalk X a k ω} := by
    ext ω; simp [strictRecordSet]
  rw [this]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun hi => measurableSet_lt ?_ ?_
  · exact negDriftWalk_measurable_in (fun j hj => by simp only [mem_Iio]; omega) a
  · exact negDriftWalk_measurable_in (fun j hj => by simp only [mem_Iio]; omega) a

omit [MeasurableSpace Ω] in
theorem futureNonposSet_measurable_in (a : ℝ) (k m : ℕ) :
    MeasurableSet[incrementIndexSpace X (Ici k)] (futureNonposSet X a k m) := by
  let : MeasurableSpace Ω := incrementIndexSpace X (Ici k)
  have : futureNonposSet X a k m =
      ⋂ i, ⋂ (_ : i ≤ m), {ω | negDriftWalk (fun j ω => X (k + j) ω) a i ω ≤ 0} := by
    ext ω; simp [futureNonposSet]
  rw [this]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
    measurableSet_le ?_ measurable_const
  unfold negDriftWalk gaussianDriftWalk cumulativeSamples
  apply Measurable.add_const
  apply Measurable.const_add
  exact Finset.measurable_sum _ (fun j _ => incrementIndexSpace_eval (show k + j ∈ Ici k by
    simp only [mem_Ici]; omega))

theorem measurableSet_strictRecordSet (hX : ∀ n, Measurable (X n)) (a : ℝ) (k : ℕ) :
    MeasurableSet (strictRecordSet X a k) :=
  incrementIndexSpace_le hX _ _ (strictRecordSet_measurable_in a k)

theorem measurableSet_futureNonposSet (hX : ∀ n, Measurable (X n)) (a : ℝ) (k m : ℕ) :
    MeasurableSet (futureNonposSet X a k m) :=
  incrementIndexSpace_le hX _ _ (futureNonposSet_measurable_in a k m)

/-- The canonical nonpositivity set on sequence space. -/
def canonicalNonposSet (a : ℝ) (m : ℕ) : Set (ℕ → ℝ) :=
  {v | ∀ i ≤ m, negDriftWalk (fun j (w : ℕ → ℝ) => w j) a i v ≤ 0}

theorem measurableSet_canonicalNonposSet (a : ℝ) (m : ℕ) :
    MeasurableSet (canonicalNonposSet a m) := by
  have : canonicalNonposSet a m = ⋂ i, ⋂ (_ : i ≤ m),
      {v : ℕ → ℝ | negDriftWalk (fun j (w : ℕ → ℝ) => w j) a i v ≤ 0} := by
    ext v; simp [canonicalNonposSet]
  rw [this]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
    measurableSet_le (negDriftWalk_measurable (fun k => measurable_pi_apply k) a i) measurable_const

omit [MeasurableSpace Ω] in
theorem futureNonposSet_eq_preimage (a : ℝ) (k m : ℕ) :
    futureNonposSet X a k m = (fun ω (n : ℕ) => X (k + n) ω) ⁻¹' canonicalNonposSet a m := by
  ext ω
  simp only [futureNonposSet, canonicalNonposSet, mem_preimage, mem_ofPred_eq]
  rfl

/-- `μ{S_{k+i} - S_k ≤ 0 ∀ i ≤ m} = μ{T_m = 0}` by shift invariance. -/
theorem measure_futureNonposSet (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (a : ℝ) (k m : ℕ) :
    μ (futureNonposSet X a k m) = μ (futureNonposSet X a 0 m) := by
  obtain ⟨hX', hi', hG'⟩ := iidGaussian_shift hX hi hG k
  rw [futureNonposSet_eq_preimage, futureNonposSet_eq_preimage]
  have h := iidGaussian_measure_functional_eq hX' hi' hG' hX hi hG
    (measurableSet_canonicalNonposSet a m)
  rw [h]
  congr 1
  ext ω
  simp

/-- **Factorisation at the first argmax.** -/
theorem measure_argmax_eq_mul (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (a : ℝ) {n k : ℕ} (hk : k ≤ n) :
    μ {ω | driftArgmaxUpTo X a n ω = k} =
      μ {ω | driftArgmaxUpTo X a k ω = k} * μ {ω | driftArgmaxUpTo X a (n - k) ω = 0} := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hset : {ω | driftArgmaxUpTo X a n ω = k} =
      strictRecordSet X a k ∩ futureNonposSet X a k (n - k) := by
    ext ω; exact argmax_eq_iff_inter a hk ω
  have hset1 : {ω | driftArgmaxUpTo X a k ω = k} = strictRecordSet X a k := by
    ext ω; exact argmax_eq_self_iff a k ω
  have hset2 : {ω | driftArgmaxUpTo X a (n - k) ω = 0} = futureNonposSet X a 0 (n - k) := by
    ext ω; exact argmax_eq_zero_iff a (n - k) ω
  rw [hset, hset1, hset2, ← measure_futureNonposSet hX hi hG a k (n - k)]
  have hdis : Disjoint (Iio k) (Ici k) := Iio_disjoint_Ici le_rfl
  have hind : Indep (incrementIndexSpace X (Iio k)) (incrementIndexSpace X (Ici k)) μ :=
    indep_iSup_of_disjoint (fun j => (hX j).comap_le) hi.iIndep hdis
  have hIS := hind.indepSet_of_measurableSet (strictRecordSet_measurable_in a k)
    (futureNonposSet_measurable_in a k (n - k))
  exact (indepSet_iff_measure_inter_eq_mul (measurableSet_strictRecordSet hX a k)
    (measurableSet_futureNonposSet hX a k (n - k)) μ).mp hIS

/-! ### The three sequences -/

/-- `A_k = P(T_k = k)`. -/
def recordProb (X : ℕ → Ω → ℝ) (μ : Measure Ω) (a : ℝ) (k : ℕ) : ℝ :=
  μ.real {ω | driftArgmaxUpTo X a k ω = k}

/-- `B_m = P(T_m = 0) = P(S_1 ≤ 0, …, S_m ≤ 0)`. -/
def nonposProb (X : ℕ → Ω → ℝ) (μ : Measure Ω) (a : ℝ) (m : ℕ) : ℝ :=
  μ.real {ω | driftArgmaxUpTo X a m ω = 0}

/-- `P_j = P(S_j > 0)`. -/
def posProb (X : ℕ → Ω → ℝ) (μ : Measure Ω) (a : ℝ) (j : ℕ) : ℝ :=
  μ.real {ω | 0 < negDriftWalk X a j ω}

omit [MeasurableSpace Ω] in
theorem argmax_zero_eq_univ (a : ℝ) : {ω | driftArgmaxUpTo X a 0 ω = 0} = univ := by
  ext ω
  simp only [mem_ofPred_eq, mem_univ, iff_true]
  exact Nat.le_zero.mp (driftArgmaxUpTo_le a 0 ω)

theorem recordProb_zero [IsProbabilityMeasure μ] (a : ℝ) : recordProb X μ a 0 = 1 := by
  unfold recordProb
  rw [argmax_zero_eq_univ, probReal_univ]

theorem nonposProb_zero [IsProbabilityMeasure μ] (a : ℝ) : nonposProb X μ a 0 = 1 := by
  unfold nonposProb
  rw [argmax_zero_eq_univ, probReal_univ]

theorem posProb_zero (a : ℝ) : posProb X μ a 0 = 0 := by
  unfold posProb
  have : {ω | 0 < negDriftWalk X a 0 ω} = ∅ := by
    ext ω; simp [negDriftWalk_zero]
  rw [this, measureReal_empty]

theorem recordProb_nonneg (a : ℝ) (k : ℕ) : 0 ≤ recordProb X μ a k := measureReal_nonneg
theorem nonposProb_nonneg (a : ℝ) (m : ℕ) : 0 ≤ nonposProb X μ a m := measureReal_nonneg
theorem posProb_nonneg (a : ℝ) (j : ℕ) : 0 ≤ posProb X μ a j := measureReal_nonneg

theorem recordProb_le_one [IsProbabilityMeasure μ] (a : ℝ) (k : ℕ) :
    recordProb X μ a k ≤ 1 := measureReal_le_one
theorem nonposProb_le_one [IsProbabilityMeasure μ] (a : ℝ) (m : ℕ) :
    nonposProb X μ a m ≤ 1 := measureReal_le_one

theorem nonposProb_antitone [IsProbabilityMeasure μ] (a : ℝ) : Antitone (nonposProb X μ a) := by
  refine antitone_nat_of_succ_le fun m => ?_
  unfold nonposProb
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  rw [mem_ofPred_eq, argmax_eq_zero_iff] at hω ⊢
  exact fun i hi => hω i (by omega)

omit [MeasurableSpace Ω] in
/-- `⋂_m {T_m = 0} = {S_i ≤ 0 ∀ i}`. -/
theorem iInter_argmax_zero (a : ℝ) :
    (⋂ m, {ω | driftArgmaxUpTo X a m ω = 0}) = {ω | ∀ i, negDriftWalk X a i ω ≤ 0} := by
  ext ω
  simp only [mem_iInter, mem_ofPred_eq]
  constructor
  · intro h i
    have := (argmax_eq_zero_iff a i ω).mp (h i) i le_rfl
    simpa using this
  · intro h m
    rw [argmax_eq_zero_iff]
    intro i _
    simpa using h i

theorem measurableSet_argmax_eq (hX : ∀ n, Measurable (X n)) (a : ℝ) (n k : ℕ) :
    MeasurableSet {ω | driftArgmaxUpTo X a n ω = k} :=
  driftArgmaxUpTo_measurable hX a n (measurableSet_singleton k)

theorem tendsto_nonposProb (hX : ∀ n, Measurable (X n)) [IsProbabilityMeasure μ] (a : ℝ) :
    Tendsto (nonposProb X μ a) atTop
      (𝓝 (μ.real {ω | ∀ i, negDriftWalk X a i ω ≤ 0})) := by
  have hanti : Antitone fun m => {ω | driftArgmaxUpTo X a m ω = 0} := by
    refine antitone_nat_of_succ_le fun m ω hω => ?_
    rw [mem_ofPred_eq, argmax_eq_zero_iff] at hω ⊢
    exact fun i hi => hω i (by omega)
  have h := tendsto_measure_iInter_atTop (μ := μ)
    (s := fun m => {ω | driftArgmaxUpTo X a m ω = 0})
    (fun m => (measurableSet_argmax_eq hX a m 0).nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  rw [iInter_argmax_zero] at h
  unfold nonposProb Measure.real
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h

/-- `P_j = Φ(-a√j)` for `j ≥ 1`. -/
theorem posProb_eq_gaussianTailSqrt (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (a : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    posProb X μ a j = gaussianTailSqrt a j := by
  unfold posProb
  rw [← measureReal_cumulativeSamples_gt hX hi hG a hj]
  congr 1
  ext ω
  simp only [mem_ofPred_eq, negDriftWalk_eq, sub_pos]

theorem summable_posProb (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) :
    Summable (posProb X μ a) := by
  rw [← summable_nat_add_iff 1]
  refine (summable_gaussianTailSqrt ha).congr fun n => ?_
  rw [posProb_eq_gaussianTailSqrt hX hi hG a (by omega)]

/-! ### The two convolution identities -/

theorem sum_recordProb_mul_nonposProb (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (a : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), recordProb X μ a k * nonposProb X μ a (n - k) = 1 := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hterm : ∀ k ∈ Finset.range (n + 1),
      recordProb X μ a k * nonposProb X μ a (n - k) = μ.real {ω | driftArgmaxUpTo X a n ω = k} := by
    intro k hk
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    unfold recordProb nonposProb Measure.real
    rw [← ENNReal.toReal_mul, ← measure_argmax_eq_mul hX hi hG a hk']
  rw [Finset.sum_congr rfl hterm]
  have hfib : ∀ k, {ω | driftArgmaxUpTo X a n ω = k} = driftArgmaxUpTo X a n ⁻¹' {k} := by
    intro k; ext ω; simp
  simp_rw [hfib, Measure.real]
  rw [← ENNReal.toReal_sum (fun k _ => measure_ne_top _ _),
    sum_measure_preimage_singleton _ (fun k _ => driftArgmaxUpTo_measurable hX a n
      (measurableSet_singleton k))]
  have : driftArgmaxUpTo X a n ⁻¹' ↑(Finset.range (n + 1)) = univ := by
    ext ω
    simp only [mem_preimage, Finset.coe_range, mem_Iio, mem_univ, iff_true]
    exact Nat.lt_succ_of_le (driftArgmaxUpTo_le a n ω)
  rw [this, measure_univ, ENNReal.toReal_one]

theorem sum_mul_recordProb_mul_nonposProb (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (a : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (k : ℝ) * recordProb X μ a k * nonposProb X μ a (n - k) =
      ∑ j ∈ Finset.range (n + 1), posProb X μ a j := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hterm : ∀ k ∈ Finset.range (n + 1),
      (k : ℝ) * recordProb X μ a k * nonposProb X μ a (n - k) =
        ((k : ℝ≥0∞) * μ {ω | driftArgmaxUpTo X a n ω = k}).toReal := by
    intro k hk
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    unfold recordProb nonposProb Measure.real
    rw [measure_argmax_eq_mul hX hi hG a hk', ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_natCast, mul_assoc]
  rw [Finset.sum_congr rfl hterm, ← ENNReal.toReal_sum (fun k _ =>
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top k) (measure_ne_top _ _)),
    ← lintegral_nat_eq_sum (driftArgmaxUpTo_measurable hX a n) (driftArgmaxUpTo_le a n),
    lintegral_driftArgmaxUpTo hX hi hG a n, ENNReal.toReal_sum (fun j _ => measure_ne_top _ _),
    Finset.sum_range_succ', posProb_zero, add_zero]
  rfl

/-! ### Spitzer's formula -/

/-- The Spitzer exponent `∑_{n ≥ 1} Φ(-a√n)/n`. -/
def spitzerExponent (a : ℝ) : ℝ := ∑' n : ℕ, gaussianTailSqrt a (n + 1 : ℕ) / (n + 1 : ℕ)

theorem tsum_posProb_div (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) :
    ∑' n : ℕ, posProb X μ a n / n = spitzerExponent a := by
  have hs : Summable fun n : ℕ => posProb X μ a n / n := by
    refine Summable.of_nonneg_of_le (fun n => div_nonneg (posProb_nonneg a n) (Nat.cast_nonneg n))
      (fun n => ?_) (summable_posProb hX hi hG ha)
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [posProb_zero]
    · rw [div_le_iff₀ (by exact_mod_cast hn)]
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [posProb_nonneg (X := X) (μ := μ) a n]
  rw [hs.tsum_eq_zero_add]
  simp only [posProb_zero, Nat.cast_zero, div_zero, zero_add, spitzerExponent]
  refine tsum_congr fun n => ?_
  rw [posProb_eq_gaussianTailSqrt hX hi hG a (by omega)]

/-- **Spitzer's formula for the atom**: `P(S_n ≤ 0 ∀ n) = exp(-∑_{n≥1} Φ(-a√n)/n)` for the
drift `-a` walk. -/
theorem measureReal_nonpos_walk_eq_spitzer (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) :
    μ.real {ω | ∀ i, negDriftWalk X a i ω ≤ 0} = Real.exp (-spitzerExponent a) := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  rw [← tsum_posProb_div hX hi hG ha]
  exact spitzer_limit_of_factorisation (recordProb_zero a) (recordProb_nonneg a)
    (recordProb_le_one a) (nonposProb_zero a) (nonposProb_nonneg a) (nonposProb_le_one a)
    (nonposProb_antitone a) (tendsto_nonposProb hX a) (posProb_nonneg a) (posProb_zero a)
    (summable_posProb hX hi hG ha) (sum_recordProb_mul_nonposProb hX hi hG a)
    (sum_mul_recordProb_mul_nonposProb hX hi hG a)

/-! ### Reflection to `posWalkSet` -/

/-- `P(S_i = c) = 0` for `i ≥ 1`. -/
theorem measure_cumulativeSamples_eq_zero (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {i : ℕ} (hi1 : 1 ≤ i) (c : ℝ) :
    μ {ω | cumulativeSamples X i ω = c} = 0 := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hl : HasLaw (cumulativeSamples X i) (gaussianReal 0 (i : ℝ≥0)) μ := by
    simpa [cumulativeSamples] using! gaussian_weighted_sum_hasLaw hX hi hG (Finset.range i) (fun _ => 1)
  have hset : {ω | cumulativeSamples X i ω = c} = cumulativeSamples X i ⁻¹' {c} := by
    ext ω; simp
  have hv : (i : ℝ≥0) ≠ 0 := by exact_mod_cast (show i ≠ 0 by omega)
  have : NullSingletonClass (gaussianReal 0 (i : ℝ≥0)) := nullSingletonClass_gaussianReal hv
  rw [hset, ← Measure.map_apply (cumulativeSamples_measurable hX i) (measurableSet_singleton c),
    hl.map_eq]
  exact measure_singleton c

/-- `μ(posWalkSet X a) = P(S_n ≥ 0 ∀ n)` for the reflected walk: the boundary event is null. -/
theorem measure_posWalkSet_eq_nonneg (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (a : ℝ) :
    μ (posWalkSet X a) = μ {ω | ∀ i, 0 ≤ gaussianDriftWalk X 0 a i ω} := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  refine measure_congr ?_
  have hnull : μ (⋃ i, ⋃ (_ : 1 ≤ i), {ω | gaussianDriftWalk X 0 a i ω = 0}) = 0 := by
    refine measure_iUnion_null fun i => measure_iUnion_null fun hi1 => ?_
    have : {ω | gaussianDriftWalk X 0 a i ω = 0} = {ω | cumulativeSamples X i ω = -(a * i)} := by
      ext ω
      simp only [mem_ofPred_eq, gaussianDriftWalk, zero_add]
      constructor <;> intro h <;> linarith
    rw [this]
    exact measure_cumulativeSamples_eq_zero hX hi hG hi1 _
  have hsub : ∀ ω, ω ∉ ⋃ i, ⋃ (_ : 1 ≤ i), {ω | gaussianDriftWalk X 0 a i ω = 0} →
      (ω ∈ posWalkSet X a ↔ ω ∈ {ω | ∀ i, 0 ≤ gaussianDriftWalk X 0 a i ω}) := by
    intro ω hω
    simp only [mem_iUnion, mem_ofPred_eq, not_exists] at hω
    simp only [posWalkSet, mem_ofPred_eq]
    constructor
    · intro h i
      rcases Nat.eq_zero_or_pos i with hi0 | hi0
      · subst hi0; simp [gaussianDriftWalk, cumulativeSamples]
      · exact (h i hi0).le
    · intro h i hi1
      exact lt_of_le_of_ne (h i) (fun heq => hω i hi1 heq.symm)
  have hae : ∀ᵐ ω ∂μ, ω ∉ ⋃ i, ⋃ (_ : 1 ≤ i), {ω | gaussianDriftWalk X 0 a i ω = 0} :=
    compl_mem_ae_iff.mpr hnull
  filter_upwards [hae] with ω hω
  exact propext (hsub ω hω)

/-- **`p_a = exp(-∑_{n≥1} Φ(-a√n)/n)`** for the ladder-height atom of the drift `+a` walk. -/
theorem measure_posWalkSet_eq_spitzer (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) :
    μ (posWalkSet X a) = ENNReal.ofReal (Real.exp (-spitzerExponent a)) := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  obtain ⟨hXn, hin, hGn⟩ := iidGaussian_neg hX hi hG
  have h := measureReal_nonpos_walk_eq_spitzer hXn hin hGn ha
  have hneg : ∀ i ω, negDriftWalk (fun k ω => -X k ω) a i ω = -gaussianDriftWalk X 0 a i ω := by
    intro i ω
    simp only [negDriftWalk_eq, gaussianDriftWalk, cumulativeSamples, Finset.sum_neg_distrib,
      zero_add]
    ring
  have hset : {ω | ∀ i, negDriftWalk (fun k ω => -X k ω) a i ω ≤ 0} =
      {ω | ∀ i, 0 ≤ gaussianDriftWalk X 0 a i ω} := by
    ext ω
    simp only [mem_ofPred_eq, hneg, neg_nonpos]
  rw [hset] at h
  rw [measure_posWalkSet_eq_nonneg hX hi hG a, ← h, ofReal_measureReal]

theorem measureReal_posWalkSet_eq_spitzer (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) :
    μ.real (posWalkSet X a) = Real.exp (-spitzerExponent a) := by
  rw [Measure.real, measure_posWalkSet_eq_spitzer hX hi hG ha,
    ENNReal.toReal_ofReal (Real.exp_pos _).le]

theorem measure_posWalkSet_pos (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) :
    μ (posWalkSet X a) ≠ 0 := by
  rw [measure_posWalkSet_eq_spitzer hX hi hG ha]
  exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'

end SwingRepair
