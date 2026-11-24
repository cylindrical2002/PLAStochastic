import PLAStochastic.ForMathlib.Probability.RandomWalk.Fluctuation.SparreAndersenIID
import PLAStochastic.Swing.ConstantEvaluation.Fluctuation.DriftMaximum

/-! # Sparre Andersen for the drifted Gaussian walk (roadmap 1.2, target C)

Apply `measure_posCount_eq_measure_isFirstArgmax` to the i.i.d. increments `X_i - a`.
With `S_j = W_j - a j`, the first argmax `T_n` of `S_0, …, S_n` satisfies
`𝔼 T_n = 𝔼 N_n = ∑_{j=1}^n P(S_j > 0)`; `T_n` is nondecreasing in `n` and equals `τ*_a`
(`driftArgmax`) once `n ≥ τ*_a`.  Monotone convergence gives

  `𝔼 τ*_a = ∑_{n ≥ 1} P(W_n > a n)`  and  `τ*_a` integrable,

i.e. the named input `SparreAndersenArgmax X μ` of `overshootMeanLipschitz_of_inputs`.
-/
noncomputable section
open Classical MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology List
namespace SwingRepair

open Fluctuation

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-! ### Partial sums along `range n` -/

theorem list_sum_map_range (g : ℕ → ℝ) (j : ℕ) :
    ((List.range j).map g).sum = ∑ i ∈ Finset.range j, g i := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, ih]
    simp

theorem psum_range (g : ℕ → ℝ) (n j : ℕ) :
    psum g (List.range n) j = ∑ i ∈ Finset.range (min j n), g i := by
  rw [psum, List.take_range, list_sum_map_range]

/-- The drifted increments. -/
def driftIncrement (X : ℕ → Ω → ℝ) (a : ℝ) (i : ℕ) (ω : Ω) : ℝ := X i ω - a

omit [MeasurableSpace Ω] in
theorem psum_driftIncrement (a : ℝ) (n j : ℕ) (ω : Ω) :
    psum (fun i => driftIncrement X a i ω) (List.range n) j = negDriftWalk X a (min j n) ω := by
  rw [psum_range, negDriftWalk_eq, cumulativeSamples]
  simp [driftIncrement, Finset.sum_sub_distrib, mul_comm]

omit [MeasurableSpace Ω] in
theorem psum_driftIncrement_of_le (a : ℝ) {n j : ℕ} (hj : j ≤ n) (ω : Ω) :
    psum (fun i => driftIncrement X a i ω) (List.range n) j = negDriftWalk X a j ω := by
  rw [psum_driftIncrement, min_eq_left hj]

/-! ### The first argmax over `[0, n]` -/

theorem exists_isFirstArgmax {ι : Type*} (x : ι → ℝ) (p : List ι) : ∃ k, IsFirstArgmax x p k := by
  obtain ⟨k₀, hk₀, hmax⟩ := Finset.exists_max_image (Finset.range (p.length + 1))
    (fun i => psum x p i) ⟨0, by simp⟩
  have hk₀' : k₀ ≤ p.length := by simpa [Nat.lt_succ_iff] using hk₀
  have hglob : ∀ j, psum x p j ≤ psum x p k₀ := by
    intro j
    rcases Nat.lt_or_ge j (p.length + 1) with hj | hj
    · exact hmax j (Finset.mem_range.mpr hj)
    · rw [psum_of_length_le x (by omega)]
      have := hmax p.length (by simp)
      rwa [psum_length] at this
  have hex : ∃ k, ∀ j, psum x p j ≤ psum x p k := ⟨k₀, hglob⟩
  refine ⟨Nat.find hex, ?_, fun i hi => ?_, Nat.find_spec hex⟩
  · exact (Nat.find_min' hex hglob).trans hk₀'
  · have := Nat.find_min hex hi
    push Not at this
    obtain ⟨j, hj⟩ := this
    exact lt_of_lt_of_le hj (Nat.find_spec hex j)

theorem isFirstArgmax_unique {ι : Type*} {x : ι → ℝ} {p : List ι} {k k' : ℕ}
    (h : IsFirstArgmax x p k) (h' : IsFirstArgmax x p k') : k = k' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have h1 := h'.2.1 k hlt
    have h2 := h.2.2 k'
    linarith
  · have h1 := h.2.1 k' hlt
    have h2 := h'.2.2 k
    linarith

/-- `T_n`: the first argmax of `S_0, …, S_n` for the drifted walk. -/
def driftArgmaxUpTo (X : ℕ → Ω → ℝ) (a : ℝ) (n : ℕ) (ω : Ω) : ℕ :=
  Nat.find (exists_isFirstArgmax (fun i => driftIncrement X a i ω) (List.range n))

omit [MeasurableSpace Ω] in
theorem driftArgmaxUpTo_spec (a : ℝ) (n : ℕ) (ω : Ω) :
    IsFirstArgmax (fun i => driftIncrement X a i ω) (List.range n) (driftArgmaxUpTo X a n ω) :=
  Nat.find_spec _

omit [MeasurableSpace Ω] in
theorem driftArgmaxUpTo_eq_iff (a : ℝ) (n : ℕ) (ω : Ω) (k : ℕ) :
    driftArgmaxUpTo X a n ω = k ↔
      IsFirstArgmax (fun i => driftIncrement X a i ω) (List.range n) k := by
  constructor
  · rintro rfl; exact driftArgmaxUpTo_spec a n ω
  · intro h; exact isFirstArgmax_unique (driftArgmaxUpTo_spec a n ω) h

omit [MeasurableSpace Ω] in
theorem driftArgmaxUpTo_le (a : ℝ) (n : ℕ) (ω : Ω) : driftArgmaxUpTo X a n ω ≤ n := by
  have := (driftArgmaxUpTo_spec (X := X) a n ω).1
  simpa using this

omit [MeasurableSpace Ω] in
/-- `T_n` is nondecreasing in `n`. -/
theorem driftArgmaxUpTo_mono (a : ℝ) (ω : Ω) : Monotone fun n => driftArgmaxUpTo X a n ω := by
  refine monotone_nat_of_le_succ fun n => ?_
  set k := driftArgmaxUpTo X a n ω with hk
  set k' := driftArgmaxUpTo X a (n + 1) ω with hk'
  have h := driftArgmaxUpTo_spec (X := X) a n ω
  have h' := driftArgmaxUpTo_spec (X := X) a (n + 1) ω
  rw [← hk] at h
  rw [← hk'] at h'
  by_contra hlt
  push Not at hlt
  have hkn : k ≤ n := driftArgmaxUpTo_le a n ω
  -- `S_{k'} < S_k` from `T_n = k`, `S_k ≤ S_{k'}` from `T_{n+1} = k'`
  have h1 := h.2.1 k' hlt
  have h2 := h'.2.2 k
  rw [psum_driftIncrement_of_le a (by omega), psum_driftIncrement_of_le a hkn] at h1
  rw [psum_driftIncrement_of_le a (by omega), psum_driftIncrement_of_le a (by omega)] at h2
  linarith

omit [MeasurableSpace Ω] in
/-- Once `n ≥ τ*_a`, `T_n = τ*_a` (when the maximum is attained). -/
theorem driftArgmaxUpTo_eq_driftArgmax {a : ℝ} {ω : Ω} (h : DriftMaxAttained X a ω) {n : ℕ}
    (hn : driftArgmax X a ω ≤ n) : driftArgmaxUpTo X a n ω = driftArgmax X a ω := by
  rw [driftArgmaxUpTo_eq_iff]
  set τ := driftArgmax X a ω with hτ
  refine ⟨by simpa using hn, fun i hi => ?_, fun i => ?_⟩
  · rw [psum_driftIncrement_of_le a (by omega), psum_driftIncrement_of_le a hn]
    -- `i < τ` is not a global argmax
    have hnot : ¬ ∀ m, negDriftWalk X a m ω ≤ negDriftWalk X a i ω := by
      intro hcontra
      have : τ ≤ i := by
        rw [hτ]
        unfold driftArgmax
        rw [dif_pos h]
        exact Nat.find_min' h hcontra
      omega
    push Not at hnot
    obtain ⟨m, hm⟩ := hnot
    exact lt_of_lt_of_le hm (driftArgmax_spec h m)
  · rw [psum_driftIncrement, psum_driftIncrement_of_le a hn]
    exact driftArgmax_spec h _

omit [MeasurableSpace Ω] in
theorem iSup_driftArgmaxUpTo {a : ℝ} {ω : Ω} (h : DriftMaxAttained X a ω) :
    (⨆ n, (driftArgmaxUpTo X a n ω : ℝ≥0∞)) = (driftArgmax X a ω : ℝ≥0∞) := by
  apply le_antisymm
  · refine iSup_le fun n => ?_
    -- `T_n ≤ T_{max n τ} = τ`
    have hmono : driftArgmaxUpTo X a n ω ≤ driftArgmaxUpTo X a (max n (driftArgmax X a ω)) ω :=
      driftArgmaxUpTo_mono (X := X) a ω (le_max_left n (driftArgmax X a ω))
    rw [driftArgmaxUpTo_eq_driftArgmax h (le_max_right _ _)] at hmono
    exact_mod_cast hmono
  · exact le_iSup_of_le (driftArgmax X a ω) (by rw [driftArgmaxUpTo_eq_driftArgmax h le_rfl])

/-! ### Measurability -/

theorem measurable_psum_driftIncrement (hX : ∀ n, Measurable (X n)) (a : ℝ) (n j : ℕ) :
    Measurable fun ω => psum (fun i => driftIncrement X a i ω) (List.range n) j := by
  have : (fun ω => psum (fun i => driftIncrement X a i ω) (List.range n) j) =
      fun ω => negDriftWalk X a (min j n) ω := by
    funext ω; exact psum_driftIncrement a n j ω
  rw [this]
  exact negDriftWalk_measurable hX a _

theorem measurableSet_isFirstArgmax_driftIncrement (hX : ∀ n, Measurable (X n)) (a : ℝ)
    (n k : ℕ) :
    MeasurableSet {ω | IsFirstArgmax (fun i => driftIncrement X a i ω) (List.range n) k} := by
  have : {ω | IsFirstArgmax (fun i => driftIncrement X a i ω) (List.range n) k} =
      {ω | k ≤ n} ∩ ((⋂ i, ⋂ (_ : i < k), {ω | psum (fun i => driftIncrement X a i ω) (List.range n) i <
          psum (fun i => driftIncrement X a i ω) (List.range n) k}) ∩
        ⋂ i, {ω | psum (fun i => driftIncrement X a i ω) (List.range n) i ≤
          psum (fun i => driftIncrement X a i ω) (List.range n) k}) := by
    ext ω
    simp [IsFirstArgmax]
  rw [this]
  refine MeasurableSet.inter (by by_cases h : k ≤ n <;> simp [h]) (MeasurableSet.inter ?_ ?_)
  · exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
      measurableSet_lt (measurable_psum_driftIncrement hX a n i) (measurable_psum_driftIncrement hX a n k)
  · exact MeasurableSet.iInter fun i =>
      measurableSet_le (measurable_psum_driftIncrement hX a n i) (measurable_psum_driftIncrement hX a n k)

theorem driftArgmaxUpTo_measurable (hX : ∀ n, Measurable (X n)) (a : ℝ) (n : ℕ) :
    Measurable (driftArgmaxUpTo X a n) := by
  apply measurable_to_countable'
  intro k
  have : driftArgmaxUpTo X a n ⁻¹' {k} =
      {ω | IsFirstArgmax (fun i => driftIncrement X a i ω) (List.range n) k} := by
    ext ω
    simp only [mem_preimage, mem_singleton_iff, mem_ofPred_eq]
    exact driftArgmaxUpTo_eq_iff a n ω k
  rw [this]
  exact measurableSet_isFirstArgmax_driftIncrement hX a n k

/-! ### Expectations of `N_n` and `T_n` -/

/-- `∫⁻ g = ∑_{k ≤ n} k μ{g = k}` for a measurable `ℕ`-valued `g ≤ n`. -/
theorem lintegral_nat_eq_sum {g : Ω → ℕ} (hg : Measurable g) {n : ℕ} (hle : ∀ ω, g ω ≤ n) :
    (∫⁻ ω, (g ω : ℝ≥0∞) ∂μ) = ∑ k ∈ Finset.range (n + 1), (k : ℝ≥0∞) * μ {ω | g ω = k} := by
  have hpt : ∀ ω, (g ω : ℝ≥0∞) =
      ∑ k ∈ Finset.range (n + 1), (k : ℝ≥0∞) * {ω | g ω = k}.indicator (1 : Ω → ℝ≥0∞) ω := by
    intro ω
    rw [Finset.sum_eq_single (g ω)]
    · simp
    · intro k _ hk
      simp [Ne.symm hk]
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le (hle ω))) h
  have hk : ∀ k, MeasurableSet {ω | g ω = k} := fun k => hg (measurableSet_singleton k)
  simp_rw [hpt]
  rw [lintegral_finsetSum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [lintegral_const_mul _ (measurable_one.indicator (hk k)), lintegral_indicator_one (hk k)]
  · intro k _
    exact (measurable_one.indicator (hk k)).const_mul _

theorem posCount_range_eq_sum (g : ℕ → ℝ) (n : ℕ) :
    posCount g (List.range n) =
      ∑ j ∈ Finset.range n, if 0 < psum g (List.range n) (j + 1) then 1 else 0 := by
  simp only [posCount, List.length_range]
  rw [Finset.card_filter]

theorem measurable_posCount_driftIncrement (hX : ∀ n, Measurable (X n)) (a : ℝ) (n : ℕ) :
    Measurable fun ω => posCount (fun i => driftIncrement X a i ω) (List.range n) := by
  simp_rw [posCount_range_eq_sum]
  refine Finset.measurable_sum _ fun j _ => Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_lt measurable_const (measurable_psum_driftIncrement hX a n (j + 1))

theorem lintegral_posCount_driftIncrement (hX : ∀ n, Measurable (X n)) (a : ℝ) (n : ℕ) :
    (∫⁻ ω, (posCount (fun i => driftIncrement X a i ω) (List.range n) : ℝ≥0∞) ∂μ) =
      ∑ j ∈ Finset.range n, μ {ω | 0 < negDriftWalk X a (j + 1) ω} := by
  have hpt : ∀ ω, (posCount (fun i => driftIncrement X a i ω) (List.range n) : ℝ≥0∞) =
      ∑ j ∈ Finset.range n, {ω | 0 < negDriftWalk X a (j + 1) ω}.indicator (1 : Ω → ℝ≥0∞) ω := by
    intro ω
    rw [posCount_range_eq_sum, Nat.cast_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [psum_driftIncrement_of_le a (by omega), Set.indicator_apply]
    simp only [mem_ofPred_eq, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Pi.one_apply]
  simp_rw [hpt]
  rw [lintegral_finsetSum]
  · refine Finset.sum_congr rfl fun j _ => ?_
    exact lintegral_indicator_one (measurableSet_lt measurable_const (negDriftWalk_measurable hX a _))
  · intro j _
    exact measurable_one.indicator (measurableSet_lt measurable_const (negDriftWalk_measurable hX a _))

theorem driftIncrement_measurable (hX : ∀ n, Measurable (X n)) (a : ℝ) (i : ℕ) :
    Measurable (driftIncrement X a i) := (hX i).sub_const a

/-- The drifted increments are i.i.d. -/
theorem driftIncrement_iIndepFun (hi : iIndepFun X μ) (a : ℝ) :
    iIndepFun (driftIncrement X a) μ :=
  hi.comp (fun _ z => z - a) fun _ => measurable_sub_const a

theorem driftIncrement_map (hX : ∀ n, Measurable (X n))
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (a : ℝ) (i : ℕ) :
    μ.map (driftIncrement X a i) = (gaussianReal 0 1).map (fun z => z - a) := by
  have : driftIncrement X a i = (fun z => z - a) ∘ X i := rfl
  rw [this, ← Measure.map_map (measurable_sub_const a) (hX i), hG i]

/-- **`𝔼 T_n = ∑_{j=1}^n P(S_j > 0)`.** -/
theorem lintegral_driftArgmaxUpTo (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (a : ℝ) (n : ℕ) :
    (∫⁻ ω, (driftArgmaxUpTo X a n ω : ℝ≥0∞) ∂μ) =
      ∑ j ∈ Finset.range n, μ {ω | 0 < negDriftWalk X a (j + 1) ω} := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  rw [lintegral_nat_eq_sum (driftArgmaxUpTo_measurable hX a n) (driftArgmaxUpTo_le a n),
    ← lintegral_posCount_driftIncrement hX a n,
    lintegral_nat_eq_sum (measurable_posCount_driftIncrement hX a n)
      (fun ω => by simpa using posCount_le_length (fun i => driftIncrement X a i ω) (List.range n))]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  have hSA := measure_posCount_eq_measure_isFirstArgmax (driftIncrement_measurable hX a)
    (driftIncrement_iIndepFun hi a) (driftIncrement_map hX hG a) n k
  rw [hSA]
  congr 1
  ext ω
  simp only [mem_ofPred_eq]
  exact driftArgmaxUpTo_eq_iff a n ω k

/-! ### Passage to `τ*_a` -/

/-- `𝔼 τ*_a = ∑_{n ≥ 1} P(W_n > a n)` in `ℝ≥0∞`. -/
theorem lintegral_driftArgmax (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) :
    (∫⁻ ω, (driftArgmax X a ω : ℝ≥0∞) ∂μ) =
      ∑' n : ℕ, μ {ω | a * ((n + 1 : ℕ) : ℝ) < cumulativeSamples X (n + 1) ω} := by
  have hae : ∀ᵐ ω ∂μ, (driftArgmax X a ω : ℝ≥0∞) = ⨆ n, (driftArgmaxUpTo X a n ω : ℝ≥0∞) := by
    filter_upwards [driftMaxAttained_ae hX hi hG ha] with ω h
    exact (iSup_driftArgmaxUpTo h).symm
  rw [lintegral_congr_ae hae, lintegral_iSup]
  · simp_rw [lintegral_driftArgmaxUpTo hX hi hG a]
    rw [ENNReal.tsum_eq_iSup_nat]
    congr 1
    funext n
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    ext ω
    simp only [mem_ofPred_eq, negDriftWalk_eq, sub_pos, Nat.cast_add, Nat.cast_one]
  · intro n
    exact measurable_from_nat.comp (driftArgmaxUpTo_measurable hX a n)
  · intro n m hnm ω
    show ((driftArgmaxUpTo X a n ω : ℕ) : ℝ≥0∞) ≤ ((driftArgmaxUpTo X a m ω : ℕ) : ℝ≥0∞)
    exact_mod_cast driftArgmaxUpTo_mono (X := X) a ω hnm

/-- The series `∑ P(W_n > a n)` is finite (it is `∑ Φ(-a√n) ≤ 1/(2a²)`). -/
theorem tsum_measure_cumulativeSamples_gt_ne_top (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) :
    (∑' n : ℕ, μ {ω | a * ((n + 1 : ℕ) : ℝ) < cumulativeSamples X (n + 1) ω}) ≠ ∞ := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have heq : ∀ n : ℕ, μ {ω | a * ((n + 1 : ℕ) : ℝ) < cumulativeSamples X (n + 1) ω} =
      ENNReal.ofReal (gaussianTailSqrt a (n + 1 : ℕ)) := by
    intro n
    rw [← measureReal_cumulativeSamples_gt hX hi hG a (n := n + 1) (by omega), ofReal_measureReal]
  simp_rw [heq]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => gaussianTailSqrt_nonneg a _)
    (summable_gaussianTailSqrt ha)]
  exact ENNReal.ofReal_ne_top

/-- **Sparre Andersen for `τ*_a`**: the named input of `overshootMeanLipschitz_of_inputs`. -/
theorem sparreAndersenArgmax_gaussian (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) : SparreAndersenArgmax X μ := by
  intro a ha
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hmeas : Measurable fun ω => (driftArgmax X a ω : ℝ) :=
    measurable_from_nat.comp (driftArgmax_measurable hX a)
  have hlint := lintegral_driftArgmax hX hi hG ha
  have hfin := tsum_measure_cumulativeSamples_gt_ne_top hX hi hG ha
  have hint : Integrable (fun ω => (driftArgmax X a ω : ℝ)) μ := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω => Nat.cast_nonneg _)]
    simp_rw [ENNReal.ofReal_natCast]
    rw [hlint]
    exact hfin.lt_top
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => Nat.cast_nonneg _)
    hmeas.aestronglyMeasurable]
  simp_rw [ENNReal.ofReal_natCast]
  rw [hlint, ENNReal.tsum_toReal_eq (fun n => measure_ne_top _ _)]
  rfl

/-- With Sparre Andersen proved, the two-sided bound on `β` rests on the mean identity alone. -/
theorem overshootMean_bounds_of_identity (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (hid : OvershootMeanIdentity X μ)
    {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) :
    1 / 2 * (c - a) ≤ overshootMean X μ c - overshootMean X μ a ∧
      overshootMean X μ c - overshootMean X μ a ≤ 3 / 4 * (c - a) :=
  overshootMean_bounds_of_identity_sparreAndersen hX hi hG hid
    (sparreAndersenArgmax_gaussian hX hi hG) ha hac

/-- **`OvershootMeanIdentity X μ ⇒ OvershootMeanLipschitz X μ (3/4)`.** -/
theorem overshootMeanLipschitz_of_identity (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (hid : OvershootMeanIdentity X μ) :
    OvershootMeanLipschitz X μ (3 / 4) :=
  overshootMeanLipschitz_of_inputs hX hi hG hid (sparreAndersenArgmax_gaussian hX hi hG)

end SwingRepair
