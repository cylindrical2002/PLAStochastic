import PLAStochastic.Index.OneLayer.Bracket
import PLAStochastic.Index.Model.IIDPairs
import PLAStochastic.Index.Algorithm.Segmentation

/-!
# Concentration of the ALG-OPT segment count of an iid walk

For iid gaps `hX : GapLaw P X μ σ κ` and `eps > 0`, `segCount eps X K ω` is the number of
ALG-OPT segments on the first `K` keys `gapKeys (seq X ω) 0, …, gapKeys (seq X ω) (K - 1)`,
and `G = μ² eps² / σ²`.

* **Renewal representation.**  With the restart map `gapShift eps = shiftBy (gapSegLen eps)`
  the `i`-th segment of the infinite run has length
  `blockLen eps X i ω = gapSegLen eps ((gapShift eps)^[i] (seq X ω))`.  If all these lengths
  are finite, the infinite cuts are their partial sums (`cut_gapKeys`), hence
  `k < segCount ↔ ∑_{i<k} (blockLen i).toNat < K` (`lt_segCount_iff`, `ae_lt_segCount_iff`).
  If the first segment is almost surely finite, the lengths are iid with the law of
  `layerSegLen eps X` (`iIndepFun_blockLen`, `identDistrib_blockLen`, `ae_blockLen_ne_top`),
  so `E ∏_{i<k} f(T_i) = (E f(T))^k` (`lintegral_prod_blockLen`).
* **Upper tail.**  Under `GapLaw` the first segment is almost surely finite for every
  `eps ≥ 0` (`layerSegLen_ae_lt_top`).  If `P(T ≤ n₀) ≤ 1/64` and `2 K ≤ k (n₀ + 1)`, then
  `P(k < segCount) ≤ (1/4)^k` (`measureReal_lt_segCount_le_of_small`): on the event fewer than
  `k/2` blocks exceed `n₀`, so the product of the weights `8·1{T_i ≤ n₀} + (1/8)·1{T_i > n₀}`
  is at least `1`, and its mean is at most `(1/4)^k`.  With `n₀ = ⌊G/64⌋₊` the hypothesis
  holds (`measureReal_layerSegLen_le_floor`, `measureReal_lt_segCount_le`).
* **Lower tail.**  Under the geometric block tail `P(j L < T) ≤ r^j` (`L ≥ 1`, `0 < r < 1`),
  with `θ = expRate r = (1/2) log (1/r)` and `B' = expBound r = 1 + (e^θ - 1)/(1 - r e^θ)`:
  `E exp(θ T / L) ≤ B'` (`lintegral_exp_le_of_tail`) and
  `P(segCount ≤ k) ≤ exp(-θ K / L) B'^k` (`measureReal_segCount_le_le`).
* **Clean corollaries.**  For every `eps > 0` and natural `t`,
  `P(segCount > 128 K / G + t + 1) ≤ (1/4)^t` (`measureReal_segCount_gt_le`).  Under the
  large-`eps` conditions of `oneLayer_bracket`, with
  `aLow = expRate (71/72) / (2 · 5185 · log (expBound (71/72))) > 0`,
  `P(segCount < aLow K / G - t) ≤ exp(-(log (expBound (71/72))) t)`
  (`measureReal_segCount_lt_le_of_large`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

/-! ## The renewal representation of the ALG-OPT cuts -/

/-- Restart of a gap sequence after its first ALG-OPT segment. -/
def gapShift (eps : ℝ) : (ℕ → ℝ) → (ℕ → ℝ) := shiftBy (gapSegLen eps)

/-- The partial sums of the successive block lengths of a gap sequence. -/
def gapBlockStart (eps : ℝ) (g : ℕ → ℝ) (j : ℕ) : ℕ :=
  ∑ i ∈ range j, (gapSegLen eps ((gapShift eps)^[i] g)).toNat

theorem gapBlockStart_succ (eps : ℝ) (g : ℕ → ℝ) (j : ℕ) :
    gapBlockStart eps g (j + 1) =
      gapBlockStart eps g j + (gapSegLen eps ((gapShift eps)^[j] g)).toNat := by
  simp [gapBlockStart, sum_range_succ]

/-- The iterated restart is the gap sequence seen from the block start. -/
theorem gapShift_iterate (eps : ℝ) (g : ℕ → ℝ) :
    ∀ j, (gapShift eps)^[j] g = fun t => g (gapBlockStart eps g j + t)
  | 0 => by funext t; simp [gapBlockStart]
  | j + 1 => by
    have key : ∀ u, (gapShift eps)^[j] g u = g (gapBlockStart eps g j + u) :=
      fun u => congrFun (gapShift_iterate eps g j) u
    rw [Function.iterate_succ_apply']
    funext t
    show (gapShift eps)^[j] g ((gapSegLen eps ((gapShift eps)^[j] g)).toNat + t) = _
    rw [key, gapBlockStart_succ, add_assoc]

/-- If all blocks are finite, the infinite ALG-OPT cuts of the keys are the block starts. -/
theorem cut_gapKeys (eps : ℝ) {g : ℕ → ℝ}
    (hfin : ∀ i, gapSegLen eps ((gapShift eps)^[i] g) ≠ ⊤) :
    ∀ j, cut eps (gapKeys g) j = (gapBlockStart eps g j : ℕ∞)
  | 0 => by simp [cut, gapBlockStart]
  | j + 1 => by
    rw [cut, cut_gapKeys eps hfin j, ENat.toNat_natCast]
    have hs : shiftSeq (gapKeys g) (gapBlockStart eps g j) =
        fun i => gapKeys g (gapBlockStart eps g j + i) := rfl
    rw [hs, segLen_gapKeys_shift, ← gapShift_iterate eps g j, gapBlockStart_succ,
      Nat.cast_add, ENat.natCast_toNat (hfin j)]

theorem gapBlockStart_mono (eps : ℝ) (g : ℕ → ℝ) : Monotone (gapBlockStart eps g) :=
  monotone_nat_of_le_succ fun j => by rw [gapBlockStart_succ]; omega

theorem le_gapBlockStart {eps : ℝ} (heps : 0 ≤ eps) {g : ℕ → ℝ}
    (hfin : ∀ i, gapSegLen eps ((gapShift eps)^[i] g) ≠ ⊤) : ∀ j, j ≤ gapBlockStart eps g j
  | 0 => Nat.zero_le _
  | j + 1 => by
    rw [gapBlockStart_succ]
    have h1 : (1 : ℕ∞) ≤ gapSegLen eps ((gapShift eps)^[j] g) := one_le_segLen heps _
    rw [← ENat.natCast_toNat (hfin j)] at h1
    have h1' : 1 ≤ (gapSegLen eps ((gapShift eps)^[j] g)).toNat := by exact_mod_cast h1
    have := le_gapBlockStart heps hfin j
    omega

/-- **Renewal representation of the count.**  If all blocks are finite, the `k`-th segment
of ALG-OPT on the first `K` keys exists iff the first `k` blocks end before `K`. -/
theorem lt_finSegCount_gapKeys_iff {eps : ℝ} (heps : 0 ≤ eps) {g : ℕ → ℝ}
    (hfin : ∀ i, gapSegLen eps ((gapShift eps)^[i] g) ≠ ⊤) (K k : ℕ) :
    k < finSegCount eps (gapKeys g) K ↔ gapBlockStart eps g k < K := by
  classical
  set b := gapBlockStart eps g with hb
  have hcut : ∀ j, finCut eps (gapKeys g) K j = min (b j) K := by
    intro j
    have h2 := finCut_eq_min eps (gapKeys g) K j
    rw [cut_gapKeys eps hfin j] at h2
    rcases le_total (b j) K with hle | hle
    · rw [min_eq_left (by exact_mod_cast hle)] at h2
      rw [min_eq_left hle]; exact_mod_cast h2
    · rw [min_eq_right (by exact_mod_cast hle)] at h2
      rw [min_eq_right hle]; exact_mod_cast h2
  unfold finSegCount
  have hpred : (fun j => finCut eps (gapKeys g) K j < K) = fun j => b j < K := by
    funext j; rw [hcut]; exact propext ⟨fun h => by omega, fun h => by omega⟩
  simp only [hpred]
  have hnot : ¬ b (K + 1) < K := by
    have : K + 1 ≤ b (K + 1) := le_gapBlockStart heps hfin (K + 1)
    omega
  rw [count_eq_find_of_downward
    (fun j hj => lt_of_le_of_lt (gapBlockStart_mono eps g (Nat.le_succ j)) hj) hnot,
    Nat.lt_find_iff]
  constructor
  · intro h; exact not_not.mp (h k le_rfl)
  · intro h m hm; exact not_not.mpr (lt_of_le_of_lt (gapBlockStart_mono eps g hm) h)

/-! ## The block lengths of an iid walk -/

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ} {μ σ κ : ℝ}

/-- Number of ALG-OPT segments on the first `K` keys of the walk with gaps `X`. -/
def segCount (eps : ℝ) (X : ℕ → Ω → ℝ) (K : ℕ) (ω : Ω) : ℕ :=
  finSegCount eps (gapKeys (seq X ω)) K

/-- Length of the `i`-th segment of the infinite ALG-OPT run on the walk with gaps `X`. -/
def blockLen (eps : ℝ) (X : ℕ → Ω → ℝ) (i : ℕ) (ω : Ω) : ℕ∞ :=
  gapSegLen eps ((gapShift eps)^[i] (seq X ω))

omit mΩ in
theorem blockLen_zero (eps : ℝ) (X : ℕ → Ω → ℝ) : blockLen eps X 0 = layerSegLen eps X := rfl

theorem measurable_blockLen (hX : IIDSeq P X) (eps : ℝ) (i : ℕ) :
    Measurable (blockLen eps X i) :=
  (isStoppingRule_gapSegLen eps).measurable.comp
    (((measurable_shiftBy (isStoppingRule_gapSegLen eps)).iterate i).comp
      (measurable_seq hX.measurable))

/-- The block lengths are independent. -/
theorem iIndepFun_blockLen [IsProbabilityMeasure P] (hX : IIDSeq P X) {eps : ℝ}
    (hfin : ∀ᵐ ω ∂P, layerSegLen eps X ω < ⊤) : iIndepFun (blockLen eps X) P :=
  iIndepFun_rewards hX.measurable hX.indep hX.ident (isStoppingRule_gapSegLen eps)
    (hfin.mono fun _ h => h.ne) (isStoppingRule_gapSegLen eps).measurable
    fun _ _ h _ => h

/-- The block lengths have the law of the first segment length. -/
theorem identDistrib_blockLen [IsProbabilityMeasure P] (hX : IIDSeq P X) {eps : ℝ}
    (hfin : ∀ᵐ ω ∂P, layerSegLen eps X ω < ⊤) (i : ℕ) :
    IdentDistrib (blockLen eps X i) (layerSegLen eps X) P P :=
  identDistrib_rewards hX.measurable hX.indep hX.ident (isStoppingRule_gapSegLen eps)
    (hfin.mono fun _ h => h.ne) (isStoppingRule_gapSegLen eps).measurable i

/-- Almost surely every block is finite. -/
theorem ae_blockLen_ne_top [IsProbabilityMeasure P] (hX : IIDSeq P X) {eps : ℝ}
    (hfin : ∀ᵐ ω ∂P, layerSegLen eps X ω < ⊤) : ∀ᵐ ω ∂P, ∀ i, blockLen eps X i ω ≠ ⊤ :=
  ae_all_iff.2 fun i => ae_iterate_ne_top hX.measurable hX.indep hX.ident
    (isStoppingRule_gapSegLen eps) (hfin.mono fun _ h => h.ne) i

omit mΩ in
/-- **Renewal representation.**  If all blocks of the path `ω` are finite, the `k`-th segment
on the first `K` keys exists iff the first `k` blocks end before `K`. -/
theorem lt_segCount_iff {eps : ℝ} (heps : 0 ≤ eps) {ω : Ω}
    (hfin : ∀ i, blockLen eps X i ω ≠ ⊤) (K k : ℕ) :
    k < segCount eps X K ω ↔ ∑ i ∈ range k, (blockLen eps X i ω).toNat < K :=
  lt_finSegCount_gapKeys_iff heps hfin K k

/-- **Renewal representation, almost surely.** -/
theorem ae_lt_segCount_iff [IsProbabilityMeasure P] (hX : IIDSeq P X) {eps : ℝ} (heps : 0 ≤ eps)
    (hfin : ∀ᵐ ω ∂P, layerSegLen eps X ω < ⊤) :
    ∀ᵐ ω ∂P, ∀ K k : ℕ,
      k < segCount eps X K ω ↔ ∑ i ∈ range k, (blockLen eps X i ω).toNat < K := by
  filter_upwards [ae_blockLen_ne_top hX hfin] with ω hω K k
  exact lt_segCount_iff heps hω K k

/-- Products of a function of the blocks factorize: `E ∏_{i<k} f(T_i) = (E f(T))^k`. -/
theorem lintegral_prod_blockLen [IsProbabilityMeasure P] (hX : IIDSeq P X) {eps : ℝ}
    (hfin : ∀ᵐ ω ∂P, layerSegLen eps X ω < ⊤) (f : ℕ∞ → ℝ≥0∞) (k : ℕ) :
    ∫⁻ ω, ∏ i ∈ range k, f (blockLen eps X i ω) ∂P =
      (∫⁻ ω, f (layerSegLen eps X ω) ∂P) ^ k := by
  have hf : Measurable f := Measurable.of_discrete
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun (range k)
    (fun i ω => f (blockLen eps X i ω))
    ((iIndepFun_blockLen hX hfin).comp (fun _ => f) fun _ => hf)
    (fun i => hf.comp (measurable_blockLen hX eps i))]
  have h : ∀ i, ∫⁻ ω, f (blockLen eps X i ω) ∂P = ∫⁻ ω, f (layerSegLen eps X ω) ∂P :=
    fun i => ((identDistrib_blockLen hX hfin i).comp hf).lintegral_eq
  simp only [h, prod_const, card_range]

omit mΩ in
/-- Markov's inequality at level `1`. -/
theorem measure_le_lintegral_of_one_le {m : MeasurableSpace Ω} {P : Measure Ω}
    {F : Ω → ℝ≥0∞} (hF : AEMeasurable F P) {E : Set Ω}
    (h : ∀ᵐ ω ∂P, ω ∈ E → 1 ≤ F ω) : P E ≤ ∫⁻ ω, F ω ∂P :=
  calc P E ≤ P {ω | 1 ≤ F ω} := measure_mono_ae (h.mono fun _ hω hE => hω hE)
    _ = 1 * P {ω | 1 ≤ F ω} := (one_mul _).symm
    _ ≤ _ := mul_meas_ge_le_lintegral₀ hF 1

/-! ## Upper tail of the count -/

omit mΩ in
/-- If `k` finite block lengths sum to less than `K` and `2 K ≤ k (n₀ + 1)`, fewer than half
of them exceed `n₀`, so the product of the weights `8` (at most `n₀`) and `1/8` (above `n₀`)
is at least `1`. -/
theorem one_le_prod_weight {n₀ k K : ℕ} (T : ℕ → ℕ∞) (htop : ∀ i, T i ≠ ⊤)
    (hsum : ∑ i ∈ range k, (T i).toNat < K) (hk : 2 * K ≤ k * (n₀ + 1)) :
    1 ≤ ∏ i ∈ range k,
      (if T i ≤ (n₀ : ℕ∞) then ENNReal.ofReal 8 else ENNReal.ofReal (1 / 8)) := by
  classical
  set big := (range k).filter fun i => ¬ T i ≤ (n₀ : ℕ∞)
  set small := (range k).filter fun i => T i ≤ (n₀ : ℕ∞)
  have hcard : #small + #big = k := by
    rw [card_filter_add_card_filter_not, card_range]
  have hbig : #big * (n₀ + 1) ≤ ∑ i ∈ range k, (T i).toNat := by
    calc #big * (n₀ + 1) = #big • (n₀ + 1) := (smul_eq_mul _ _).symm
      _ ≤ ∑ i ∈ big, (T i).toNat := by
          refine card_nsmul_le_sum _ _ _ fun i hi => ?_
          have hi' : ¬ T i ≤ (n₀ : ℕ∞) := (mem_filter.1 hi).2
          rw [← ENat.natCast_toNat (htop i), Nat.cast_le] at hi'
          omega
      _ ≤ ∑ i ∈ range k, (T i).toNat := sum_le_sum_of_subset (filter_subset _ _)
  have h2 : 2 * #big < k := by
    have h3 : 2 * #big * (n₀ + 1) < k * (n₀ + 1) := by
      calc 2 * #big * (n₀ + 1) = 2 * (#big * (n₀ + 1)) := by ring
        _ < 2 * K := by omega
        _ ≤ k * (n₀ + 1) := hk
    exact Nat.lt_of_mul_lt_mul_right h3
  obtain ⟨c, hc⟩ : ∃ c, #small = #big + c := ⟨#small - #big, by omega⟩
  rw [prod_ite, prod_const, prod_const, hc, ← ENNReal.ofReal_pow (by norm_num),
    ← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.one_le_ofReal.2 ?_
  have : (8 : ℝ) ^ (#big + c) * (1 / 8) ^ #big = 8 ^ c := by
    rw [pow_add, mul_right_comm, ← mul_pow]; norm_num
  rw [this]
  exact one_le_pow₀ (by norm_num)

/-- **Upper tail of the count.**  If the first segment is almost surely finite and
`P(T ≤ n₀) ≤ 1/64`, then `P(k < segCount) ≤ (1/4)^k` whenever `2 K ≤ k (n₀ + 1)`. -/
theorem measureReal_lt_segCount_le_of_small [IsProbabilityMeasure P] (hX : IIDSeq P X)
    {eps : ℝ} (heps : 0 ≤ eps) (hfin : ∀ᵐ ω ∂P, layerSegLen eps X ω < ⊤) {n₀ : ℕ}
    (hsmall : P.real {ω | layerSegLen eps X ω ≤ (n₀ : ℕ∞)} ≤ 1 / 64) {K k : ℕ}
    (hk : 2 * K ≤ k * (n₀ + 1)) :
    P.real {ω | k < segCount eps X K ω} ≤ (1 / 4) ^ k := by
  classical
  set f : ℕ∞ → ℝ≥0∞ := fun t =>
    if t ≤ (n₀ : ℕ∞) then ENNReal.ofReal 8 else ENNReal.ofReal (1 / 8) with hf
  have hfm : Measurable f := Measurable.of_discrete
  have hT := measurable_blockLen hX eps
  have hpt : ∀ᵐ ω ∂P, ω ∈ {ω | k < segCount eps X K ω} →
      1 ≤ ∏ i ∈ range k, f (blockLen eps X i ω) := by
    filter_upwards [ae_lt_segCount_iff hX heps hfin, ae_blockLen_ne_top hX hfin]
      with ω hrep htop hω
    exact one_le_prod_weight (fun i => blockLen eps X i ω) htop ((hrep K k).1 hω) hk
  have hmeas : Measurable fun ω => ∏ i ∈ range k, f (blockLen eps X i ω) :=
    Finset.measurable_prod _ fun i _ => hfm.comp (hT i)
  set S := {ω | layerSegLen eps X ω ≤ (n₀ : ℕ∞)} with hS
  have hSm : MeasurableSet S :=
    (measurable_blockLen hX eps 0) (MeasurableSet.of_discrete : MeasurableSet (Set.Iic (n₀ : ℕ∞)))
  have hone : ∫⁻ ω, f (layerSegLen eps X ω) ∂P ≤ ENNReal.ofReal (1 / 4) := by
    calc ∫⁻ ω, f (layerSegLen eps X ω) ∂P
        ≤ ∫⁻ ω, S.indicator (fun _ => ENNReal.ofReal 8) ω + ENNReal.ofReal (1 / 8) ∂P := by
          refine lintegral_mono fun ω => ?_
          by_cases h : layerSegLen eps X ω ≤ (n₀ : ℕ∞)
          · have hω : ω ∈ S := h
            simp only [hf, h, if_true, Set.indicator_of_mem hω]
            exact le_self_add
          · have hω : ω ∉ S := h
            simp only [hf, h, if_false, Set.indicator_of_notMem hω, zero_add, le_refl]
      _ = ENNReal.ofReal 8 * P S + ENNReal.ofReal (1 / 8) := by
          rw [lintegral_add_right _ measurable_const, lintegral_indicator_const hSm,
            lintegral_const, measure_univ, mul_one]
      _ ≤ ENNReal.ofReal 8 * ENNReal.ofReal (1 / 64) + ENNReal.ofReal (1 / 8) := by
          gcongr
          rw [← ofReal_measureReal]
          exact ENNReal.ofReal_le_ofReal hsmall
      _ = ENNReal.ofReal (1 / 4) := by
          rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by norm_num)
            (by norm_num)]
          norm_num
  have hbound : P {ω | k < segCount eps X K ω} ≤ ENNReal.ofReal ((1 / 4) ^ k) :=
    calc P {ω | k < segCount eps X K ω}
        ≤ ∫⁻ ω, ∏ i ∈ range k, f (blockLen eps X i ω) ∂P :=
          measure_le_lintegral_of_one_le hmeas.aemeasurable hpt
      _ = (∫⁻ ω, f (layerSegLen eps X ω) ∂P) ^ k := lintegral_prod_blockLen hX hfin f k
      _ ≤ ENNReal.ofReal (1 / 4) ^ k := by gcongr
      _ = ENNReal.ofReal ((1 / 4) ^ k) := (ENNReal.ofReal_pow (by norm_num) k).symm
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hbound

/-- Under `GapLaw` the first segment is almost surely finite for every `eps ≥ 0`: the
geometric block tail `measureReal_layerSegLen_gt_le` applies with a long enough block. -/
theorem layerSegLen_ae_lt_top [IsProbabilityMeasure P] (hX : GapLaw P X μ σ κ) {eps : ℝ}
    (heps : 0 ≤ eps) : ∀ᵐ ω ∂P, layerSegLen eps X ω < ⊤ := by
  have hμ := hX.mu_pos
  have hσ := hX.sigma_pos
  have hσ2 : 0 < σ ^ 2 := by positivity
  have hμ2 : 0 < μ ^ 2 := by positivity
  set a1 : ℝ := 5184 * μ ^ 2 * eps ^ 2 / σ ^ 2 with ha1
  set a2 : ℝ := κ ^ 2 / σ ^ 6 with ha2
  set a4 : ℝ := 144 * σ ^ 2 / μ ^ 2 with ha4
  have h1 : 0 ≤ a1 := by positivity
  have h2 : 0 ≤ a2 := by positivity
  have h4 : 0 ≤ a4 := by positivity
  set h : ℕ := ⌊a1 + a2 + 2 * eps + a4⌋₊ + 1 with hh
  have hA : a1 + a2 + 2 * eps + a4 < h := by
    rw [hh]; push_cast; exact Nat.lt_floor_add_one _
  have hLc : ((2 * h : ℕ) : ℝ) = 2 * (h : ℝ) := by push_cast; ring
  have hzero := measureReal_layerSegLen_eq_top hX (h := h) (L := 2 * h) (by omega) rfl
    (by
      rw [hLc]
      have e : 5184 * μ ^ 2 * eps ^ 2 = σ ^ 2 * a1 := by rw [ha1]; field_simp
      rw [e]
      exact mul_lt_mul_of_pos_left (by linarith) hσ2)
    (by
      rw [hLc]
      have e : κ ^ 2 = σ ^ 6 * a2 := by rw [ha2]; field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity))
    (by rw [hLc]; linarith)
    (by
      rw [hLc]
      have e : 288 * σ ^ 2 = μ ^ 2 * (2 * a4) := by rw [ha4]; field_simp; ring
      rw [e]
      exact mul_le_mul_of_nonneg_left (by linarith) hμ2.le)
    heps
  rw [measureReal_eq_zero_iff] at hzero
  refine ae_iff.2 ?_
  simpa only [lt_top_iff_ne_top, not_not] using hzero

/-- `P(T ≤ ⌊G/64⌋) ≤ 1/64`, from the lower tail `P(T ≤ n) ≤ n σ² / (μ eps)²`. -/
theorem measureReal_layerSegLen_le_floor [IsProbabilityMeasure P] (hX : GapLaw P X μ σ κ)
    {eps G : ℝ} (heps : 0 < eps) (hGdef : G = μ ^ 2 * eps ^ 2 / σ ^ 2) :
    P.real {ω | layerSegLen eps X ω ≤ (⌊G / 64⌋₊ : ℕ∞)} ≤ 1 / 64 := by
  refine (layerSegLen_lowerTail hX heps ⌊G / 64⌋₊).trans ?_
  have hσ := hX.sigma_pos
  have hμ := hX.mu_pos
  have hG0 : 0 ≤ G := by rw [hGdef]; positivity
  have hfl : (⌊G / 64⌋₊ : ℝ) ≤ G / 64 := Nat.floor_le (by positivity)
  rw [div_le_iff₀ (by positivity)]
  calc (⌊G / 64⌋₊ : ℝ) * σ ^ 2 ≤ G / 64 * σ ^ 2 := by gcongr
    _ = 1 / 64 * (μ * eps) ^ 2 := by rw [hGdef]; field_simp

/-- **Upper tail of the count at scale `G`.**  With `n₀ = ⌊G/64⌋`:
`P(k < segCount) ≤ (1/4)^k` whenever `2 K ≤ k (n₀ + 1)`. -/
theorem measureReal_lt_segCount_le [IsProbabilityMeasure P] (hX : GapLaw P X μ σ κ)
    {eps G : ℝ} (heps : 0 < eps) (hGdef : G = μ ^ 2 * eps ^ 2 / σ ^ 2) {K k : ℕ}
    (hk : 2 * K ≤ k * (⌊G / 64⌋₊ + 1)) :
    P.real {ω | k < segCount eps X K ω} ≤ (1 / 4) ^ k :=
  measureReal_lt_segCount_le_of_small hX.iid heps.le (layerSegLen_ae_lt_top hX heps.le)
    (measureReal_layerSegLen_le_floor hX heps hGdef) hk

/-! ## Lower tail of the count -/

/-- Exponential rate of the lower tail: `θ = (1/2) log (1/r)`. -/
def expRate (r : ℝ) : ℝ := 1 / 2 * Real.log (1 / r)

/-- Bound on the exponential moment: `B' = 1 + (e^θ - 1) / (1 - r e^θ)`. -/
def expBound (r : ℝ) : ℝ := 1 + (Real.exp (expRate r) - 1) / (1 - r * Real.exp (expRate r))

theorem expRate_pos {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) : 0 < expRate r := by
  have : 0 < Real.log (1 / r) := Real.log_pos (one_lt_one_div hr0 hr1)
  unfold expRate
  positivity

theorem mul_exp_expRate_lt_one {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    r * Real.exp (expRate r) < 1 := by
  have hl : 0 < Real.log (1 / r) := Real.log_pos (one_lt_one_div hr0 hr1)
  have h1 : Real.exp (expRate r) < 1 / r := by
    calc Real.exp (expRate r) < Real.exp (Real.log (1 / r)) := by
          apply Real.exp_lt_exp.2; unfold expRate; linarith
      _ = 1 / r := Real.exp_log (by positivity)
  calc r * Real.exp (expRate r) < r * (1 / r) := mul_lt_mul_of_pos_left h1 hr0
    _ = 1 := by field_simp

theorem one_lt_expBound {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) : 1 < expBound r := by
  have h1 : 0 < Real.exp (expRate r) - 1 := by
    have := Real.add_one_lt_exp (expRate_pos hr0 hr1).ne'
    linarith [expRate_pos hr0 hr1]
  have h2 : 0 < 1 - r * Real.exp (expRate r) := by linarith [mul_exp_expRate_lt_one hr0 hr1]
  unfold expBound
  have : 0 < (Real.exp (expRate r) - 1) / (1 - r * Real.exp (expRate r)) := div_pos h1 h2
  linarith

theorem log_expBound_pos {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) : 0 < Real.log (expBound r) :=
  Real.log_pos (one_lt_expBound hr0 hr1)

/-- Pointwise block bound: `e^{θ n / L} ≤ 1 + ∑_j 1{jL < n} e^{θ j} (e^θ - 1)`. -/
theorem exp_toNat_le_tsum (n : ℕ∞) {L : ℕ} (hL : 1 ≤ L) {θ : ℝ} (hθ : 0 ≤ θ) :
    ENNReal.ofReal (Real.exp (θ * n.toNat / L)) ≤ 1 + ∑' j : ℕ,
      if ((j * L : ℕ) : ℕ∞) < n then
        ENNReal.ofReal (Real.exp θ ^ j * (Real.exp θ - 1)) else 0 := by
  induction n using ENat.recTopCoe with
  | top => simp
  | coe m =>
    set M := (m + L - 1) / L with hM
    have hnm : m ≤ M * L := by
      have := Nat.lt_div_mul_add (a := m + L - 1) (b := L) (by omega)
      rw [← hM] at this
      omega
    have hj : ∀ j < M, j * L < m := by
      intro j hj
      have h1 : (j + 1) * L ≤ m + L - 1 := (Nat.le_div_iff_mul_le (by omega)).1 hj
      rw [add_mul, one_mul] at h1
      omega
    set q := Real.exp θ with hq
    have hq1 : 1 ≤ q := Real.one_le_exp hθ
    have key : Real.exp (θ * m / L) ≤ q ^ M := by
      rw [hq, ← Real.exp_nat_mul]
      apply Real.exp_le_exp.2
      have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
      rw [div_le_iff₀ hL0]
      have hmL : (m : ℝ) ≤ M * L := by exact_mod_cast hnm
      calc θ * m ≤ θ * (M * L) := mul_le_mul_of_nonneg_left hmL hθ
        _ = M * θ * L := by ring
    have hgeom : q ^ M = 1 + ∑ j ∈ range M, q ^ j * (q - 1) := by
      rw [← sum_mul, geom_sum_mul]; ring
    have hnn : ∀ j ∈ range M, 0 ≤ q ^ j * (q - 1) := fun j _ =>
      mul_nonneg (pow_nonneg (by linarith) _) (by linarith)
    calc ENNReal.ofReal (Real.exp (θ * ((m : ℕ∞).toNat : ℝ) / L))
        = ENNReal.ofReal (Real.exp (θ * m / L)) := by rw [ENat.toNat_natCast]
      _ ≤ ENNReal.ofReal (q ^ M) := ENNReal.ofReal_le_ofReal key
      _ = 1 + ∑ j ∈ range M, ENNReal.ofReal (q ^ j * (q - 1)) := by
          rw [hgeom, ENNReal.ofReal_add zero_le_one (sum_nonneg hnn), ENNReal.ofReal_one,
            ENNReal.ofReal_sum_of_nonneg hnn]
      _ ≤ _ := by
          gcongr
          refine le_trans (le_of_eq (Finset.sum_congr rfl fun j hjm => ?_))
            (ENNReal.sum_le_tsum (range M))
          rw [if_pos (by exact_mod_cast hj j (Finset.mem_range.1 hjm))]

omit mΩ in
/-- **Exponential moment.**  Under the geometric block tail `P(jL < T) ≤ r^j`,
`E exp(θ T / L) ≤ B'` with `θ = expRate r`, `B' = expBound r`. -/
theorem lintegral_exp_le_of_tail {m : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {T : Ω → ℕ∞} (hT : Measurable T) {L : ℕ} (hL : 1 ≤ L) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (htail : ∀ j : ℕ, P.real {ω | ((j * L : ℕ) : ℕ∞) < T ω} ≤ r ^ j) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (expRate r * (T ω).toNat / L)) ∂P ≤
      ENNReal.ofReal (expBound r) := by
  set θ := expRate r with hθdef
  have hθ : 0 ≤ θ := (expRate_pos hr0 hr1).le
  set q := Real.exp θ with hq
  have hq1 : 1 ≤ q := Real.one_le_exp hθ
  have hrq0 : 0 ≤ r * q := by positivity
  have hrq1 : r * q < 1 := mul_exp_expRate_lt_one hr0 hr1
  set c : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal (q ^ j * (q - 1)) with hc
  have hs : ∀ j : ℕ, MeasurableSet {ω | ((j * L : ℕ) : ℕ∞) < T ω} := fun j =>
    tail_measurableSet_lt hT _
  have hg := (hasSum_geometric_of_lt_one hrq0 hrq1).mul_left (q - 1)
  have hsum : ∑' j : ℕ, c j * ENNReal.ofReal (r ^ j) =
      ENNReal.ofReal ((q - 1) * (1 - r * q)⁻¹) := by
    rw [← hg.tsum_eq, ENNReal.ofReal_tsum_of_nonneg
      (fun j => mul_nonneg (by linarith) (pow_nonneg hrq0 _)) hg.summable]
    refine tsum_congr fun j => ?_
    rw [hc, ← ENNReal.ofReal_mul (mul_nonneg (pow_nonneg (by linarith) _) (by linarith))]
    congr 1
    rw [mul_pow]; ring
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * (T ω).toNat / L)) ∂P
      ≤ ∫⁻ ω, 1 + ∑' j : ℕ, Set.indicator {ω | ((j * L : ℕ) : ℕ∞) < T ω}
          (fun _ => c j) ω ∂P := by
        refine lintegral_mono fun ω => ?_
        simpa only [Set.indicator_apply, Set.mem_ofPred_eq] using exp_toNat_le_tsum (T ω) hL hθ
    _ = 1 + ∑' j : ℕ, c j * P {ω | ((j * L : ℕ) : ℕ∞) < T ω} := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_tsum fun j => (measurable_const.indicator (hs j)).aemeasurable]
        simp_rw [lintegral_indicator_const (hs _)]
    _ ≤ 1 + ∑' j : ℕ, c j * ENNReal.ofReal (r ^ j) := by
        gcongr with j
        rw [← ofReal_measureReal]
        exact ENNReal.ofReal_le_ofReal (htail j)
    _ = ENNReal.ofReal (expBound r) := by
        rw [hsum, expBound, ← hθdef, ← hq, ENNReal.ofReal_add zero_le_one, ENNReal.ofReal_one,
          div_eq_mul_inv]
        exact mul_nonneg (by linarith) (inv_nonneg.2 (by linarith))

/-- **Lower tail of the count.**  Under the geometric block tail `P(jL < T) ≤ r^j`
(`L ≥ 1`, `0 < r < 1`), with `θ = expRate r` and `B' = expBound r`:
`P(segCount ≤ k) ≤ exp(-θ K / L) B'^k`. -/
theorem measureReal_segCount_le_le [IsProbabilityMeasure P] (hX : IIDSeq P X) {eps : ℝ}
    (heps : 0 ≤ eps) {L : ℕ} (hL : 1 ≤ L) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (htail : ∀ j : ℕ, P.real {ω | ((j * L : ℕ) : ℕ∞) < layerSegLen eps X ω} ≤ r ^ j)
    (K k : ℕ) :
    P.real {ω | segCount eps X K ω ≤ k} ≤
      Real.exp (-expRate r * K / L) * expBound r ^ k := by
  set θ := expRate r with hθdef
  have hθ : 0 ≤ θ := (expRate_pos hr0 hr1).le
  have hT := measurable_blockLen hX eps
  have hfin : ∀ᵐ ω ∂P, layerSegLen eps X ω < ⊤ :=
    ae_lt_top_of_tail (hT 0) hL hr0.le hr1 htail
  set f : ℕ∞ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (θ * t.toNat / L)) with hf
  have hfm : Measurable f := Measurable.of_discrete
  set F : Ω → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (Real.exp (-θ * K / L)) * ∏ i ∈ range k, f (blockLen eps X i ω) with hF
  have hPm : Measurable fun ω => ∏ i ∈ range k, f (blockLen eps X i ω) :=
    Finset.measurable_prod _ fun i _ => hfm.comp (hT i)
  have hFm : Measurable F := measurable_const.mul hPm
  have hpt : ∀ᵐ ω ∂P, ω ∈ {ω | segCount eps X K ω ≤ k} → 1 ≤ F ω := by
    filter_upwards [ae_lt_segCount_iff hX heps hfin] with ω hrep hω
    have hω' : ¬ k < segCount eps X K ω := not_lt.2 hω
    rw [hrep K k, not_lt] at hω'
    have hK : (K : ℝ) ≤ ∑ i ∈ range k, ((blockLen eps X i ω).toNat : ℝ) := by
      exact_mod_cast hω'
    simp only [hF, hf]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le),
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_sum, ← Real.exp_add]
    refine ENNReal.one_le_ofReal.2 (Real.one_le_exp ?_)
    have heq : -θ * K / L + ∑ i ∈ range k, θ * ((blockLen eps X i ω).toNat : ℝ) / L =
        θ * (∑ i ∈ range k, ((blockLen eps X i ω).toNat : ℝ) - K) / L := by
      rw [← sum_div, ← mul_sum]; ring
    rw [heq]
    exact div_nonneg (mul_nonneg hθ (sub_nonneg.2 hK)) (Nat.cast_nonneg _)
  have hbound : P {ω | segCount eps X K ω ≤ k} ≤
      ENNReal.ofReal (Real.exp (-θ * K / L) * expBound r ^ k) :=
    calc P {ω | segCount eps X K ω ≤ k} ≤ ∫⁻ ω, F ω ∂P :=
          measure_le_lintegral_of_one_le hFm.aemeasurable hpt
      _ = ENNReal.ofReal (Real.exp (-θ * K / L)) *
            (∫⁻ ω, f (layerSegLen eps X ω) ∂P) ^ k := by
          show ∫⁻ ω, ENNReal.ofReal (Real.exp (-θ * K / L)) *
            ∏ i ∈ range k, f (blockLen eps X i ω) ∂P = _
          rw [lintegral_const_mul _ hPm, lintegral_prod_blockLen hX hfin f k]
      _ ≤ ENNReal.ofReal (Real.exp (-θ * K / L)) * ENNReal.ofReal (expBound r) ^ k := by
          gcongr
          exact lintegral_exp_le_of_tail (hT 0) hL hr0 hr1 htail
      _ = _ := by
          rw [← ENNReal.ofReal_pow (by linarith [one_lt_expBound hr0 hr1]),
            ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact ENNReal.toReal_le_of_le_ofReal
    (mul_nonneg (Real.exp_pos _).le (pow_nonneg (by linarith [one_lt_expBound hr0 hr1]) _))
    hbound

/-! ## Clean corollaries under the large-`eps` conditions -/

/-- Absolute constant of the lower tail: `aLow = θ / (2 · 5185 · log B')` with
`θ = expRate (71/72)` and `B' = expBound (71/72)`. -/
def aLow : ℝ := expRate (71 / 72) / (2 * 5185 * Real.log (expBound (71 / 72)))

theorem log_expBound_low_pos : 0 < Real.log (expBound (71 / 72)) :=
  log_expBound_pos (by norm_num) (by norm_num)

theorem aLow_pos : 0 < aLow :=
  div_pos (expRate_pos (by norm_num) (by norm_num)) (by
    have := log_expBound_low_pos
    positivity)

/-- **Upper tail, clean form.**  For every `eps > 0` (no large-`eps` condition is needed),
`P(segCount > 128 K / G + t + 1) ≤ (1/4)^t` for every natural `t`. -/
theorem measureReal_segCount_gt_le [IsProbabilityMeasure P] (hX : GapLaw P X μ σ κ)
    {eps G : ℝ} (heps : 0 < eps) (hGdef : G = μ ^ 2 * eps ^ 2 / σ ^ 2) (K t : ℕ) :
    P.real {ω | 128 * K / G + t + 1 < (segCount eps X K ω : ℝ)} ≤ (1 / 4) ^ t := by
  have hGpos : 0 < G := by
    have := hX.mu_pos
    have := hX.sigma_pos
    rw [hGdef]; positivity
  set a : ℝ := 128 * K / G with ha
  have ha0 : 0 ≤ a := by positivity
  set k := ⌈a⌉₊ + t with hkdef
  have hk : 2 * K ≤ k * (⌊G / 64⌋₊ + 1) := by
    have h1 : G / 64 < (⌊G / 64⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have h2 : a ≤ (k : ℝ) := by
      rw [hkdef]; push_cast
      linarith [Nat.le_ceil a, (Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
    have h3 : (2 * K : ℝ) ≤ (k : ℝ) * ((⌊G / 64⌋₊ : ℝ) + 1) :=
      calc (2 * K : ℝ) = a * (G / 64) := by rw [ha]; field_simp; ring
        _ ≤ k * (G / 64) := by gcongr
        _ ≤ k * ((⌊G / 64⌋₊ : ℝ) + 1) := by gcongr
    exact_mod_cast h3
  have hsub : {ω | a + t + 1 < (segCount eps X K ω : ℝ)} ⊆ {ω | k < segCount eps X K ω} := by
    intro ω hω
    have hω' : a + t + 1 < (segCount eps X K ω : ℝ) := hω
    have hc := Nat.ceil_lt_add_one ha0
    have : (k : ℝ) < segCount eps X K ω := by
      rw [hkdef]; push_cast; linarith
    exact_mod_cast this
  calc P.real {ω | a + t + 1 < (segCount eps X K ω : ℝ)}
      ≤ P.real {ω | k < segCount eps X K ω} := measureReal_mono hsub
    _ ≤ (1 / 4) ^ k := measureReal_lt_segCount_le hX heps hGdef hk
    _ ≤ (1 / 4) ^ t := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

/-- **Lower tail, clean form.**  Under the large-`eps` conditions,
`P(segCount < aLow K / G - t) ≤ exp(-(log B') t)` for every natural `t`,
with `B' = expBound (71/72)`. -/
theorem measureReal_segCount_lt_le_of_large [IsProbabilityMeasure P] (hX : GapLaw P X μ σ κ)
    {eps G : ℝ} (heps : 0 < eps) (hGdef : G = μ ^ 2 * eps ^ 2 / σ ^ 2) (hG : 10000 ≤ G)
    (hβ : κ ^ 2 ≤ σ ^ 6 * (G / 2304)) (hv1 : σ ^ 2 ≤ 1296 * eps * μ ^ 2)
    (hv2 : σ ^ 4 ≤ 18 * eps ^ 2 * μ ^ 4) (K t : ℕ) :
    P.real {ω | (segCount eps X K ω : ℝ) < aLow * K / G - t} ≤
      Real.exp (-(Real.log (expBound (71 / 72))) * t) := by
  obtain ⟨L, hL1, hLG, htail⟩ := layerSegLen_tail_of_large hX heps hGdef hG hβ hv1 hv2
  have hGpos : 0 < G := by linarith
  set θ := expRate (71 / 72) with hθdef
  set B := expBound (71 / 72) with hBdef
  have hθ : 0 < θ := expRate_pos (by norm_num) (by norm_num)
  have hlogB : 0 < Real.log B := log_expBound_low_pos
  have hB0 : 0 < B := by linarith [one_lt_expBound (r := 71 / 72) (by norm_num) (by norm_num)]
  set x : ℝ := aLow * K / G - t with hx
  rcases lt_or_ge x 0 with hneg | hpos
  · have hempty : {ω | (segCount eps X K ω : ℝ) < x} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact le_trans hneg.le (Nat.cast_nonneg _)
    rw [hempty, measureReal_empty]
    exact (Real.exp_pos _).le
  set k := ⌊x⌋₊ with hkdef
  have hsub : {ω | (segCount eps X K ω : ℝ) < x} ⊆ {ω | segCount eps X K ω ≤ k} :=
    fun ω hω => Nat.le_floor (le_of_lt hω)
  have hk : (k : ℝ) ≤ x := Nat.floor_le hpos
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL1
  have h1 : (k : ℝ) * Real.log B ≤ x * Real.log B := mul_le_mul_of_nonneg_right hk hlogB.le
  have h2 : x * Real.log B = θ * K / (2 * 5185 * G) - t * Real.log B := by
    rw [hx, aLow, ← hθdef, ← hBdef]
    field_simp
  have h3 : θ * K / (5185 * G) ≤ θ * K / L :=
    div_le_div_of_nonneg_left (by positivity) hL0 hLG
  have h4 : θ * K / (2 * 5185 * G) = (θ * K / (5185 * G)) / 2 := by
    field_simp
  have h5 : 0 ≤ θ * K / (5185 * G) := by positivity
  have hkey : -θ * K / L + k * Real.log B ≤ -Real.log B * t := by
    have e1 : -θ * K / L = -(θ * K / L) := by ring
    have e2 : -Real.log B * t = -(t * Real.log B) := by ring
    rw [e1, e2]
    linarith
  calc P.real {ω | (segCount eps X K ω : ℝ) < x}
      ≤ P.real {ω | segCount eps X K ω ≤ k} := measureReal_mono hsub
    _ ≤ Real.exp (-θ * K / L) * B ^ k :=
        measureReal_segCount_le_le hX.iid heps.le hL1 (by norm_num) (by norm_num) htail K k
    _ = Real.exp (-θ * K / L + k * Real.log B) := by
        rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hB0]
    _ ≤ Real.exp (-Real.log B * t) := Real.exp_le_exp.2 hkey

end

end PGM
