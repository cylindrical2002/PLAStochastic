import PLAStochastic.Index.Model.IIDPairs
import PLAStochastic.Index.Algorithm.EndpointHierarchyBounds
import PLAStochastic.ForMathlib.Probability.Moments.PaleyZygmund
import PLAStochastic.ForMathlib.Probability.StoppedSum.WaldENat

/-!
# Expected endpoint height from layer-level moment bounds

Let `Z` be the input pair sequence and write `H = spanHeight eps (seq Z ·) n`.  On
the probability-one event where every infinite segment is finite:

* **Upper bound** (`integral_spanHeight_le`).  If the layer-`ℓ⁺` pairs are iid, the
  mean `m` of their count components is at least `2n`, and `E N² ≤ K m²`, then
  `E H ≤ ℓ⁺ + 4K`.  (`H ≤ ℓ⁺ + K_{ℓ⁺} - 1`; `K_{ℓ⁺}` has a geometric tail because
  each layer hyper-segment spans `n` with probability at least `1/(4K)` by
  Paley–Zygmund.)  This replaces Lorden's inequality of the TeX proof.
* **Lower bound** (`integral_spanHeight_ge`).  For every `L`,
  `E H ≥ 1 + L - ∑_{ℓ=1}^{L} E[N^{(ℓ)}_0] / n` (Markov at each layer).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Filter
open scoped ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {Z : ℕ → Ω → ℝ × ℕ} {eps : ℝ}

/-! ## Measurability -/

theorem measurable_leadSpan_seq (hZ : ∀ t, Measurable (Z t)) (ℓ : ℕ) :
    Measurable fun ω => leadSpan eps (seq Z ω) ℓ := by
  have h1 : Measurable fun ω => pairLayer eps ℓ (seq Z ω) :=
    (measurable_pairLayer eps ℓ).comp (measurable_seq hZ)
  exact measurable_snd.comp ((measurable_pi_apply 0).comp h1)

theorem measurable_layerCount_seq (hZ : ∀ t, Measurable (Z t)) (n ℓ : ℕ) :
    Measurable fun ω => layerCount eps (seq Z ω) n ℓ := by
  have h1 : Measurable fun ω => pairLayer eps ℓ (seq Z ω) :=
    (measurable_pairLayer eps ℓ).comp (measurable_seq hZ)
  have hr : ∀ j, Measurable fun ω => pairRank (pairLayer eps ℓ (seq Z ω)) j := by
    intro j
    simp only [pairRank]
    exact Finset.measurable_sum _ fun s _ => measurable_snd.comp ((measurable_pi_apply s).comp h1)
  apply measurable_to_countable'
  intro k
  have hset : (fun ω => layerCount eps (seq Z ω) n ℓ) ⁻¹' {k} =
      ({ω | sInf {j | n ≤ pairRank (pairLayer eps ℓ (seq Z ω)) j} = k}) := rfl
  rw [hset]
  have hchar : ∀ S : Set ℕ, sInf S = k ↔ (S = ∅ ∧ k = 0) ∨ (k ∈ S ∧ ∀ j < k, j ∉ S) := by
    intro S
    constructor
    · intro h
      by_cases hS : S.Nonempty
      · right
        exact ⟨h ▸ Nat.sInf_mem hS, fun j hj => Nat.notMem_of_lt_sInf (h ▸ hj)⟩
      · left
        have hS' : S = ∅ := Set.not_nonempty_iff_eq_empty.1 hS
        exact ⟨hS', by rw [← h, hS', Nat.sInf_empty]⟩
    · rintro (⟨hS, hk⟩ | ⟨hk, hmin⟩)
      · rw [hS, hk, Nat.sInf_empty]
      · apply le_antisymm (Nat.sInf_le hk)
        by_contra hc
        exact hmin _ (not_le.mp hc) (Nat.sInf_mem ⟨k, hk⟩)
  have : {ω | sInf {j | n ≤ pairRank (pairLayer eps ℓ (seq Z ω)) j} = k} =
      ({ω | ∀ j, ¬ n ≤ pairRank (pairLayer eps ℓ (seq Z ω)) j} ∩ {_ω | k = 0}) ∪
        ({ω | n ≤ pairRank (pairLayer eps ℓ (seq Z ω)) k} ∩
          ⋂ j ∈ Finset.range k, {ω | ¬ n ≤ pairRank (pairLayer eps ℓ (seq Z ω)) j}) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_iInter,
      Finset.mem_range, hchar, Set.eq_empty_iff_forall_notMem]
  rw [this]
  refine MeasurableSet.union (MeasurableSet.inter ?_ ?_) (MeasurableSet.inter ?_ ?_)
  · rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => (measurableSet_le measurable_const (hr j)).compl
  · exact MeasurableSet.const _
  · exact measurableSet_le measurable_const (hr k)
  · exact MeasurableSet.biInter (Finset.range k).countable_toSet fun j _ =>
      (measurableSet_le measurable_const (hr j)).compl

theorem measurable_spanHeight_seq (hZ : ∀ t, Measurable (Z t)) (n : ℕ) :
    Measurable fun ω => spanHeight eps (seq Z ω) n := by
  have hl := measurable_leadSpan_seq (eps := eps) hZ
  apply measurable_to_countable'
  intro k
  have hchar : ∀ S : Set ℕ, sInf S = k ↔ (S = ∅ ∧ k = 0) ∨ (k ∈ S ∧ ∀ j < k, j ∉ S) := by
    intro S
    constructor
    · intro h
      by_cases hS : S.Nonempty
      · right
        exact ⟨h ▸ Nat.sInf_mem hS, fun j hj => Nat.notMem_of_lt_sInf (h ▸ hj)⟩
      · left
        have hS' : S = ∅ := Set.not_nonempty_iff_eq_empty.1 hS
        exact ⟨hS', by rw [← h, hS', Nat.sInf_empty]⟩
    · rintro (⟨hS, hk⟩ | ⟨hk, hmin⟩)
      · rw [hS, hk, Nat.sInf_empty]
      · apply le_antisymm (Nat.sInf_le hk)
        by_contra hc
        exact hmin _ (not_le.mp hc) (Nat.sInf_mem ⟨k, hk⟩)
  have : (fun ω => spanHeight eps (seq Z ω) n) ⁻¹' {k} =
      ({ω | ∀ ℓ, ¬ (1 ≤ ℓ ∧ n ≤ leadSpan eps (seq Z ω) ℓ)} ∩ {_ω | k = 0}) ∪
        ({ω | 1 ≤ k ∧ n ≤ leadSpan eps (seq Z ω) k} ∩
          ⋂ j ∈ Finset.range k, {ω | ¬ (1 ≤ j ∧ n ≤ leadSpan eps (seq Z ω) j)}) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, spanHeight, hchar,
      Set.eq_empty_iff_forall_notMem, Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff,
      Set.mem_iInter, Finset.mem_range]
  rw [this]
  have hm : ∀ ℓ, MeasurableSet {ω | 1 ≤ ℓ ∧ n ≤ leadSpan eps (seq Z ω) ℓ} := fun ℓ =>
    (MeasurableSet.const _).inter (measurableSet_le measurable_const (hl ℓ))
  refine MeasurableSet.union (MeasurableSet.inter ?_ (MeasurableSet.const _))
    (MeasurableSet.inter (hm k) ?_)
  · rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun ℓ => (hm ℓ).compl
  · exact MeasurableSet.biInter (Finset.range k).countable_toSet fun j _ => (hm j).compl

/-! ## Tail sums -/

theorem lintegral_nat_eq_tsum {f : Ω → ℕ} (hf : Measurable f) :
    ∫⁻ ω, (f ω : ℝ≥0∞) ∂P = ∑' k : ℕ, P {ω | k < f ω} := by
  have h := lintegral_enat_eq_tsum (P := P) (T := fun ω => (f ω : ℕ∞))
    (by exact (Measurable.of_discrete (f := fun k : ℕ => (k : ℕ∞))).comp hf)
  simp only [ENat.toENNReal_coe, Nat.cast_lt] at h
  exact h

omit mΩ in
theorem hposAll (heps : 0 ≤ eps) (hpos0 : ∀ t ω, 1 ≤ (Z t ω).2) {ω : Ω}
    (hω : AllLayersFinite eps (seq Z ω)) : ∀ ℓ t, 1 ≤ (pairLayer eps ℓ (seq Z ω) t).2 :=
  pairLayer_pos heps hω (fun t => hpos0 t ω)

/-! ## Upper bound -/

/-- Paley–Zygmund for the leading hyper-segment: it spans `n` with probability at
    least `1/(4K)` when its mean is at least `2n` and `E N² ≤ K m²`. -/
theorem prob_count_lt_le [IsProbabilityMeasure P] {N : Ω → ℕ} (hN : Measurable N) {n : ℕ}
    (hn : 1 ≤ n)
    {K : ℝ} (hK : 1 ≤ K) (hN2 : Integrable (fun ω => (N ω : ℝ) ^ 2) P)
    (hm : 2 * (n : ℝ) ≤ ∫ ω, (N ω : ℝ) ∂P)
    (hKm : ∫ ω, (N ω : ℝ) ^ 2 ∂P ≤ K * (∫ ω, (N ω : ℝ) ∂P) ^ 2) :
    P.real {ω | N ω < n} ≤ 1 - 1 / (4 * K) := by
  set W : Ω → ℝ := fun ω => (N ω : ℝ)
  have hWm : Measurable W := (Measurable.of_discrete (f := fun k : ℕ => (k : ℝ))).comp hN
  have hW2 : MemLp W 2 P := (memLp_two_iff_integrable_sq hWm.aestronglyMeasurable).2 hN2
  have hpz := paley_zygmund (P := P) (W := W) hWm (fun ω => Nat.cast_nonneg (N ω)) hW2
    (θ := 1 / 2) (by norm_num) (by norm_num)
  set m := ∫ ω, W ω ∂P
  have hm0 : 0 < m := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  set p := P.real {ω | 1 / 2 * m < W ω}
  have hp : 1 / (4 * K) ≤ p := by
    have h1 : (1 - 1 / 2) ^ 2 * m ^ 2 ≤ K * m ^ 2 * p :=
      hpz.trans (mul_le_mul_of_nonneg_right hKm measureReal_nonneg)
    have hm2 : 0 < m ^ 2 := by positivity
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hsub : {ω | 1 / 2 * m < W ω} ⊆ {ω | N ω < n}ᶜ := by
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt]
    have : (n : ℝ) < N ω := by
      have := hω; simp only [Set.mem_ofPred_eq, W] at this; linarith
    exact_mod_cast this.le
  have hcompl : P.real {ω | N ω < n}ᶜ = 1 - P.real {ω | N ω < n} :=
    probReal_compl_eq_one_sub (measurableSet_lt hN measurable_const)
  have := measureReal_mono hsub (μ := P)
  linarith

theorem lintegral_layerCount_le [IsProbabilityMeasure P] (hZ : ∀ t, Measurable (Z t))
    (heps : 0 ≤ eps) (hfinAll : ∀ᵐ ω ∂P, AllLayersFinite eps (seq Z ω))
    (hpos0 : ∀ t ω, 1 ≤ (Z t ω).2) {n ℓ : ℕ}
    (hiid : IIDPairs P (fun j ω => pairLayer eps ℓ (seq Z ω) j)) {q : ℝ} (hq1 : q < 1)
    (hq : P.real {ω | (pairLayer eps ℓ (seq Z ω) 0).2 < n} ≤ q) :
    ∫⁻ ω, (layerCount eps (seq Z ω) n ℓ : ℝ≥0∞) ∂P ≤ ENNReal.ofReal (1 / (1 - q)) := by
  have hq0 : 0 ≤ q := le_trans measureReal_nonneg hq
  rw [lintegral_nat_eq_tsum (measurable_layerCount_seq hZ n ℓ)]
  -- each tail is at most `q^k`
  have htail : ∀ k, P {ω | k < layerCount eps (seq Z ω) n ℓ} ≤ ENNReal.ofReal (q ^ k) := by
    intro k
    set A : Set (ℝ × ℕ) := {x | x.2 < n}
    have hA : MeasurableSet A := measurableSet_lt (measurable_snd) measurable_const
    have hsub : {ω | k < layerCount eps (seq Z ω) n ℓ} ≤ᵐ[P]
        (⋂ s ∈ Finset.range k, (fun ω => pairLayer eps ℓ (seq Z ω) s) ⁻¹' A : Set Ω) := by
      filter_upwards [hfinAll] with ω hω hk
      change k < layerCount eps (seq Z ω) n ℓ at hk
      show ω ∈ (⋂ s ∈ Finset.range k, (fun ω => pairLayer eps ℓ (seq Z ω) s) ⁻¹' A)
      have hp := hposAll heps hpos0 hω
      have hrank : pairRank (pairLayer eps ℓ (seq Z ω)) k < n := by
        by_contra hc
        exact (not_le.mpr hk) ((layerCount_spec hp n ℓ k).1 (not_lt.mp hc))
      simp only [Set.mem_iInter, Set.mem_preimage, Finset.mem_range]
      intro s hs
      show (pairLayer eps ℓ (seq Z ω) s).2 < n
      refine lt_of_le_of_lt ?_ hrank
      simp only [pairRank]
      exact Finset.single_le_sum (f := fun t => (pairLayer eps ℓ (seq Z ω) t).2)
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hs)
    calc P {ω | k < layerCount eps (seq Z ω) n ℓ}
        ≤ P (⋂ s ∈ Finset.range k, (fun ω => pairLayer eps ℓ (seq Z ω) s) ⁻¹' A) :=
          measure_mono_ae hsub
      _ = ∏ s ∈ Finset.range k, P ((fun ω => pairLayer eps ℓ (seq Z ω) s) ⁻¹' A) :=
          hiid.indep.measure_inter_preimage_eq_mul _ (fun _ _ => hA)
      _ = ∏ _s ∈ Finset.range k, P ((fun ω => pairLayer eps ℓ (seq Z ω) 0) ⁻¹' A) := by
          refine Finset.prod_congr rfl fun s _ => ?_
          exact (hiid.ident s).measure_mem_eq hA
      _ = P ((fun ω => pairLayer eps ℓ (seq Z ω) 0) ⁻¹' A) ^ k := by simp
      _ ≤ ENNReal.ofReal q ^ k := by
          gcongr
          rw [← ofReal_measureReal (measure_ne_top _ _)]
          exact ENNReal.ofReal_le_ofReal hq
      _ = ENNReal.ofReal (q ^ k) := (ENNReal.ofReal_pow hq0 k).symm
  calc ∑' k, P {ω | k < layerCount eps (seq Z ω) n ℓ}
      ≤ ∑' k : ℕ, ENNReal.ofReal (q ^ k) := ENNReal.tsum_le_tsum htail
    _ = ENNReal.ofReal (∑' k : ℕ, q ^ k) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun k => pow_nonneg hq0 k)
          (summable_geometric_of_lt_one hq0 hq1)).symm
    _ = ENNReal.ofReal (1 / (1 - q)) := by
        rw [tsum_geometric_of_lt_one hq0 hq1, one_div]

/-- **Upper bound on the expected height.** -/
theorem integral_spanHeight_le [IsProbabilityMeasure P] (hZ : ∀ t, Measurable (Z t))
    (heps : 1 ≤ eps) (hfinAll : ∀ᵐ ω ∂P, AllLayersFinite eps (seq Z ω))
    (hpos0 : ∀ t ω, 1 ≤ (Z t ω).2) {n : ℕ} (hn : 1 ≤ n) {ℓp : ℕ} (hℓp : 1 ≤ ℓp)
    (hiid : IIDPairs P (fun j ω => pairLayer eps ℓp (seq Z ω) j)) {K : ℝ} (hK : 1 ≤ K)
    (hN2 : Integrable (fun ω => ((pairLayer eps ℓp (seq Z ω) 0).2 : ℝ) ^ 2) P)
    (hm : 2 * (n : ℝ) ≤ ∫ ω, ((pairLayer eps ℓp (seq Z ω) 0).2 : ℝ) ∂P)
    (hKm : ∫ ω, ((pairLayer eps ℓp (seq Z ω) 0).2 : ℝ) ^ 2 ∂P ≤
      K * (∫ ω, ((pairLayer eps ℓp (seq Z ω) 0).2 : ℝ) ∂P) ^ 2) :
    ∫ ω, (spanHeight eps (seq Z ω) n : ℝ) ∂P ≤ ℓp + 4 * K := by
  have heps0 : 0 ≤ eps := by linarith
  have hN : Measurable fun ω => (pairLayer eps ℓp (seq Z ω) 0).2 :=
    measurable_snd.comp ((measurable_pi_apply 0).comp
      ((measurable_pairLayer eps ℓp).comp (measurable_seq hZ)))
  have hq := prob_count_lt_le hN hn hK hN2 hm hKm
  have hq1 : 1 - 1 / (4 * K) < 1 := by
    have : 0 < 1 / (4 * K) := by positivity
    linarith
  have hLC := lintegral_layerCount_le hZ heps0 hfinAll hpos0 hiid hq1 hq
  have hgeo : 1 / (1 - (1 - 1 / (4 * K))) = 4 * K := by rw [sub_sub_cancel, one_div_one_div]
  rw [hgeo] at hLC
  -- pathwise: `H ≤ ℓp + K_ℓp - 1`
  have hpath : ∀ᵐ ω ∂P, (spanHeight eps (seq Z ω) n : ℝ) ≤
      ℓp + (layerCount eps (seq Z ω) n ℓp : ℝ) := by
    filter_upwards [hfinAll] with ω hω
    have hp := hposAll heps0 hpos0 hω
    have h1 := layerCount_pos hp hn ℓp
    have := spanHeight_le_add_layerCount heps hω hp hn (layerCount eps (seq Z ω) n ℓp - 1) ℓp hℓp
      (by omega)
    have : spanHeight eps (seq Z ω) n ≤ ℓp + layerCount eps (seq Z ω) n ℓp := by omega
    exact_mod_cast this
  have hLCm := measurable_layerCount_seq (eps := eps) hZ n ℓp
  have hLCint : Integrable (fun ω => (layerCount eps (seq Z ω) n ℓp : ℝ)) P := by
    refine ⟨((Measurable.of_discrete (f := fun k : ℕ => (k : ℝ))).comp hLCm).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => Nat.cast_nonneg _)]
    simp only [ENNReal.ofReal_natCast]
    exact lt_of_le_of_lt hLC ENNReal.ofReal_lt_top
  have hLCreal : ∫ ω, (layerCount eps (seq Z ω) n ℓp : ℝ) ∂P ≤ 4 * K := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => Nat.cast_nonneg _)
      hLCint.aestronglyMeasurable]
    simp only [ENNReal.ofReal_natCast]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hLC
  have hHm : Measurable fun ω => (spanHeight eps (seq Z ω) n : ℝ) :=
    (Measurable.of_discrete (f := fun k : ℕ => (k : ℝ))).comp (measurable_spanHeight_seq hZ n)
  have hHint : Integrable (fun ω => (spanHeight eps (seq Z ω) n : ℝ)) P := by
    refine Integrable.mono' ((integrable_const (ℓp : ℝ)).add hLCint)
      hHm.aestronglyMeasurable ?_
    filter_upwards [hpath] with ω hω
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact hω
  calc ∫ ω, (spanHeight eps (seq Z ω) n : ℝ) ∂P
      ≤ ∫ ω, ((ℓp : ℝ) + (layerCount eps (seq Z ω) n ℓp : ℝ)) ∂P :=
        integral_mono_ae hHint ((integrable_const _).add hLCint) hpath
    _ = ℓp + ∫ ω, (layerCount eps (seq Z ω) n ℓp : ℝ) ∂P := by
        rw [integral_add (integrable_const _) hLCint]; simp
    _ ≤ ℓp + 4 * K := by linarith

/-! ## Lower bound -/

theorem integrable_spanHeight [IsProbabilityMeasure P] (hZ : ∀ t, Measurable (Z t))
    (heps : 1 ≤ eps) (hfinAll : ∀ᵐ ω ∂P, AllLayersFinite eps (seq Z ω))
    (hpos0 : ∀ t ω, 1 ≤ (Z t ω).2) {n : ℕ} (hn : 1 ≤ n) :
    Integrable (fun ω => (spanHeight eps (seq Z ω) n : ℝ)) P := by
  have hHm : Measurable fun ω => (spanHeight eps (seq Z ω) n : ℝ) :=
    (Measurable.of_discrete (f := fun k : ℕ => (k : ℝ))).comp (measurable_spanHeight_seq hZ n)
  refine Integrable.mono' (integrable_const (n : ℝ)) hHm.aestronglyMeasurable ?_
  filter_upwards [hfinAll] with ω hω
  have hp := hposAll (by linarith) hpos0 hω
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast spanHeight_le_n heps hω hp hn (layerCount_le hp n 1)

/-- **Lower bound on the expected height** (Markov at each of the first `L` layers). -/
theorem integral_spanHeight_ge [IsProbabilityMeasure P] (hZ : ∀ t, Measurable (Z t))
    (heps : 1 ≤ eps) (hfinAll : ∀ᵐ ω ∂P, AllLayersFinite eps (seq Z ω))
    (hpos0 : ∀ t ω, 1 ≤ (Z t ω).2) {n : ℕ} (hn : 1 ≤ n) (L : ℕ)
    (hint : ∀ ℓ, Integrable (fun ω => (leadSpan eps (seq Z ω) ℓ : ℝ)) P) :
    1 + L - ∑ i ∈ Finset.range L, (∫ ω, (leadSpan eps (seq Z ω) (i + 1) : ℝ) ∂P) / n ≤
      ∫ ω, (spanHeight eps (seq Z ω) n : ℝ) ∂P := by
  have heps0 : 0 ≤ eps := by linarith
  have hHmN := measurable_spanHeight_seq (eps := eps) hZ n
  have hHint := integrable_spanHeight hZ heps hfinAll hpos0 hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  -- probabilities of the tail events
  have hmeasH : ∀ k, MeasurableSet {ω | k < spanHeight eps (seq Z ω) n} := fun k =>
    measurableSet_lt measurable_const hHmN
  have hlead := measurable_leadSpan_seq (eps := eps) hZ
  have hP0 : P.real {ω | 0 < spanHeight eps (seq Z ω) n} = 1 := by
    have hae : ∀ᵐ ω ∂P, 0 < spanHeight eps (seq Z ω) n := by
      filter_upwards [hfinAll] with ω hω
      exact one_le_spanHeight heps hω (hposAll heps0 hpos0 hω) hn
    have hc : P {ω | 0 < spanHeight eps (seq Z ω) n}ᶜ = 0 := ae_iff.1 hae
    have h1 := probReal_compl_eq_one_sub (μ := P) (hmeasH 0)
    have h0 : P.real {ω | 0 < spanHeight eps (seq Z ω) n}ᶜ = 0 := by
      rw [measureReal_def, hc]; rfl
    linarith
  have hPk : ∀ i : ℕ, 1 - (∫ ω, (leadSpan eps (seq Z ω) (i + 1) : ℝ) ∂P) / n ≤
      P.real {ω | i + 1 < spanHeight eps (seq Z ω) n} := by
    intro i
    have hae : {ω | i + 1 < spanHeight eps (seq Z ω) n} =ᵐ[P]
        {ω | leadSpan eps (seq Z ω) (i + 1) < n} := by
      filter_upwards [hfinAll] with ω hω
      have hp := hposAll heps0 hpos0 hω
      exact propext (lt_spanHeight_iff heps0 hω (by omega) (exists_leadSpan_ge heps hω hp hn))
    rw [measureReal_congr hae]
    have hmeasL : MeasurableSet {ω | leadSpan eps (seq Z ω) (i + 1) < n} :=
      measurableSet_lt (hlead _) measurable_const
    have hcompl : {ω | leadSpan eps (seq Z ω) (i + 1) < n}ᶜ =
        {ω | (n : ℝ) ≤ (leadSpan eps (seq Z ω) (i + 1) : ℝ)} := by
      ext ω; simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt, Nat.cast_le]
    have hmark := mul_meas_ge_le_integral_of_nonneg
      (Eventually.of_forall fun ω => (Nat.cast_nonneg (leadSpan eps (seq Z ω) (i + 1)) : (0:ℝ) ≤ _))
      (hint (i + 1)) (n : ℝ)
    rw [← hcompl, probReal_compl_eq_one_sub hmeasL] at hmark
    have h2 : 1 - P.real {ω | leadSpan eps (seq Z ω) (i + 1) < n} ≤
        (∫ ω, (leadSpan eps (seq Z ω) (i + 1) : ℝ) ∂P) / n := by
      rw [le_div_iff₀ hn0]; linarith
    linarith
  -- the tail-sum formula
  have htail : ∑ k ∈ Finset.range (L + 1), P.real {ω | k < spanHeight eps (seq Z ω) n} ≤
      ∫ ω, (spanHeight eps (seq Z ω) n : ℝ) ∂P := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => Nat.cast_nonneg _)
      hHint.aestronglyMeasurable]
    simp only [ENNReal.ofReal_natCast]
    rw [lintegral_nat_eq_tsum hHmN]
    have hfin : ∑' k : ℕ, P {ω | k < spanHeight eps (seq Z ω) n} ≠ ⊤ := by
      rw [← lintegral_nat_eq_tsum hHmN]
      have := hHint.2
      rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => Nat.cast_nonneg _)] at this
      simpa using this.ne
    calc ∑ k ∈ Finset.range (L + 1), P.real {ω | k < spanHeight eps (seq Z ω) n}
        = (∑ k ∈ Finset.range (L + 1), P {ω | k < spanHeight eps (seq Z ω) n}).toReal := by
          rw [ENNReal.toReal_sum fun _ _ => measure_ne_top _ _]; rfl
      _ ≤ (∑' k : ℕ, P {ω | k < spanHeight eps (seq Z ω) n}).toReal :=
          ENNReal.toReal_mono hfin (ENNReal.sum_le_tsum _)
  rw [Finset.sum_range_succ', hP0] at htail
  have hsum : ∑ i ∈ Finset.range L, (1 - (∫ ω, (leadSpan eps (seq Z ω) (i + 1) : ℝ) ∂P) / n) ≤
      ∑ i ∈ Finset.range L, P.real {ω | i + 1 < spanHeight eps (seq Z ω) n} :=
    Finset.sum_le_sum fun i _ => hPk i
  rw [Finset.sum_sub_distrib] at hsum
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hsum
  linarith

end

end PGM
