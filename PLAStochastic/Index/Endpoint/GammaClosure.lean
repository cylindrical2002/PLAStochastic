import PLAStochastic.ForMathlib.Probability.Distributions.GammaLukacs
import PLAStochastic.Index.OneLayer.FiniteFirstSegment
import PLAStochastic.Index.Endpoint.LayerInduction

/-!
# Exact Gamma closure of the endpoint hierarchy (`prop:gammaDirclosure`)

`GammaKernel P Z` says that the first pair `(gap, count)` of the pair sequence `Z` has
the Gamma kernel: conditionally on `count = m ≥ 1` the gap is `Gamma(m, 1)`.

* `pi_gammaMeasure_inter_sum` (in `PLAStochastic.ForMathlib.Probability.Distributions.GammaLukacs`), random-variable form
  `measure_scaleInv_inter_sum`: for independent `Gamma(aᵢ, 1)` coordinates and a
  scale-invariant event `S`, `law(S ∩ {∑ xᵢ ∈ A}) = law(S) · Gamma(∑ aᵢ, 1)(A)`.
* `measure_gaps_counts`: for an iid pair sequence with the Gamma kernel, the first `t`
  gaps restricted to the shape event `{counts = n}` have law
  `(∏ P(count = nᵢ)) · ⊗ Gamma(nᵢ, 1)`.
* `pairSegLen_eq_iff_mem_segSet`, `segSet_smul`: the event `{T = t}` is a scale-invariant
  event of the first `t` gaps.
* `measure_total_inter_segLen_shape` (the precise statement of the proposition): on a
  shape event the total of the first `t` gaps is `Gamma(∑ nᵢ, 1)` and independent of
  `{T = t}`.
* **Closure step** `gammaKernel_nextLayer`: decomposing `{count' = m}` over the first
  segment length `t` and the shape `(n₁, …, n_t)` with `∑ nᵢ = m`, each piece has the
  `Gamma(m, 1)` law, so the next layer again has the Gamma kernel.
* **Reference hierarchy** `gammaKernel_epLayerSeq`: on iid `Exp(1)` input gaps every
  layer of the endpoint hierarchy has the Gamma kernel, for every `eps ≥ 0`; the needed
  almost sure finiteness of each layer's first segment follows from the Gamma kernel
  (`ae_pairSegLen_ne_top_of_gammaKernel`).
* Corollary `integral_fst_eq_integral_snd`, `lmean_eq_lcount_epLayerSeq`: the mean gap
  equals the mean count.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace PGM

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {Z : ℕ → Ω → ℝ × ℕ}

/-- The first pair has the Gamma kernel: conditionally on `count = m ≥ 1`, the gap is
`Gamma(m, 1)`. -/
def GammaKernel (P : Measure Ω) (Z : ℕ → Ω → ℝ × ℕ) : Prop :=
  ∀ (m : ℕ) (A : Set ℝ), MeasurableSet A → 1 ≤ m →
    P {ω | (Z 0 ω).1 ∈ A ∧ (Z 0 ω).2 = m} = P {ω | (Z 0 ω).2 = m} * gammaMeasure (m : ℝ) 1 A

/-! ## The first segment length as a scale-invariant event of the first gaps -/

/-- The segment has exactly `t` keys iff the first `t` keys are feasible and the first
`t + 1` are not. -/
theorem segLen_eq_coe_iff {eps : ℝ} {p : ℕ → ℝ} (t : ℕ) :
    segLen eps p = (t : ℕ∞) ↔
      prefixAffineFeasible eps p t ∧ ¬ prefixAffineFeasible eps p (t + 1) := by
  constructor
  · intro h
    refine ⟨?_, fun hf => ?_⟩
    · cases t with
      | zero => exact prefixAffineFeasible_zero eps p
      | succ j =>
        exact (lt_segLen_iff j).1 (by rw [h]; exact_mod_cast Nat.lt_succ_self j)
    · have := (lt_segLen_iff t).2 hf
      rw [h] at this
      exact lt_irrefl _ this
  · rintro ⟨h1, h2⟩
    have hle : segLen eps p ≤ t := (segLen_le_iff t).2 h2
    refine le_antisymm hle ?_
    cases t with
    | zero => exact zero_le
    | succ j =>
      have := (lt_segLen_iff j).2 h1
      exact Order.add_one_le_of_lt this

/-- Extension of a finite gap vector by zeros. -/
def finExt {t : ℕ} (x : Fin t → ℝ) (j : ℕ) : ℝ := if h : j < t then x ⟨j, h⟩ else 0

/-- Keys of a finite gap vector. -/
def vecKeys {t : ℕ} (x : Fin t → ℝ) : ℕ → ℝ := gapKeys (finExt x)

theorem measurable_finExt (t : ℕ) : Measurable (finExt (t := t)) := by
  refine measurable_pi_lambda _ fun j => ?_
  by_cases hj : j < t
  · simp only [finExt, hj, dif_pos]
    exact measurable_pi_apply _
  · simp only [finExt, hj, dif_neg, not_false_eq_true]
    exact measurable_const

theorem measurable_vecKeys (t : ℕ) : Measurable (vecKeys (t := t)) :=
  measurable_gapKeys.comp (measurable_finExt t)

theorem vecKeys_smul {t : ℕ} (c : ℝ) (x : Fin t → ℝ) (i : ℕ) :
    vecKeys (c • x) i = c * vecKeys x i + 0 := by
  simp only [vecKeys, gapKeys, finExt, Finset.mul_sum, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

/-- The first gap vectors whose ALG-OPT segment has exactly `t` keys. -/
def segSet (eps : ℝ) (t : ℕ) : Set (Fin t → ℝ) :=
  {x | prefixAffineFeasible eps (vecKeys x) t ∧ ¬ prefixAffineFeasible eps (vecKeys x) (t + 1)}

theorem measurableSet_segSet (eps : ℝ) (t : ℕ) : MeasurableSet (segSet eps t) :=
  ((measurable_vecKeys t) (measurableSet_prefixAffineFeasible eps t)).inter
    ((measurable_vecKeys t) (measurableSet_prefixAffineFeasible eps (t + 1))).compl

/-- The segment event is invariant under positive scaling of the gaps. -/
theorem segSet_smul {eps : ℝ} {t : ℕ} {c : ℝ} (hc : 0 < c) {x : Fin t → ℝ}
    (hx : x ∈ segSet eps t) : c • x ∈ segSet eps t := by
  have e : vecKeys (c • x) = fun i => c * vecKeys x i + 0 := funext (vecKeys_smul c x)
  simp only [segSet, mem_ofPred_eq, e, prefixAffineFeasible_affine_iff hc.ne'] at hx ⊢
  exact hx

/-- `{T = t}` is the event that the first `t` gaps lie in `segSet eps t`. -/
theorem pairSegLen_eq_iff_mem_segSet (eps : ℝ) (z : ℕ → ℝ × ℕ) (t : ℕ) :
    pairSegLen eps z = t ↔ (fun i : Fin t => (z i).1) ∈ segSet eps t := by
  have hk : ∀ s ≤ t, pairKeys z s = vecKeys (fun i : Fin t => (z i).1) s := by
    refine gapKeys_congr (g := fun s => (z s).1) (g' := finExt fun i : Fin t => (z i).1)
      fun i hi => ?_
    simp [finExt, hi]
  rw [pairSegLen, segLen_eq_coe_iff, segSet, mem_ofPred_eq,
    prefixAffineFeasible_congr (len := t) fun i hi => hk i hi.le,
    prefixAffineFeasible_congr (len := t + 1) fun i hi => hk i (by omega)]

/-- On `{T = t}` the first block is the sum of the first `t` pairs. -/
theorem firstBlock_of_eq {eps : ℝ} {z : ℕ → ℝ × ℕ} {t : ℕ} (h : pairSegLen eps z = t) :
    firstBlock eps z = ∑ i : Fin t, z i := by
  rw [firstBlock, h, ENat.toNat_natCast, Fin.sum_univ_eq_sum_range (fun i => z i)]

/-! ## Scale-invariant events of independent Gamma random variables -/

/-- **Lukacs, random-variable form.**  If `X 0, …, X (t-1)` (`t ≥ 1`) are independent with
`X i ∼ Gamma(nᵢ, 1)`, `nᵢ ≥ 1`, and `S` is a measurable set invariant under multiplication
by positive scalars, then `P(X ∈ S, ∑ Xᵢ ∈ A) = P(X ∈ S) · Gamma(∑ nᵢ, 1)(A)`. -/
theorem measure_scaleInv_inter_sum {t : ℕ} (ht : 0 < t) {X : Fin t → Ω → ℝ} (n : Fin t → ℕ)
    (hn : ∀ i, 1 ≤ n i) (hX : ∀ i, HasLaw (X i) (gammaMeasure (n i : ℝ) 1) P)
    (hind : iIndepFun X P) {S : Set (Fin t → ℝ)} (hS : MeasurableSet S)
    (hSs : ∀ c : ℝ, 0 < c → ∀ x ∈ S, c • x ∈ S) {A : Set ℝ} (hA : MeasurableSet A) :
    P {ω | (fun i => X i ω) ∈ S ∧ ∑ i, X i ω ∈ A} =
      P {ω | (fun i => X i ω) ∈ S} * gammaMeasure ((∑ i, n i : ℕ) : ℝ) 1 A := by
  have hlaw := hind.hasLaw_pi hX
  have hsumm : MeasurableSet {x : Fin t → ℝ | ∑ i, x i ∈ A} :=
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply i) hA
  rw [hlaw.measure_eq (p := fun x => x ∈ S ∧ ∑ i, x i ∈ A) (hS.inter hsumm),
    hlaw.measure_eq (p := fun x => x ∈ S) hS, Nat.cast_sum]
  exact pi_gammaMeasure_inter_sum ht (fun i => (n i : ℝ)) (fun i => by have := hn i; positivity)
    hS hSs hA

/-! ## The law of the first gaps on a shape event -/

/-- For an iid pair sequence with the Gamma kernel, the first `t` gaps restricted to the
shape event `{(count₀, …, count_{t-1}) = n}` have law `(∏ P(count = nᵢ)) · ⊗ Gamma(nᵢ, 1)`. -/
theorem measure_gaps_counts [IsProbabilityMeasure P] (h : IIDPairs P Z) (hK : GammaKernel P Z)
    {t : ℕ} (n : Fin t → ℕ) (hn : ∀ i, 1 ≤ n i) {B : Set (Fin t → ℝ)} (hB : MeasurableSet B) :
    P ({ω | (fun i : Fin t => (Z i ω).1) ∈ B} ∩ {ω | ∀ i : Fin t, (Z i ω).2 = n i}) =
      (∏ i, P {ω | (Z 0 ω).2 = n i}) * Measure.pi (fun i => gammaMeasure (n i : ℝ) 1) B := by
  set c : Fin t → ℝ≥0∞ := fun i => P {ω | (Z 0 ω).2 = n i} with hc
  set Γ : Fin t → Measure ℝ := fun i => gammaMeasure (n i : ℝ) 1 with hΓ
  have hΓp : ∀ i, IsProbabilityMeasure (Γ i) := fun i =>
    isProbabilityMeasure_gammaMeasure (by have := hn i; positivity) one_pos
  have hcΓ : ∀ i, SigmaFinite (c i • Γ i) := fun i => by
    have := (Γ i).smul_finite (measure_ne_top P {ω | (Z 0 ω).2 = n i})
    infer_instance
  set gv : Ω → Fin t → ℝ := fun ω i => (Z i ω).1 with hgvdef
  set C : Set Ω := {ω | ∀ i : Fin t, (Z i ω).2 = n i} with hCdef
  have hgv : Measurable gv := measurable_pi_lambda _ fun i => (h.measurable i).fst
  have hC : MeasurableSet C := by
    have : C = ⋂ i : Fin t, (fun ω => (Z i ω).2) ⁻¹' {n i} := by ext; simp [C]
    rw [this]
    exact MeasurableSet.iInter fun i => (h.measurable i).snd (measurableSet_singleton _)
  have hind : iIndepFun (fun i : Fin t => Z i) P :=
    h.indep.precomp (g := fun i : Fin t => (i : ℕ)) Fin.val_injective
  have h1 : (P.restrict C).map gv = Measure.pi (fun i => c i • Γ i) := by
    refine (Measure.pi_eq fun s hs => ?_).symm
    rw [Measure.map_apply hgv (MeasurableSet.univ_pi hs),
      Measure.restrict_apply (hgv (MeasurableSet.univ_pi hs))]
    have e : gv ⁻¹' univ.pi s ∩ C = ⋂ i ∈ (Finset.univ : Finset (Fin t)),
        (fun i : Fin t => Z i) i ⁻¹' (s i ×ˢ {n i}) := by
      ext ω
      simp [gv, C, forall_and]
    rw [e, hind.measure_inter_preimage_eq_mul _ fun i _ => (hs i).prod (measurableSet_singleton _)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [(h.ident i).measure_mem_eq ((hs i).prod (measurableSet_singleton _)), Measure.smul_apply,
      smul_eq_mul]
    have e2 : Z 0 ⁻¹' (s i ×ˢ {n i}) = {ω | (Z 0 ω).1 ∈ s i ∧ (Z 0 ω).2 = n i} := by
      ext; simp
    rw [e2, hK _ _ (hs i) (hn i)]
  have h2 : Measure.pi (fun i => c i • Γ i) = (∏ i, c i) • Measure.pi Γ := by
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.smul_apply, smul_eq_mul, Measure.pi_pi, ← Finset.prod_mul_distrib]
    rfl
  rw [show {ω | gv ω ∈ B} = gv ⁻¹' B from rfl, ← Measure.restrict_apply (hgv hB),
    ← Measure.map_apply hgv hB, h1, h2, Measure.smul_apply, smul_eq_mul]

/-! ## Positivity of the gap law under the Gamma kernel -/

theorem gammaMeasure_ne_zero {b : ℝ} (hb : 0 < b) {I : Set ℝ} {a c : ℝ} (hac : a < c)
    (ha : 0 ≤ a) (hI : Ioo a c ⊆ I) : gammaMeasure b 1 I ≠ 0 := by
  intro h0
  have h1 := measure_mono_null hI h0
  rw [gammaMeasure, withDensity_apply_eq_zero (f := gammaPDF b 1)
    (measurable_gammaPDFReal b 1).ennreal_ofReal] at h1
  have e : {x | gammaPDF b 1 x ≠ 0} ∩ Ioo a c = Ioo a c := by
    refine inter_eq_right.2 fun x hx => ?_
    simp only [mem_ofPred_eq, gammaPDF, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact gammaPDFReal_pos hb one_pos (lt_of_le_of_lt ha hx.1)
  rw [e, Real.volume_Ioo, ENNReal.ofReal_eq_zero] at h1
  linarith

/-- Under the Gamma kernel with positive counts, some count value has positive mass. -/
theorem exists_count_ne_zero [IsProbabilityMeasure P] (h0 : P {ω | (Z 0 ω).2 = 0} = 0) :
    ∃ m, 1 ≤ m ∧ P {ω | (Z 0 ω).2 = m} ≠ 0 := by
  by_contra hne
  push Not at hne
  have hall : ∀ m, P {ω | (Z 0 ω).2 = m} = 0 := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact h0
    · exact hne m hm
  have : P (⋃ m : ℕ, {ω | (Z 0 ω).2 = m}) = 0 := measure_iUnion_null hall
  have e : (⋃ m : ℕ, {ω | (Z 0 ω).2 = m}) = univ := by
    ext ω; simp
  rw [e, measure_univ] at this
  exact one_ne_zero this

/-- Under the Gamma kernel with positive counts, the gap puts positive mass on every
interval `(a, c) ⊆ [0, ∞)`. -/
theorem measure_gap_ne_zero [IsProbabilityMeasure P] (hK : GammaKernel P Z)
    (h0 : P {ω | (Z 0 ω).2 = 0} = 0) {I : Set ℝ} (hIm : MeasurableSet I) {a c : ℝ}
    (hac : a < c) (ha : 0 ≤ a) (hI : Ioo a c ⊆ I) : P {ω | (Z 0 ω).1 ∈ I} ≠ 0 := by
  obtain ⟨m, hm, hPm⟩ := exists_count_ne_zero h0
  have hle : P {ω | (Z 0 ω).1 ∈ I ∧ (Z 0 ω).2 = m} ≤ P {ω | (Z 0 ω).1 ∈ I} :=
    measure_mono fun ω hω => hω.1
  rw [hK m I hIm hm] at hle
  intro hz
  rw [hz, nonpos_iff_eq_zero, mul_eq_zero] at hle
  rcases hle with h1 | h1
  · exact hPm h1
  · exact gammaMeasure_ne_zero (by exact_mod_cast hm) hac ha hI h1

/-- Under the Gamma kernel with positive counts, the first segment is almost surely
finite. -/
theorem ae_pairSegLen_ne_top_of_gammaKernel [IsProbabilityMeasure P] (h : IIDPairs P Z)
    (hK : GammaKernel P Z) (h0 : P {ω | (Z 0 ω).2 = 0} = 0) (eps : ℝ) :
    ∀ᵐ ω ∂P, pairSegLen eps (seq Z ω) ≠ ⊤ :=
  ae_gapSegLen_ne_top h.fst eps
    (measure_gap_ne_zero hK h0 measurableSet_Icc (by norm_num : (0 : ℝ) < 2) le_rfl
      Ioo_subset_Icc_self)
    (measure_gap_ne_zero hK h0 (measurableSet_Ici (a := (8 : ℝ)))
      (by norm_num : (8 : ℝ) < 9) (by norm_num) fun x hx => le_of_lt hx.1)

/-! ## The closure step -/

theorem measure_count_eq_zero (hpos : ∀ᵐ ω ∂P, 1 ≤ (Z 0 ω).2) :
    P {ω | (Z 0 ω).2 = 0} = 0 :=
  measure_mono_null (fun ω (hω : (Z 0 ω).2 = 0) => by simp [hω]) (ae_iff.1 hpos)

theorem measurableSet_shape (h : IIDPairs P Z) {t : ℕ} (n : Fin t → ℕ) :
    MeasurableSet {ω | ∀ i : Fin t, (Z i ω).2 = n i} := by
  have : {ω | ∀ i : Fin t, (Z i ω).2 = n i} = ⋂ i : Fin t, (fun ω => (Z i ω).2) ⁻¹' {n i} := by
    ext; simp
  rw [this]
  exact MeasurableSet.iInter fun i => (h.measurable i).snd (measurableSet_singleton _)

/-- Decomposition of an event over the first segment length `t` and the shape
`(count₀, …, count_{t-1})`. -/
theorem measure_eq_tsum_shape (h : IIDPairs P Z) (eps : ℝ)
    (hfin : ∀ᵐ ω ∂P, pairSegLen eps (seq Z ω) ≠ ⊤) {S : Set Ω} (hS : MeasurableSet S) :
    P S = ∑' t : ℕ, ∑' n : Fin t → ℕ,
      P (S ∩ {ω | pairSegLen eps (seq Z ω) = t} ∩ {ω | ∀ i : Fin t, (Z i ω).2 = n i}) := by
  have hT : Measurable (fun ω => pairSegLen eps (seq Z ω)) :=
    (measurable_pairSegLen eps).comp (measurable_seq h.measurable)
  rw [measure_eq_tsum_eq_coe hT hfin hS]
  refine tsum_congr fun t => ?_
  have hTt : MeasurableSet {ω | pairSegLen eps (seq Z ω) = t} := hT (measurableSet_singleton _)
  have e : S ∩ {ω | pairSegLen eps (seq Z ω) = t} = ⋃ n : Fin t → ℕ,
      (S ∩ {ω | pairSegLen eps (seq Z ω) = t} ∩ {ω | ∀ i : Fin t, (Z i ω).2 = n i}) := by
    ext ω
    simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun i => (Z i ω).2, ⟨h1, h2⟩, fun i => rfl⟩
    · rintro ⟨n, ⟨h1, h2⟩, -⟩
      exact ⟨h1, h2⟩
  have hP := congrArg P e
  rw [hP]
  refine measure_iUnion (fun n n' hnn' => ?_) fun n => (hS.inter hTt).inter (measurableSet_shape h n)
  refine Set.disjoint_left.2 fun ω h1 h2 => hnn' ?_
  funext i
  exact (h1.2 i).symm.trans (h2.2 i)

/-- **The precise closure statement.**  On the shape event
`(count₀, …, count_{t-1}) = n` (all `nᵢ ≥ 1`, `t ≥ 1`), the total `G_t = ∑_{i<t} gapᵢ` of the
first `t` gaps is `Gamma(∑ nᵢ, 1)` and independent of the cut event `{T = t}`. -/
theorem measure_total_inter_segLen_shape [IsProbabilityMeasure P] (h : IIDPairs P Z)
    (hK : GammaKernel P Z) (eps : ℝ) {t : ℕ} (ht : 0 < t) (n : Fin t → ℕ) (hn : ∀ i, 1 ≤ n i)
    {A : Set ℝ} (hA : MeasurableSet A) :
    P ({ω | ∑ i : Fin t, (Z i ω).1 ∈ A} ∩ {ω | pairSegLen eps (seq Z ω) = t} ∩
        {ω | ∀ i : Fin t, (Z i ω).2 = n i}) =
      P ({ω | pairSegLen eps (seq Z ω) = t} ∩ {ω | ∀ i : Fin t, (Z i ω).2 = n i}) *
        gammaMeasure ((∑ i, n i : ℕ) : ℝ) 1 A := by
  have hsumm : MeasurableSet {x : Fin t → ℝ | ∑ i, x i ∈ A} :=
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply i) hA
  have eA : {ω | ∑ i : Fin t, (Z i ω).1 ∈ A} ∩ {ω | pairSegLen eps (seq Z ω) = t} ∩
        {ω | ∀ i : Fin t, (Z i ω).2 = n i} =
      {ω | (fun i : Fin t => (Z i ω).1) ∈ segSet eps t ∩ {x | ∑ i, x i ∈ A}} ∩
        {ω | ∀ i : Fin t, (Z i ω).2 = n i} := by
    ext ω
    have hiff := pairSegLen_eq_iff_mem_segSet eps (seq Z ω) t
    simp only [mem_inter_iff, mem_ofPred_eq]
    exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨⟨hiff.1 h2, h1⟩, h3⟩,
      fun ⟨⟨h1, h2⟩, h3⟩ => ⟨⟨h2, hiff.2 h1⟩, h3⟩⟩
  have e1 : {ω | pairSegLen eps (seq Z ω) = t} ∩ {ω | ∀ i : Fin t, (Z i ω).2 = n i} =
      {ω | (fun i : Fin t => (Z i ω).1) ∈ segSet eps t} ∩
        {ω | ∀ i : Fin t, (Z i ω).2 = n i} := by
    ext ω
    have hiff := pairSegLen_eq_iff_mem_segSet eps (seq Z ω) t
    simp only [mem_inter_iff, mem_ofPred_eq]
    exact ⟨fun ⟨h1, h2⟩ => ⟨hiff.1 h1, h2⟩, fun ⟨h1, h2⟩ => ⟨hiff.2 h1, h2⟩⟩
  rw [eA, e1, measure_gaps_counts h hK n hn ((measurableSet_segSet eps t).inter hsumm),
    measure_gaps_counts h hK n hn (measurableSet_segSet eps t),
    pi_gammaMeasure_inter_sum ht (fun i => (n i : ℝ)) (fun i => by have := hn i; positivity)
      (measurableSet_segSet eps t) (fun c hc x hx => segSet_smul hc hx) hA, Nat.cast_sum,
    mul_assoc]

/-- **Gamma closure step.**  If the pairs are iid with the Gamma kernel and positive counts,
and the first segment is almost surely finite, the next layer has the Gamma kernel. -/
theorem gammaKernel_nextLayer [IsProbabilityMeasure P] (h : IIDPairs P Z)
    (hK : GammaKernel P Z) (hpos : ∀ᵐ ω ∂P, 1 ≤ (Z 0 ω).2) (eps : ℝ)
    (hfin : ∀ᵐ ω ∂P, pairSegLen eps (seq Z ω) ≠ ⊤) :
    GammaKernel P (nextLayer eps Z) := by
  intro m A hA hm
  have h0 := measure_count_eq_zero hpos
  have hY : Measurable (nextLayer eps Z 0) :=
    (measurable_firstBlock eps).comp (measurable_seq h.measurable)
  have hFA : MeasurableSet {ω | (nextLayer eps Z 0 ω).1 ∈ A ∧ (nextLayer eps Z 0 ω).2 = m} :=
    (hY.fst hA).inter (hY.snd (measurableSet_singleton m))
  have hF1 : MeasurableSet {ω | (nextLayer eps Z 0 ω).2 = m} :=
    hY.snd (measurableSet_singleton m)
  rw [measure_eq_tsum_shape h eps hfin hFA, measure_eq_tsum_shape h eps hfin hF1,
    ← ENNReal.tsum_mul_right]
  refine tsum_congr fun t => ?_
  rw [← ENNReal.tsum_mul_right]
  refine tsum_congr fun n => ?_
  have hsnd : ∀ ω, pairSegLen eps (seq Z ω) = t → (∀ i : Fin t, (Z i ω).2 = n i) →
      (nextLayer eps Z 0 ω).2 = ∑ i, n i := by
    intro ω hT hC
    rw [nextLayer_zero, firstBlock_of_eq hT, Prod.snd_sum]
    exact Finset.sum_congr rfl fun i _ => hC i
  have hfst : ∀ ω, pairSegLen eps (seq Z ω) = t →
      (nextLayer eps Z 0 ω).1 = ∑ i : Fin t, (Z i ω).1 := by
    intro ω hT
    rw [nextLayer_zero, firstBlock_of_eq hT, Prod.fst_sum]
    rfl
  by_cases hsum : ∑ i, n i = m
  · have eA : {ω | (nextLayer eps Z 0 ω).1 ∈ A ∧ (nextLayer eps Z 0 ω).2 = m} ∩
          {ω | pairSegLen eps (seq Z ω) = t} ∩ {ω | ∀ i : Fin t, (Z i ω).2 = n i} =
        {ω | ∑ i : Fin t, (Z i ω).1 ∈ A} ∩ {ω | pairSegLen eps (seq Z ω) = t} ∩
          {ω | ∀ i : Fin t, (Z i ω).2 = n i} := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨⟨⟨hA', -⟩, hT⟩, hC⟩
        rw [hfst ω hT] at hA'
        exact ⟨⟨hA', hT⟩, hC⟩
      · rintro ⟨⟨hA', hT⟩, hC⟩
        refine ⟨⟨⟨?_, ?_⟩, hT⟩, hC⟩
        · rw [hfst ω hT]; exact hA'
        · rw [hsnd ω hT hC, hsum]
    have e1 : {ω | (nextLayer eps Z 0 ω).2 = m} ∩
          {ω | pairSegLen eps (seq Z ω) = t} ∩ {ω | ∀ i : Fin t, (Z i ω).2 = n i} =
        {ω | pairSegLen eps (seq Z ω) = t} ∩ {ω | ∀ i : Fin t, (Z i ω).2 = n i} := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq]
      exact ⟨fun ⟨⟨_, hT⟩, hC⟩ => ⟨hT, hC⟩,
        fun ⟨hT, hC⟩ => ⟨⟨by rw [hsnd ω hT hC, hsum], hT⟩, hC⟩⟩
    rw [eA, e1]
    by_cases hn : ∀ i, 1 ≤ n i
    · have ht : 0 < t := by
        rcases Nat.eq_zero_or_pos t with rfl | ht
        · simp only [Finset.univ_eq_empty, Finset.sum_empty] at hsum
          omega
        · exact ht
      rw [measure_total_inter_segLen_shape h hK eps ht n hn hA, hsum]
    · push Not at hn
      obtain ⟨i, hi⟩ := hn
      have hi0 : n i = 0 := by omega
      have hz : P {ω | ∀ i : Fin t, (Z i ω).2 = n i} = 0 := by
        have hZi : P {ω | (Z i ω).2 = 0} = 0 := by
          have e : {ω | (Z i ω).2 = 0} = Z i ⁻¹' (Prod.snd ⁻¹' {0}) := rfl
          rw [e, (h.ident i).measure_mem_eq (measurable_snd (measurableSet_singleton 0))]
          exact h0
        refine measure_mono_null (fun ω hω => ?_) hZi
        simp only [mem_ofPred_eq] at hω ⊢
        rw [hω i, hi0]
      rw [measure_mono_null inter_subset_right hz, measure_mono_null inter_subset_right hz,
        zero_mul]
  · have e1 : {ω | (nextLayer eps Z 0 ω).2 = m} ∩
        {ω | pairSegLen eps (seq Z ω) = t} ∩ {ω | ∀ i : Fin t, (Z i ω).2 = n i} = ∅ := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro hm' hC
      exact hsum (by rw [← hsnd ω hm'.2 hC, hm'.1])
    have eA : {ω | (nextLayer eps Z 0 ω).1 ∈ A ∧ (nextLayer eps Z 0 ω).2 = m} ∩
          {ω | pairSegLen eps (seq Z ω) = t} ∩ {ω | ∀ i : Fin t, (Z i ω).2 = n i} ⊆
        {ω | (nextLayer eps Z 0 ω).2 = m} ∩
          {ω | pairSegLen eps (seq Z ω) = t} ∩ {ω | ∀ i : Fin t, (Z i ω).2 = n i} :=
      fun ω hω => ⟨⟨hω.1.1.2, hω.1.2⟩, hω.2⟩
    rw [measure_mono_null eA (by rw [e1, measure_empty]), e1, measure_empty, zero_mul]

/-! ## The reference hierarchy on exponential input gaps -/

/-- The law `Exp(1)` of the input gaps makes `P` a probability measure. -/
theorem isProbabilityMeasure_of_hasLaw_exp {g : Ω → ℝ} (hlaw : HasLaw g (expMeasure 1) P) :
    IsProbabilityMeasure P :=
  haveI := isProbabilityMeasure_expMeasure (r := 1) one_pos
  hlaw.isProbabilityMeasure

/-- Unit-rate exponential input gaps have the Gamma kernel (`Gamma(1, 1) = Exp(1)`). -/
theorem gammaKernel_inputPairs {g : ℕ → Ω → ℝ}
    (hlaw : HasLaw (g 0) (expMeasure 1) P) : GammaKernel P (inputPairs g) := by
  have := isProbabilityMeasure_of_hasLaw_exp hlaw
  intro m A hA hm
  simp only [inputPairs]
  by_cases h1 : (1 : ℕ) = m
  · subst h1
    simp only [and_true, ofPred_true, measure_univ, one_mul, Nat.cast_one]
    exact hlaw.measure_eq (p := fun x => x ∈ A) hA
  · simp [h1]

/-- Positive counts survive one layer: on `{T < ∞}` with positive counts the first
block has a positive count. -/
theorem ae_one_le_nextLayer_snd (h : IIDPairs P Z) {eps : ℝ} (heps : 0 ≤ eps)
    (hpos : ∀ᵐ ω ∂P, 1 ≤ (Z 0 ω).2) (hfin : ∀ᵐ ω ∂P, pairSegLen eps (seq Z ω) ≠ ⊤) :
    ∀ᵐ ω ∂P, 1 ≤ (nextLayer eps Z 0 ω).2 := by
  have hm : MeasurableSet {x : ℝ × ℕ | 1 ≤ x.2} := measurable_snd measurableSet_Ici
  filter_upwards [hfin, (h.ident 0).symm.ae_mem_snd hm hpos] with ω hT h0
  rw [nextLayer_zero, firstBlock, Prod.snd_sum]
  have h1 := one_le_toNat_pairSegLen heps hT
  calc 1 ≤ (Z 0 ω).2 := h0
    _ ≤ ∑ j ∈ Finset.range (pairSegLen eps (seq Z ω)).toNat, (seq Z ω j).2 :=
      Finset.single_le_sum (f := fun j => (seq Z ω j).2) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.2 h1)

/-- **One layer of the Gamma closure**, with all the invariants: iid pairs, the Gamma kernel,
positive counts; the first segment is almost surely finite. -/
theorem gammaLayer_step [IsProbabilityMeasure P] (h : IIDPairs P Z) (hK : GammaKernel P Z)
    (hpos : ∀ᵐ ω ∂P, 1 ≤ (Z 0 ω).2) {eps : ℝ} (heps : 0 ≤ eps) :
    (∀ᵐ ω ∂P, pairSegLen eps (seq Z ω) ≠ ⊤) ∧ IIDPairs P (nextLayer eps Z) ∧
      GammaKernel P (nextLayer eps Z) ∧ ∀ᵐ ω ∂P, 1 ≤ (nextLayer eps Z 0 ω).2 := by
  have hfin := ae_pairSegLen_ne_top_of_gammaKernel h hK (measure_count_eq_zero hpos) eps
  exact ⟨hfin, h.layerMap eps hfin, gammaKernel_nextLayer h hK hpos eps hfin,
    ae_one_le_nextLayer_snd h heps hpos hfin⟩

omit mΩ in
theorem epLayerSeq_succ (eps : ℝ) (g : ℕ → Ω → ℝ) (ℓ : ℕ) :
    epLayerSeq eps g (ℓ + 1) = nextLayer eps (epLayerSeq eps g ℓ) := by
  simp only [epLayerSeq, Function.iterate_succ_apply']

/-- **Exact Gamma closure of the endpoint hierarchy** (`prop:gammaDirclosure`).  On iid
`Exp(1)` input gaps and for every `eps ≥ 0`, every layer is an iid pair sequence with the
Gamma kernel and positive counts, and its first segment is almost surely finite. -/
theorem gammaClosure_epLayerSeq {g : ℕ → Ω → ℝ} (hg : IIDSeq P g)
    (hlaw : HasLaw (g 0) (expMeasure 1) P) {eps : ℝ} (heps : 0 ≤ eps) (ℓ : ℕ) :
    IIDPairs P (epLayerSeq eps g ℓ) ∧ GammaKernel P (epLayerSeq eps g ℓ) ∧
      (∀ᵐ ω ∂P, 1 ≤ (epLayerSeq eps g ℓ 0 ω).2) ∧
      ∀ᵐ ω ∂P, pairSegLen eps (seq (epLayerSeq eps g ℓ) ω) ≠ ⊤ := by
  have := isProbabilityMeasure_of_hasLaw_exp hlaw
  have key : ∀ ℓ, IIDPairs P (epLayerSeq eps g ℓ) ∧ GammaKernel P (epLayerSeq eps g ℓ) ∧
      ∀ᵐ ω ∂P, 1 ≤ (epLayerSeq eps g ℓ 0 ω).2 := by
    intro ℓ
    induction ℓ with
    | zero =>
      refine ⟨IIDPairs.inputPairs hg, gammaKernel_inputPairs hlaw, ?_⟩
      exact ae_of_all _ fun ω => le_refl 1
    | succ ℓ ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      obtain ⟨-, h4, h5, h6⟩ := gammaLayer_step h1 h2 h3 heps
      rw [epLayerSeq_succ]
      exact ⟨h4, h5, h6⟩
  obtain ⟨h1, h2, h3⟩ := key ℓ
  exact ⟨h1, h2, h3, (gammaLayer_step h1 h2 h3 heps).1⟩

/-- Every layer of the exponential reference hierarchy has the Gamma kernel. -/
theorem gammaKernel_epLayerSeq {g : ℕ → Ω → ℝ} (hg : IIDSeq P g)
    (hlaw : HasLaw (g 0) (expMeasure 1) P) {eps : ℝ} (heps : 0 ≤ eps) (ℓ : ℕ) :
    GammaKernel P (epLayerSeq eps g ℓ) :=
  (gammaClosure_epLayerSeq hg hlaw heps ℓ).2.1

/-- Almost surely every segment of every layer of the exponential reference hierarchy is
finite. -/
theorem ae_allLayersFinite_exp {g : ℕ → Ω → ℝ} (hg : IIDSeq P g)
    (hlaw : HasLaw (g 0) (expMeasure 1) P) {eps : ℝ} (heps : 0 ≤ eps) :
    ∀ᵐ ω ∂P, AllLayersFinite eps (seq (inputPairs g) ω) := by
  have := isProbabilityMeasure_of_hasLaw_exp hlaw
  refine ae_allLayersFinite (IIDPairs.inputPairs hg) eps fun ℓ => ?_
  have := (gammaClosure_epLayerSeq hg hlaw heps ℓ).2.2.2
  simpa only [seq_epLayerSeq] using this

/-! ## The mean gap equals the mean count -/

/-- The mean of `Gamma(m, 1)` is `m`. -/
theorem lintegral_ofReal_gammaMeasure {m : ℕ} (hm : 1 ≤ m) :
    ∫⁻ x, ENNReal.ofReal x ∂(gammaMeasure (m : ℝ) 1) = m := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  rw [gammaMeasure, lintegral_withDensity_eq_lintegral_mul _ (f := gammaPDF (m : ℝ) 1)
    (measurable_gammaPDFReal _ _).ennreal_ofReal ENNReal.measurable_ofReal]
  have hpt : ∀ x : ℝ, (gammaPDF (m : ℝ) 1 * fun x => ENNReal.ofReal x) x =
      ENNReal.ofReal (1 / Real.Gamma m) *
        (Ioi 0).indicator (fun x => ENNReal.ofReal (x ^ m * Real.exp (-x))) x := by
    intro x
    simp only [Pi.mul_apply]
    rcases le_or_gt x 0 with hx | hx
    · rw [indicator_of_notMem (show x ∉ Ioi 0 from not_lt.2 hx), mul_zero,
        ENNReal.ofReal_of_nonpos hx, mul_zero]
    · rw [indicator_of_mem (show x ∈ Ioi 0 from hx), gammaPDF_of_nonneg hx.le,
        ← ENNReal.ofReal_mul (by have := Real.Gamma_pos_of_pos hmpos; positivity),
        ← ENNReal.ofReal_mul (by have := Real.Gamma_pos_of_pos hmpos; positivity)]
      congr 1
      rw [Real.one_rpow, Real.rpow_sub_one hx.ne', Real.rpow_natCast]
      field_simp
  rw [lintegral_congr fun x => hpt x, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_indicator measurableSet_Ioi, PGM.Renyi.lintegral_pow_mul_exp_neg]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 by push_cast; ring, Real.Gamma_nat_eq_factorial,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_natCast]
  congr 1
  rw [Nat.factorial_succ]
  push_cast
  field_simp

/-- Under the Gamma kernel with positive counts the gap is almost surely nonnegative. -/
theorem ae_gap_nonneg (hK : GammaKernel P Z) (hpos : ∀ᵐ ω ∂P, 1 ≤ (Z 0 ω).2) :
    ∀ᵐ ω ∂P, 0 ≤ (Z 0 ω).1 := by
  have h0 := measure_count_eq_zero hpos
  rw [ae_iff]
  have e : {ω | ¬ 0 ≤ (Z 0 ω).1} ⊆ ⋃ m : ℕ, {ω | (Z 0 ω).1 ∈ Iio 0 ∧ (Z 0 ω).2 = m} := by
    intro ω hω
    simp only [mem_iUnion, mem_ofPred_eq, mem_Iio]
    exact ⟨_, not_le.1 hω, rfl⟩
  refine measure_mono_null e (measure_iUnion_null fun m => ?_)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact measure_mono_null (fun ω hω => hω.2) h0
  · rw [hK m _ measurableSet_Iio hm]
    have : gammaMeasure (m : ℝ) 1 (Iio 0) = 0 := by
      rw [gammaMeasure, withDensity_apply _ measurableSet_Iio]
      exact lintegral_gammaPDF_of_nonpos le_rfl
    rw [this, mul_zero]

/-- Under the Gamma kernel with positive counts, `E[gap] = E[count]` (in `ℝ≥0∞`). -/
theorem lintegral_gap_eq_lintegral_count (hK : GammaKernel P Z) (hZ : Measurable (Z 0))
    (hpos : ∀ᵐ ω ∂P, 1 ≤ (Z 0 ω).2) :
    ∫⁻ ω, ENNReal.ofReal (Z 0 ω).1 ∂P = ∫⁻ ω, ((Z 0 ω).2 : ℝ≥0∞) ∂P := by
  have h0 := measure_count_eq_zero hpos
  set s : ℕ → Set Ω := fun m => {ω | (Z 0 ω).2 = m} with hsdef
  have hs : ∀ m, MeasurableSet (s m) := fun m => hZ.snd (measurableSet_singleton m)
  have hd : Pairwise (Function.onFun Disjoint s) := by
    intro i j hij
    exact Set.disjoint_left.2 fun ω h1 h2 => hij (h1.symm.trans h2)
  have hU : (⋃ m, s m) = univ := by
    ext ω
    simp [s]
  have hsplit : ∀ f : Ω → ℝ≥0∞, ∫⁻ ω, f ω ∂P = ∑' m, ∫⁻ ω in s m, f ω ∂P := by
    intro f
    rw [← lintegral_iUnion hs hd, hU, Measure.restrict_univ]
  rw [hsplit, hsplit]
  refine tsum_congr fun m => ?_
  rw [show ∫⁻ ω in s m, ((Z 0 ω).2 : ℝ≥0∞) ∂P = ∫⁻ ω in s m, (m : ℝ≥0∞) ∂P from
    setLIntegral_congr_fun (hs m) (fun ω (hω : (Z 0 ω).2 = m) => by rw [hω]),
    setLIntegral_const]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have : P.restrict (s 0) = 0 := Measure.restrict_eq_zero.2 h0
    rw [this, lintegral_zero_measure]
    simp
  · have hmap : (P.restrict (s m)).map (fun ω => (Z 0 ω).1) =
        P (s m) • gammaMeasure (m : ℝ) 1 := by
      ext A hA
      rw [Measure.map_apply hZ.fst hA, Measure.restrict_apply (hZ.fst hA), Measure.smul_apply,
        smul_eq_mul, ← hK m A hA hm]
      rfl
    rw [← lintegral_map (f := ENNReal.ofReal) ENNReal.measurable_ofReal hZ.fst, hmap,
      lintegral_smul_measure, lintegral_ofReal_gammaMeasure hm, smul_eq_mul, mul_comm]

/-- Under the Gamma kernel with positive counts, `E[gap] = E[count]`. -/
theorem integral_fst_eq_integral_snd (hK : GammaKernel P Z) (hZ : Measurable (Z 0))
    (hpos : ∀ᵐ ω ∂P, 1 ≤ (Z 0 ω).2) :
    ∫ ω, (Z 0 ω).1 ∂P = ∫ ω, ((Z 0 ω).2 : ℝ) ∂P := by
  have hN : Measurable fun ω => ((Z 0 ω).2 : ℝ) :=
    (Measurable.of_discrete (f := fun n : ℕ => (n : ℝ))).comp hZ.snd
  rw [integral_eq_lintegral_of_nonneg_ae (ae_gap_nonneg hK hpos) hZ.fst.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => Nat.cast_nonneg _)
      hN.aestronglyMeasurable]
  simp_rw [ENNReal.ofReal_natCast]
  rw [lintegral_gap_eq_lintegral_count hK hZ hpos]

/-- In the exponential reference hierarchy the mean layer gap equals the mean number of
input gaps it spans. -/
theorem lmean_eq_lcount_epLayerSeq {g : ℕ → Ω → ℝ}
    (hg : IIDSeq P g) (hlaw : HasLaw (g 0) (expMeasure 1) P) {eps : ℝ} (heps : 0 ≤ eps)
    (ℓ : ℕ) : lmean P (epLayerSeq eps g ℓ) = lcount P (epLayerSeq eps g ℓ) := by
  obtain ⟨h1, h2, h3, -⟩ := gammaClosure_epLayerSeq hg hlaw heps ℓ
  exact integral_fst_eq_integral_snd h2 (h1.measurable 0) h3

end PGM
