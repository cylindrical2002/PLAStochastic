import PLAStochastic.Index.Model.IIDGaps
import PLAStochastic.Index.Algorithm.EndpointHierarchy

/-!
# The iid pair model

A layer of the endpoint hierarchy is a sequence of pairs `(gap, count)`.  For an iid
sequence of pairs `Z` (`IIDPairs P Z`) with natural filtration
`pairFiltration Z _ t = σ(Z 0, …, Z (t - 1))` this file provides:

* the gap components form an iid real sequence (`IIDPairs.fst`), shifts are iid
  (`IIDPairs.shift`), and centred measurable functionals of the pairs have independent
  increments for the pair filtration (`IIDPairs.indepIncrements`);
* the first segment length is a stopping index for the pair filtration
  (`pairSegLen_lt_measurable`) and a stopping rule on sequence space
  (`isStoppingRule_pairSegLen`);
* measurability of the aggregated first block, the restart map and the layer map
  (`measurable_firstBlock`, `measurable_pairShift`, `measurable_layerMap`,
  `measurable_pairLayer`), and the fact that the first block only reads the stopped
  block (`firstBlock_stopped`);
* **layer regeneration**: if the first segment is almost surely finite, the next layer
  is again an iid pair sequence whose pairs have the law of the first block
  (`IIDPairs.layerMap`, `identDistrib_layerMap_zero`), and almost surely all segments
  are finite (`ae_allSegmentsFinite`); iterating, every layer is iid and almost surely
  all layers have finite segments, provided each layer's first segment is almost surely
  finite (`IIDPairs.pairLayer`, `ae_allLayersFinite`);
* the future `(Z m, Z (m + 1), …)` is independent of the pair filtration at `m`
  (`indep_future_pairFiltration`, `measure_future_inter_pairFiltration`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace PGM

/-! ## Stopping rule and measurability on pair sequence space -/

/-- The first segment length of a pair sequence is a stopping rule. -/
theorem isStoppingRule_pairSegLen (eps : ℝ) : IsStoppingRule (pairSegLen eps) :=
  isStoppingRule_gapSegLen_fst eps

theorem measurable_pairSegLen (eps : ℝ) : Measurable (pairSegLen eps) :=
  (isStoppingRule_pairSegLen eps).measurable

/-- The aggregated first block is measurable. -/
theorem measurable_firstBlock (eps : ℝ) : Measurable (firstBlock eps) := by
  have hm : Measurable (fun p : (ℕ → ℝ × ℕ) × ℕ => ∑ t ∈ Finset.range p.2, p.1 t) :=
    measurable_from_prod_countable_left fun n => by
      change Measurable fun z : ℕ → ℝ × ℕ => ∑ t ∈ Finset.range n, z t
      exact Finset.measurable_sum _ fun t _ => measurable_pi_apply t
  exact hm.comp (measurable_id.prodMk
    ((Measurable.of_discrete (f := ENat.toNat)).comp (measurable_pairSegLen eps)))

/-- The first block only reads the stopped block. -/
theorem firstBlock_stopped (eps : ℝ) {z z' : ℕ → ℝ × ℕ}
    (hτ : pairSegLen eps z = pairSegLen eps z')
    (h : ∀ t : ℕ, (t : ℕ∞) < pairSegLen eps z → z t = z' t) :
    firstBlock eps z = firstBlock eps z' := by
  unfold firstBlock
  rw [← hτ]
  refine Finset.sum_congr rfl fun t ht => h t ?_
  rw [Finset.mem_range] at ht
  exact lt_of_lt_of_le (Nat.cast_lt.mpr ht) (ENat.natCast_toNat_le_self _)

theorem measurable_pairShift (eps : ℝ) : Measurable (pairShift eps) :=
  measurable_shiftBy (isStoppingRule_pairSegLen eps)

/-- One layer of the hierarchy is a measurable map of pair sequence space. -/
theorem measurable_layerMap (eps : ℝ) : Measurable (layerMap eps) :=
  measurable_pi_lambda _ fun j =>
    (measurable_firstBlock eps).comp ((measurable_pairShift eps).iterate j)

theorem measurable_pairLayer (eps : ℝ) (ℓ : ℕ) : Measurable (pairLayer eps ℓ) :=
  (measurable_layerMap eps).iterate ℓ

/-! ## iid pair sequences and the pair filtration -/

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {Z : ℕ → Ω → ℝ × ℕ}

/-- An iid sequence of pairs. -/
structure IIDPairs (P : Measure Ω) (Z : ℕ → Ω → ℝ × ℕ) : Prop where
  measurable : ∀ t, Measurable (Z t)
  indep : iIndepFun Z P
  ident : ∀ t, IdentDistrib (Z t) (Z 0) P P

/-- The natural filtration of the pairs: `F t = σ(Z 0, …, Z (t - 1))`. -/
def pairFiltration (Z : ℕ → Ω → ℝ × ℕ) (hZ : ∀ t, Measurable (Z t)) : Filtration ℕ mΩ where
  seq t := ⨆ s ∈ Set.Iio t, MeasurableSpace.comap (Z s) inferInstance
  mono' := fun _ _ hst =>
    biSup_mono fun _ hs => lt_of_lt_of_le hs hst
  le' := fun _ => iSup₂_le fun s _ => (hZ s).comap_le

theorem pairFiltration_apply (hZ : ∀ t, Measurable (Z t)) (t : ℕ) :
    pairFiltration Z hZ t = ⨆ s ∈ Set.Iio t, MeasurableSpace.comap (Z s) inferInstance :=
  rfl

theorem pairFiltration_measurable_lt (hZ : ∀ t, Measurable (Z t)) {s t : ℕ} (hst : s < t) :
    Measurable[pairFiltration Z hZ t] (Z s) :=
  (comap_measurable (Z s)).mono (le_iSup₂ (f := fun s (_ : s ∈ Set.Iio t) =>
    MeasurableSpace.comap (Z s) inferInstance) s hst) le_rfl

/-- The gap filtration of the first components is coarser than the pair filtration. -/
theorem gapFiltration_fst_le (hZ : ∀ t, Measurable (Z t)) (t : ℕ) :
    gapFiltration (fun s ω => (Z s ω).1) (fun s => (hZ s).fst) t ≤ pairFiltration Z hZ t :=
  iSup₂_le fun _ hs =>
    ((pairFiltration_measurable_lt hZ hs).fst).comap_le

/-- The first segment length is a stopping index for the pair filtration. -/
theorem pairSegLen_lt_measurable (hZ : ∀ t, Measurable (Z t)) (eps : ℝ) (t : ℕ) :
    MeasurableSet[pairFiltration Z hZ t] {ω | (t : ℕ∞) < pairSegLen eps (seq Z ω)} :=
  gapFiltration_fst_le hZ t _
    (gapSegLen_lt_measurable (X := fun s ω => (Z s ω).1) (fun s => (hZ s).fst) eps t)

namespace IIDPairs

/-- The gap components of an iid pair sequence are iid. -/
theorem fst (h : IIDPairs P Z) : IIDSeq P (fun t ω => (Z t ω).1) where
  measurable t := (h.measurable t).fst
  indep := h.indep.comp (fun _ => Prod.fst) (fun _ => measurable_fst)
  ident t := (h.ident t).comp measurable_fst

/-- A shifted iid pair sequence is iid. -/
theorem shift (h : IIDPairs P Z) (m : ℕ) : IIDPairs P (fun t => Z (m + t)) where
  measurable t := h.measurable (m + t)
  indep := h.indep.precomp (g := fun t => m + t) fun _ _ hij => by simpa using hij
  ident t := (h.ident (m + t)).trans (h.ident m).symm

/-- Centred measurable functionals of the pairs have independent increments for the
pair filtration. -/
theorem indepIncrements (h : IIDPairs P Z) (f : ℝ × ℕ → ℝ) (hf : Measurable f) (c : ℝ) :
    IndepIncrements P (pairFiltration Z h.measurable) (fun t ω => f (Z t ω) - c) where
  measurable t :=
    (hf.comp (pairFiltration_measurable_lt h.measurable (Nat.lt_succ_self t))).sub_const c
  indep t := by
    have hd : Disjoint ({t} : Set ℕ) (Set.Iio t) := by simp
    have hind := indep_iSup_of_disjoint (fun k => (h.measurable k).comap_le) h.indep.iIndep hd
    simp only [Set.mem_singleton_iff, iSup_iSup_eq_left] at hind
    exact indep_of_indep_of_le_left hind
      ((hf.comp (comap_measurable (Z t))).sub_const c).comap_le

end IIDPairs

/-! ## Independence of the future from the pair filtration -/

/-- The future `(Z m, Z (m + 1), …)` is independent of the pair filtration at `m`. -/
theorem indep_future_pairFiltration (h : IIDPairs P Z) (m : ℕ) :
    Indep (MeasurableSpace.comap (fun ω t => Z (m + t) ω) inferInstance)
      (pairFiltration Z h.measurable m) P := by
  have hd : Disjoint (Set.Ici m) (Set.Iio m) := by
    apply Set.disjoint_left.mpr
    intro i h1 h2
    simp only [Set.mem_Ici, Set.mem_Iio] at h1 h2
    omega
  have hind := indep_iSup_of_disjoint (fun k => (h.measurable k).comap_le) h.indep.iIndep hd
  have h1 : MeasurableSpace.comap (fun ω (t : ℕ) => Z (m + t) ω) inferInstance ≤
      ⨆ i ∈ Set.Ici m, MeasurableSpace.comap (Z i) inferInstance := by
    rw [MeasurableSpace.comap_process_pi]
    exact iSup_le fun j => le_iSup_of_le (m + j) (le_iSup_of_le (by simp) le_rfl)
  exact indep_of_indep_of_le_left hind h1

/-- Event form of `indep_future_pairFiltration`. -/
theorem measure_future_inter_pairFiltration (h : IIDPairs P Z) (m : ℕ)
    {A : Set (ℕ → ℝ × ℕ)} (hA : MeasurableSet A)
    {B : Set Ω} (hB : MeasurableSet[pairFiltration Z h.measurable m] B) :
    P ((fun ω t => Z (m + t) ω) ⁻¹' A ∩ B) = P ((fun ω t => Z (m + t) ω) ⁻¹' A) * P B :=
  (Indep_iff _ _ P).mp (indep_future_pairFiltration h m) _ _ ⟨A, hA, rfl⟩ hB

/-! ## Layer regeneration -/

/-- Almost surely every segment of an iid pair sequence is finite, once the first one is. -/
theorem ae_allSegmentsFinite [IsProbabilityMeasure P] (h : IIDPairs P Z) (eps : ℝ)
    (hfin : ∀ᵐ ω ∂P, pairSegLen eps (seq Z ω) ≠ ⊤) :
    ∀ᵐ ω ∂P, AllSegmentsFinite eps (seq Z ω) :=
  ae_all_iff.mpr fun j =>
    ae_iterate_ne_top h.measurable h.indep h.ident (isStoppingRule_pairSegLen eps) hfin j

/-- **Layer regeneration.**  If the first segment is almost surely finite, the next layer
of an iid pair sequence is again an iid pair sequence. -/
theorem IIDPairs.layerMap [IsProbabilityMeasure P] (h : IIDPairs P Z) (eps : ℝ)
    (hfin : ∀ᵐ ω ∂P, pairSegLen eps (seq Z ω) ≠ ⊤) :
    IIDPairs P (fun j ω => PGM.layerMap eps (seq Z ω) j) where
  measurable j :=
    (measurable_pi_apply j).comp ((measurable_layerMap eps).comp (measurable_seq h.measurable))
  indep :=
    iIndepFun_rewards h.measurable h.indep h.ident (isStoppingRule_pairSegLen eps) hfin
      (measurable_firstBlock eps) fun _ _ => firstBlock_stopped eps
  ident j :=
    identDistrib_rewards h.measurable h.indep h.ident (isStoppingRule_pairSegLen eps) hfin
      (measurable_firstBlock eps) j

/-- The pairs of the next layer have the law of the first block. -/
theorem identDistrib_layerMap_zero (h : IIDPairs P Z) (eps : ℝ) :
    IdentDistrib (fun ω => PGM.layerMap eps (seq Z ω) 0) (fun ω => firstBlock eps (seq Z ω))
      P P :=
  IdentDistrib.refl ((measurable_firstBlock eps).comp (measurable_seq h.measurable)).aemeasurable

/-- Iterated layer regeneration: if the first segment of every layer is almost surely
finite, every layer is an iid pair sequence. -/
theorem IIDPairs.pairLayer [IsProbabilityMeasure P] (h : IIDPairs P Z) (eps : ℝ)
    (hfin : ∀ ℓ, ∀ᵐ ω ∂P, pairSegLen eps (PGM.pairLayer eps ℓ (seq Z ω)) ≠ ⊤) :
    ∀ ℓ, IIDPairs P (fun j ω => PGM.pairLayer eps ℓ (seq Z ω) j)
  | 0 => h
  | ℓ + 1 => by
    have e : (fun j ω => PGM.pairLayer eps (ℓ + 1) (seq Z ω) j) =
        fun j ω => PGM.layerMap eps (seq (fun j ω => PGM.pairLayer eps ℓ (seq Z ω) j) ω) j := by
      funext j ω
      rw [pairLayer_succ]
      rfl
    rw [e]
    exact (h.pairLayer eps hfin ℓ).layerMap eps (hfin ℓ)

/-- If the first segment of every layer is almost surely finite, then almost surely all
segments of all layers are finite. -/
theorem ae_allLayersFinite [IsProbabilityMeasure P] (h : IIDPairs P Z) (eps : ℝ)
    (hfin : ∀ ℓ, ∀ᵐ ω ∂P, pairSegLen eps (PGM.pairLayer eps ℓ (seq Z ω)) ≠ ⊤) :
    ∀ᵐ ω ∂P, AllLayersFinite eps (seq Z ω) :=
  ae_all_iff.mpr fun ℓ => ae_allSegmentsFinite (h.pairLayer eps hfin ℓ) eps (hfin ℓ)

end PGM
