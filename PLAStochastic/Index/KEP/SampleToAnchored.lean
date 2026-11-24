import PLAStochastic.Index.KEP.AnchoredSample
import PLAStochastic.Index.KEP.OrderStatisticReset
import PLAStochastic.Index.KEP.PivotRestart
import PLAStochastic.Index.ModelK.ConstantDensity
import PLAStochastic.Index.ModelK.Density
import PLAStochastic.ForMathlib.Probability.OrderStatistics.Renyi
import PLAStochastic.Index.Model.ExpSequence

/-!
# From the Model K sample to the anchored canonical model

Let `Q = quantK f A B` and let `X 0, X 1, …` be iid with the Model K law.  This file connects
the event `{ALG-PGM on the N sorted samples has height ≤ L}` to the anchored pair sequences
of `PLAStochastic.Index.KEP.AnchoredSample`.

* **Sorted sample law** (`identDistrib_sortVec_quantK_orderLaw`,
  `integral_epHeight_kKeys_eq_orderLaw`, `measure_epHeight_kKeys_le_eq_orderLaw`).  The sorted
  sample has the law of `Q ∘ v` with `v ∼ orderLaw N`.
* **Height via the anchored leading pivot** (`epHeight_le_iff_layerPivot_anchPairsW`).  For
  `v` in the simplex, the keys `Q ∘ v` are `Q (v 0)` plus the keys of
  `anchPairsW Q (v 0) (resc 0 v)`, so for `eps ≥ 1/2`, `L ≥ 1` the height is at most `L` iff
  the leading layer-`L` pivot of the anchored pairs is at least `N = 1 + M`.
* **Reset at the first key** (`orderLaw_anchPairsW_resc_mem`,
  `orderLaw_le_layerPivot_anchPairsW_resc`, `orderLaw_le_layerPivot_anchPairsW_resc_le_iSup`).
  The first key and the rescaled future are independent (`Renyi.map_pre_resc_orderLaw`), so
  the probability of an anchored event is an average over the anchor value, bounded by the
  supremum over anchor values in `[0, 1)`.
* **Canonical realisation** (`orderLaw_anchPairsW_mem_eq_expSeqMeasure`).  Under
  `expSeqMeasure`, `anchPairs Q u M` has the law of `anchPairsW Q u w` with `w ∼ orderLaw M`.
* **Lower-bound bridge** (`measure_epHeight_kKeys_le_le_iSup_anchPairs`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-! ## Keys of the anchored pair sequence -/

private theorem anchPos_zero {M : ℕ} (w : Fin M → ℝ) : anchPos w 0 = 0 := by
  simp [anchPos]

/-- The anchored keys telescope to `Q (u + (1-u) · anchPos w t) - Q u` for `t ≤ M`. -/
private theorem pairKeys_anchPairsW (Q : ℝ → ℝ) (u : ℝ) {M : ℕ} (w : Fin M → ℝ) :
    ∀ t ≤ M, pairKeys (anchPairsW Q u w) t = Q (u + (1 - u) * anchPos w t) - Q u
  | 0, _ => by simp [pairKeys, anchPos]
  | t + 1, ht => by
    have ih := pairKeys_anchPairsW Q u w t (by omega)
    simp only [pairKeys, Finset.sum_range_succ] at ih ⊢
    rw [ih]
    simp only [anchPairsW, if_pos (show t < M by omega)]
    ring

private theorem anchPairsW_fst_eq_zero (Q : ℝ → ℝ) (u : ℝ) {M : ℕ} (w : Fin M → ℝ) {t : ℕ}
    (ht : M ≤ t) : (anchPairsW Q u w t).1 = 0 := by
  simp [anchPairsW, not_lt.2 ht]

/-- On the simplex, the anchor `v 0` and the rescaled future `resc 0 v` recover `v`. -/
private theorem add_mul_anchPos_resc {M : ℕ} {v : Fin (1 + M) → ℝ} (hv : v ∈ Renyi.simplex (1 + M))
    {t : ℕ} (ht : t < 1 + M) :
    v 0 + (1 - v 0) * anchPos (Renyi.resc 0 v) t = v ⟨t, ht⟩ := by
  rcases Nat.eq_zero_or_pos t with rfl | htpos
  · rw [anchPos_zero, mul_zero, add_zero]
    rfl
  · have h := Renyi.future_eq_pivot_add_of_mem (r := 0) hv ⟨t - 1, by omega⟩
    have hidx : (Fin.natAdd (0 + 1) (⟨t - 1, by omega⟩ : Fin M) : Fin (0 + 1 + M)) = ⟨t, ht⟩ := by
      ext
      simp only [Fin.val_natAdd]
      omega
    rw [hidx] at h
    rw [h, anchPos, dif_pos ⟨htpos, by omega⟩]
    rfl

/-- **Height via the anchored leading pivot.** -/
theorem epHeight_le_iff_layerPivot_anchPairsW {eps : ℝ} (heps : 1 / 2 ≤ eps) (Q : ℝ → ℝ)
    {M : ℕ} {v : Fin (1 + M) → ℝ} (hv : v ∈ Renyi.simplex (1 + M)) {L : ℕ} (hL : 1 ≤ L) :
    epHeight eps (extendKeys (Q ∘ v)) (1 + M) ≤ L ↔
      1 + M ≤ layerPivot eps (anchPairsW Q (v 0) (Renyi.resc 0 v)) L 1 := by
  set z := anchPairsW Q (v 0) (Renyi.resc 0 v) with hz
  have hkeys : ∀ t < 1 + M, extendKeys (Q ∘ v) t = Q (v 0) + pairKeys z t := by
    intro t ht
    rw [extendKeys_of_lt _ ht, hz, pairKeys_anchPairsW Q _ _ t (by omega),
      add_mul_anchPos_resc hv ht]
    simp
  rw [epHeight_congr hkeys]
  exact epHeight_le_iff_layerPivot heps (fun _ => rfl)
    (allLayersFinite_of_fst_eq_zero (M := M) fun t ht => anchPairsW_fst_eq_zero Q _ _ ht)
    (Q (v 0)) (by omega) hL

/-! ## The sorted sample -/

section Sample

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f : ℝ → ℝ} {A B fmin fmax Lf : ℝ}

theorem ae_orderLaw_mem_simplex (n : ℕ) : ∀ᵐ v ∂(Renyi.orderLaw n), v ∈ Renyi.simplex n :=
  Measure.ae_smul_measure (ae_restrict_mem Renyi.measurableSet_simplex) _

/-- The sorted Model K sample has the law of `quantK f A B ∘ v` for sorted uniforms `v`. -/
theorem identDistrib_sortVec_quantK_orderLaw (hf : DensityK f A B fmin fmax Lf) {n : ℕ}
    {X : Fin n → Ω → ℝ} (hX : ∀ i, HasLaw (X i) (densityLaw f A B) P) (hind : iIndepFun X P) :
    IdentDistrib (fun ω => Renyi.sortVec fun i => X i ω) (fun v => quantK f A B ∘ v) P
      (Renyi.orderLaw n) := by
  have hU := fun i => hasLaw_cdfK_comp hf (hX i)
  have hUind := iIndepFun_cdfK hf hX hind
  have h1 : IdentDistrib (fun ω => Renyi.sortVec fun i => cdfK f A (X i ω)) id P
      (Renyi.orderLaw n) :=
    { aemeasurable_fst := (Renyi.hasLaw_sortVec_uniform hU hUind).aemeasurable
      aemeasurable_snd := aemeasurable_id
      map_eq := by rw [Measure.map_id]; exact Renyi.map_sortVec_uniform_eq_orderLaw hU hUind }
  have h2 := h1.comp (measurable_comp_quantK hf)
  have h3 := IdentDistrib.of_ae_eq
    (Renyi.measurable_sortVec.comp_aemeasurable
      (aemeasurable_pi_lambda _ fun i => (hX i).aemeasurable))
    (sortVec_ae_eq_quantK_sortVec hf hX)
  exact h3.trans h2

/-- **Sorted sample law, expectation.** -/
theorem integral_epHeight_kKeys_eq_orderLaw (hf : DensityK f A B fmin fmax Lf)
    {X : ℕ → Ω → ℝ} (hX : ∀ i, HasLaw (X i) (densityLaw f A B) P) (hind : iIndepFun X P)
    (eps : ℝ) (N : ℕ) :
    ∫ ω, (epHeight eps (kKeys X N ω) N : ℝ) ∂P =
      ∫ v, (epHeight eps (extendKeys (quantK f A B ∘ v)) N : ℝ) ∂(Renyi.orderLaw N) := by
  have hid := identDistrib_sortVec_quantK_orderLaw hf (fun i : Fin N => hX i)
    (hind.precomp Fin.val_injective)
  have hu : Measurable fun v : Fin N → ℝ => (epHeight eps (extendKeys v) N : ℝ) :=
    measurable_from_nat.comp (measurable_epHeight_extendKeys eps N)
  exact (hid.comp hu).integral_eq

/-- **Sorted sample law, event form.** -/
theorem measure_epHeight_kKeys_le_eq_orderLaw (hf : DensityK f A B fmin fmax Lf)
    {X : ℕ → Ω → ℝ} (hX : ∀ i, HasLaw (X i) (densityLaw f A B) P) (hind : iIndepFun X P)
    (eps : ℝ) (N L : ℕ) :
    P {ω | epHeight eps (kKeys X N ω) N ≤ L} =
      Renyi.orderLaw N {v | epHeight eps (extendKeys (quantK f A B ∘ v)) N ≤ L} :=
  (identDistrib_sortVec_quantK_orderLaw hf (fun i : Fin N => hX i)
    (hind.precomp Fin.val_injective)).measure_mem_eq
    (s := {v : Fin N → ℝ | epHeight eps (extendKeys v) N ≤ L})
    (measurable_epHeight_extendKeys eps N measurableSet_Iic)

end Sample

/-! ## Measurability of the anchored pairs -/

section Measurability

private theorem measurable_anchPos {M : ℕ} (t : ℕ) :
    Measurable fun w : Fin M → ℝ => anchPos w t := by
  by_cases h : 1 ≤ t ∧ t ≤ M
  · simp only [anchPos, dif_pos h]
    exact measurable_pi_apply _
  · simp only [anchPos, dif_neg h]
    exact measurable_const

/-- `anchPairsW Q u w` is jointly measurable in the anchor value `u` and the positions `w`. -/
theorem measurable_anchPairsW_uncurry {Q : ℝ → ℝ} (hQ : Measurable Q) {M : ℕ} :
    Measurable fun q : ℝ × (Fin M → ℝ) => anchPairsW Q q.1 q.2 := by
  refine measurable_pi_lambda _ fun t => Measurable.prodMk ?_ measurable_const
  have hpos : ∀ s, Measurable fun q : ℝ × (Fin M → ℝ) => q.1 + (1 - q.1) * anchPos q.2 s :=
    fun s => measurable_fst.add ((measurable_const.sub measurable_fst).mul
      ((measurable_anchPos s).comp measurable_snd))
  by_cases ht : t < M
  · simp only [if_pos ht]
    exact (hQ.comp (hpos (t + 1))).sub (hQ.comp (hpos t))
  · simp only [if_neg ht]
    exact measurable_const

theorem measurable_anchPairsW {Q : ℝ → ℝ} (hQ : Measurable Q) (u : ℝ) {M : ℕ} :
    Measurable (anchPairsW Q u (M := M)) :=
  (measurable_anchPairsW_uncurry hQ).comp (measurable_const.prodMk measurable_id)

theorem measurableSet_le_layerPivot (eps : ℝ) (n L j : ℕ) :
    MeasurableSet {p : ℕ → ℝ × ℕ | n ≤ layerPivot eps p L j} :=
  measurable_layerPivot eps L j measurableSet_Ici

end Measurability

/-! ## Reset at the first key -/

section Reset

theorem ae_preLaw_mem_simplex {M : ℕ} :
    ∀ᵐ p ∂(Renyi.preLaw 0 M), p ∈ Renyi.simplex (0 + 1) := by
  rw [Renyi.preLaw]
  refine (ae_map_iff (p := fun p => p ∈ Renyi.simplex (0 + 1)) Renyi.measurable_pre.aemeasurable
    Renyi.measurableSet_simplex).2 ?_
  filter_upwards [ae_orderLaw_mem_simplex (0 + 1 + M)] with v hv using Renyi.pre_mem_simplex hv

/-- A functional of the first key, integrated against its law, is bounded by its supremum over
anchor values in `[0, 1)`. -/
theorem lintegral_preLaw_le_iSup {M : ℕ} (g : ℝ → ℝ≥0∞) :
    ∫⁻ p, g (p 0) ∂(Renyi.preLaw 0 M) ≤ ⨆ u ∈ Ico (0 : ℝ) 1, g u := by
  calc ∫⁻ p, g (p 0) ∂(Renyi.preLaw 0 M)
      ≤ ∫⁻ _, (⨆ u ∈ Ico (0 : ℝ) 1, g u) ∂(Renyi.preLaw 0 M) :=
        lintegral_mono_ae (ae_preLaw_mem_simplex.mono fun p hp =>
          le_iSup₂ (f := fun u (_ : u ∈ Ico (0 : ℝ) 1) => g u) (p 0) ⟨(hp.2.1 0).le, hp.2.2 0⟩)
    _ = ⨆ u ∈ Ico (0 : ℝ) 1, g u := by rw [lintegral_const, measure_univ, mul_one]

/-- **Reset at the first key**, for any measurable event of the anchored pairs. -/
theorem orderLaw_anchPairsW_resc_mem {Q : ℝ → ℝ} (hQ : Measurable Q) {M : ℕ}
    {E : Set (ℕ → ℝ × ℕ)} (hE : MeasurableSet E) :
    Renyi.orderLaw (1 + M) {v | anchPairsW Q (v 0) (Renyi.resc 0 v) ∈ E} =
      ∫⁻ p, Renyi.orderLaw M {w | anchPairsW Q (p 0) w ∈ E} ∂(Renyi.preLaw 0 M) := by
  set S : Set ((Fin (0 + 1) → ℝ) × (Fin M → ℝ)) := {q | anchPairsW Q (q.1 0) q.2 ∈ E} with hS
  have hSm : MeasurableSet S :=
    ((measurable_anchPairsW_uncurry hQ).comp
      (f := fun q : (Fin (0 + 1) → ℝ) × (Fin M → ℝ) => (q.1 0, q.2))
      (((measurable_pi_apply 0).comp measurable_fst).prodMk measurable_snd)) hE
  have hmap : (Renyi.orderLaw (1 + M)).map (fun v => (Renyi.pre 0 v, Renyi.resc 0 v)) =
      (Renyi.preLaw 0 M).prod (Renyi.orderLaw M) := Renyi.map_pre_resc_orderLaw
  have hset : {v : Fin (1 + M) → ℝ | anchPairsW Q (v 0) (Renyi.resc 0 v) ∈ E} =
      (fun v => (Renyi.pre 0 v, Renyi.resc 0 v)) ⁻¹' S := rfl
  rw [hset, ← Measure.map_apply Renyi.measurable_pre_resc hSm, hmap, Measure.prod_apply hSm]
  rfl

/-- **Reset at the first key**, pivot form. -/
theorem orderLaw_le_layerPivot_anchPairsW_resc {Q : ℝ → ℝ} (hQ : Measurable Q) (eps : ℝ)
    (M n L : ℕ) :
    Renyi.orderLaw (1 + M) {v | n ≤ layerPivot eps (anchPairsW Q (v 0) (Renyi.resc 0 v)) L 1} =
      ∫⁻ p, Renyi.orderLaw M {w | n ≤ layerPivot eps (anchPairsW Q (p 0) w) L 1}
        ∂(Renyi.preLaw 0 M) :=
  orderLaw_anchPairsW_resc_mem hQ (measurableSet_le_layerPivot eps n L 1)

/-- **Reset at the first key**, supremum over the anchor value. -/
theorem orderLaw_le_layerPivot_anchPairsW_resc_le_iSup {Q : ℝ → ℝ} (hQ : Measurable Q)
    (eps : ℝ) (M n L : ℕ) :
    Renyi.orderLaw (1 + M) {v | n ≤ layerPivot eps (anchPairsW Q (v 0) (Renyi.resc 0 v)) L 1} ≤
      ⨆ u ∈ Ico (0 : ℝ) 1, Renyi.orderLaw M {w | n ≤ layerPivot eps (anchPairsW Q u w) L 1} := by
  rw [orderLaw_le_layerPivot_anchPairsW_resc hQ eps M n L]
  exact lintegral_preLaw_le_iSup fun u =>
    Renyi.orderLaw M {w | n ≤ layerPivot eps (anchPairsW Q u w) L 1}

end Reset

/-! ## The canonical realisation -/

section Canonical

/-- The Rényi ratios of the first `M + 1` canonical coordinates are sorted uniforms. -/
theorem hasLaw_gammaRatio_expSeq (M : ℕ) :
    HasLaw (fun ω : ℕ → ℝ => Renyi.gammaRatio fun i : Fin (M + 1) => ω i) (Renyi.orderLaw M)
      expSeqMeasure :=
  Renyi.hasLaw_gammaRatio_exp (E := fun i : Fin (M + 1) => expCoord i)
    (fun i => hasLaw_expCoord i) (iidSeq_expCoord.indep.precomp Fin.val_injective)

/-- **Canonical realisation.** -/
theorem orderLaw_anchPairsW_mem_eq_expSeqMeasure {Q : ℝ → ℝ} (hQ : Measurable Q) (u : ℝ)
    (M : ℕ) {E : Set (ℕ → ℝ × ℕ)} (hE : MeasurableSet E) :
    Renyi.orderLaw M {w | anchPairsW Q u w ∈ E} = expSeqMeasure {ω | anchPairs Q u M ω ∈ E} := by
  have h := hasLaw_gammaRatio_expSeq M
  rw [← h.map_eq, Measure.map_apply_of_aemeasurable h.aemeasurable
    (s := {w | anchPairsW Q u w ∈ E}) (measurable_anchPairsW hQ u hE)]
  rfl

end Canonical

/-! ## The lower-bound bridge -/

section Bridge

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f : ℝ → ℝ} {A B fmin fmax Lf : ℝ}

/-- **Lower-bound bridge.**  The probability that ALG-PGM on `N` sorted Model K samples has
height at most `L` is at most the supremum over anchor values `u ∈ [0, 1)` of the probability
that the anchored canonical model with `N - 1` further keys has leading layer-`L` pivot at
least `N`. -/
theorem measure_epHeight_kKeys_le_le_iSup_anchPairs (hf : DensityK f A B fmin fmax Lf)
    {X : ℕ → Ω → ℝ} (hX : ∀ i, HasLaw (X i) (densityLaw f A B) P) (hind : iIndepFun X P)
    {eps : ℝ} (heps : 1 / 2 ≤ eps) {N L : ℕ} (hN : 1 ≤ N) (hL : 1 ≤ L) :
    P {ω | epHeight eps (kKeys X N ω) N ≤ L} ≤
      ⨆ u ∈ Ico (0 : ℝ) 1,
        expSeqMeasure {ω | N ≤ layerPivot eps (anchPairs (quantK f A B) u (N - 1) ω) L 1} := by
  obtain ⟨M, rfl⟩ : ∃ M, N = 1 + M := ⟨N - 1, by omega⟩
  rw [Nat.add_sub_cancel_left, measure_epHeight_kKeys_le_eq_orderLaw hf hX hind]
  have hae : {v : Fin (1 + M) → ℝ | epHeight eps (extendKeys (quantK f A B ∘ v)) (1 + M) ≤ L}
      =ᵐ[Renyi.orderLaw (1 + M)]
      {v | 1 + M ≤ layerPivot eps (anchPairsW (quantK f A B) (v 0) (Renyi.resc 0 v)) L 1} := by
    refine Filter.eventuallyEq_set.2 ?_
    filter_upwards [ae_orderLaw_mem_simplex (1 + M)] with v hv
    exact epHeight_le_iff_layerPivot_anchPairsW heps _ hv hL
  rw [measure_congr hae]
  refine (orderLaw_le_layerPivot_anchPairsW_resc_le_iSup (measurable_quantK hf) eps M
    (1 + M) L).trans (iSup₂_mono fun u _ => ?_)
  exact (orderLaw_anchPairsW_mem_eq_expSeqMeasure (measurable_quantK hf) u M
    (measurableSet_le_layerPivot eps (1 + M) L 1)).le

end Bridge

end

end PGM
