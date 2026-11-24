import PLAStochastic.Index.GEP.Shadow.EndpointBridge
import PLAStochastic.Index.GEP.Shadow.Synchronization

/-!
# Joint regeneration of the actual exponential-mark shadow

The input triples are iid under the independent product construction. Their
stopped blocks regenerate jointly, so every actual triple layer and every
normalized active/passive layer is iid. The stopping finiteness used here is
obtained from the existing actual gap hierarchy bounds.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Set

variable {Ω E F : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace F]
variable {P : Measure Ω} {W : ℕ → Ω → E}

theorem IIDSeqE.comp (h : IIDSeqE P W) (f : E → F) (hf : Measurable f) :
    IIDSeqE P (fun t ω => f (W t ω)) where
  measurable t := hf.comp (h.measurable t)
  indep := h.indep.comp (fun _ => f) (fun _ => hf)
  ident t := (h.ident t).comp hf

/-- Two iid sequences on independent spaces give an iid sequence of pairs. -/
theorem IIDSeqE.prod {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {Y : ℕ → Ω' → F}
    (hW : IIDSeqE P W) (hY : IIDSeqE Q Y) :
    IIDSeqE (P.prod Q) (fun t p => (W t p.1, Y t p.2)) := by
  have hm (t : ℕ) : Measurable (fun p : Ω × Ω' => (W t p.1, Y t p.2)) :=
    ((hW.measurable t).comp measurable_fst).prodMk
      ((hY.measurable t).comp measurable_snd)
  have hmap (t : ℕ) : (P.prod Q).map (fun p => (W t p.1, Y t p.2)) =
      (P.map (W t)).prod (Q.map (Y t)) :=
    (Measure.map_prod_map P Q (hW.measurable t) (hY.measurable t)).symm
  refine ⟨hm, ?_, fun t => ?_⟩
  · apply iIndepFun_iff_finset.mpr
    intro s
    apply (iIndepFun_iff_map_fun_eq_pi_map (fun i : s => (hm i).aemeasurable)).mpr
    change (P.prod Q).map (fun p (i : s) => (W i p.1, Y i p.2)) = _
    simp_rw [hmap]
    let e := MeasurableEquiv.arrowProdEquivProdArrow E F s
    have (t : ℕ) : IsProbabilityMeasure (P.map (W t)) :=
      Measure.isProbabilityMeasure_map (hW.measurable t).aemeasurable
    have (t : ℕ) : IsProbabilityMeasure (Q.map (Y t)) :=
      Measure.isProbabilityMeasure_map (hY.measurable t).aemeasurable
    apply e.map_measurableEquiv_injective
    rw [(measurePreserving_arrowProdEquivProdArrow E F s
      (fun i => P.map (W i)) (fun i => Q.map (Y i))).map_eq]
    rw [Measure.map_map e.measurable (measurable_pi_lambda _ fun i => hm i)]
    change (P.prod Q).map (Prod.map (fun ω (i : s) => W i ω) (fun ω (i : s) => Y i ω)) = _
    rw [← Measure.map_prod_map P Q (measurable_pi_lambda _ fun i : s => hW.measurable i)
      (measurable_pi_lambda _ fun i : s => hY.measurable i)]
    rw [(hW.indep.restrict s).map_fun_eq_pi_map (fun i : s => (hW.measurable i).aemeasurable),
      (hY.indep.restrict s).map_fun_eq_pi_map (fun i : s => (hY.measurable i).aemeasurable)]
  · exact ⟨(hm t).aemeasurable, (hm 0).aemeasurable,
      by rw [hmap, hmap, (hW.ident t).map_eq, (hY.ident t).map_eq]⟩

theorem iidSeqE_shInput [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} (hg : IIDSeq P g) :
    IIDSeqE (shP P) (shInput g) := by
  have hX : IIDSeqE P g := ⟨hg.measurable, hg.indep, hg.ident⟩
  have hY : IIDSeqE expSeqMeasure expCoord :=
    ⟨iidSeq_expCoord.measurable, iidSeq_expCoord.indep, iidSeq_expCoord.ident⟩
  exact (hX.prod hY).comp (fun p : ℝ × ℝ => ((p.1, (1 : ℕ)), p.2))
    ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)

/-! ## Regeneration of stopped triples -/

theorem triBlock_stopped (eps : ℝ) {w w' : ℕ → Tri}
    (hτ : triSegLen eps w = triSegLen eps w')
    (h : ∀ t : ℕ, (t : ℕ∞) < triSegLen eps w → w t = w' t) :
    triBlock eps w = triBlock eps w' := by
  unfold triBlock
  rw [← hτ]
  refine Finset.sum_congr rfl fun t ht => h t ?_
  rw [Finset.mem_range] at ht
  exact lt_of_lt_of_le (Nat.cast_lt.mpr ht) (ENat.natCast_toNat_le_self _)

theorem IIDSeqE.triLayerMap [IsProbabilityMeasure P] {Z : ℕ → Ω → Tri}
    (h : IIDSeqE P Z) (eps : ℝ)
    (hfin : ∀ᵐ ω ∂P, triSegLen eps (seq Z ω) ≠ ⊤) :
    IIDSeqE P (fun j ω => PGM.triLayerMap eps (seq Z ω) j) where
  measurable j := (measurable_pi_apply j).comp
    ((measurable_triLayerMap eps).comp (measurable_seq h.measurable))
  indep := iIndepFun_rewards h.measurable h.indep h.ident (isStoppingRule_triSegLen eps)
    hfin (measurable_triBlock eps) fun _ _ => triBlock_stopped eps
  ident j := identDistrib_rewards h.measurable h.indep h.ident (isStoppingRule_triSegLen eps)
    hfin (measurable_triBlock eps) j

theorem IIDSeqE.triLayer [IsProbabilityMeasure P] {Z : ℕ → Ω → Tri}
    (h : IIDSeqE P Z) (eps : ℝ)
    (hfin : ∀ ℓ, ∀ᵐ ω ∂P, triSegLen eps (PGM.triLayer eps ℓ (seq Z ω)) ≠ ⊤) :
    ∀ ℓ, IIDSeqE P (fun j ω => PGM.triLayer eps ℓ (seq Z ω) j)
  | 0 => h
  | ℓ + 1 => by
    have heq : (fun j ω => PGM.triLayer eps (ℓ + 1) (seq Z ω) j) =
        fun j ω => PGM.triLayerMap eps
          (seq (fun i ω => PGM.triLayer eps ℓ (seq Z ω) i) ω) j := by
      funext j ω
      exact congrFun (Function.iterate_succ_apply' (PGM.triLayerMap eps) ℓ (seq Z ω)) j
    rw [heq]
    exact (h.triLayer eps hfin ℓ).triLayerMap eps (hfin ℓ)

/-! ## Joint iid laws of the actual shadow layers -/

variable [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} {μ₀ σ₀ κ₀ eps : ℝ}

theorem iidSeqE_shTri (hg : GapLaw P g μ₀ σ₀ κ₀)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (ℓ : ℕ) :
    IIDSeqE (shP P) (shTri eps g ℓ) := by
  have hall := layerOK_all (layerOK_input hg) (bAbs_le_bIn μ₀ σ₀) (βAbs_le_βIn _ _)
    (vIn_pos hg.mu_pos hg.sigma_pos) (vIn_le μ₀ σ₀) KcAbs_le_KcIn heps
  have hfin (k : ℕ) : ∀ᵐ p ∂shP P,
      triSegLen eps (triLayer eps k (seq (shInput g) p)) ≠ ⊤ := by
    have hp := (measurePreserving_fst : MeasurePreserving Prod.fst (shP P) P).quasiMeasurePreserving.ae
      (hall k).2.1
    filter_upwards [hp] with p hp
    change pairSegLen eps (fun t => (shTri eps g k t p).1) ≠ ⊤
    change pairSegLen eps (fun t => epLayerSeq eps g k t p.1) ≠ ⊤ at hp
    simpa only [shTri_fst_eq_actual] using hp
  exact (iidSeqE_shInput hg.iid).triLayer eps hfin ℓ

theorem iidSeqE_shPair (hg : GapLaw P g μ₀ σ₀ κ₀)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (ℓ : ℕ) :
    IIDSeqE (shP P) (shPair P eps g ℓ) :=
  (iidSeqE_shTri hg heps ℓ).comp
    (fun t : Tri => (t.1.1 / shMean P eps g ℓ, t.2 / shCount P eps g ℓ))
    ((measurable_fst.fst.div_const _).prodMk (measurable_snd.div_const _))

theorem shMean_pos (hg : GapLaw P g μ₀ σ₀ κ₀)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (ℓ : ℕ) :
    0 < shMean P eps g ℓ := by
  rw [shMean_eq]
  exact (layerOK_all (layerOK_input hg) (bAbs_le_bIn μ₀ σ₀) (βAbs_le_βIn _ _)
    (vIn_pos hg.mu_pos hg.sigma_pos) (vIn_le μ₀ σ₀) KcAbs_le_KcIn heps ℓ).1.law.mu_pos

theorem shCount_pos (hg : GapLaw P g μ₀ σ₀ κ₀)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (ℓ : ℕ) :
    0 < shCount P eps g ℓ := by
  rw [shCount_eq]
  exact (layerOK_all (layerOK_input hg) (bAbs_le_bIn μ₀ σ₀) (βAbs_le_βIn _ _)
    (vIn_pos hg.mu_pos hg.sigma_pos) (vIn_le μ₀ σ₀) KcAbs_le_KcIn heps ℓ).1.cnt_pos

/-! ## The active stopping mean and normalization recursion -/

omit [IsProbabilityMeasure P] in
theorem actLen_shPair_eq (eps : ℝ) (g : ℕ → Ω → ℝ) (ℓ : ℕ)
    (hμ : shMean P eps g ℓ ≠ 0) (p : Ω × (ℕ → ℝ)) :
    actLen eps (shPair P eps g ℓ) p = pairSegLen eps (seq (epLayerSeq eps g ℓ) p.1) := by
  simp only [actLen, shPair, shTri_fst_eq_actual, div_eq_inv_mul]
  rw [gapSegLen_const_mul eps _ (inv_ne_zero hμ)]
  rfl

theorem actMean_shPair_eq_segMean (hg : GapLaw P g μ₀ σ₀ κ₀)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (ℓ : ℕ) :
    actMean eps (shP P) (shPair P eps g ℓ) = segMean P eps (epLayerSeq eps g ℓ) := by
  simp only [actMean, actLen_shPair_eq eps g ℓ (shMean_pos hg heps ℓ).ne', shP, segMean]
  rw [integral_fun_fst (fun ω => ((pairSegLen eps (seq (epLayerSeq eps g ℓ) ω)).toNat : ℝ))]
  simp

theorem actMean_shPair_pos (hg : GapLaw P g μ₀ σ₀ κ₀)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (ℓ : ℕ) :
    0 < actMean eps (shP P) (shPair P eps g ℓ) := by
  rw [actMean_shPair_eq_segMean hg heps]
  have hε : 0 < eps := lt_of_lt_of_le zero_lt_one ((one_le_epsZero _ _).trans heps)
  have hb : 0 < bIn μ₀ σ₀ := bAbs_pos.trans_le (bAbs_le_bIn μ₀ σ₀)
  exact lt_of_lt_of_le (by positivity)
    (layerOK_all (layerOK_input hg) (bAbs_le_bIn μ₀ σ₀) (βAbs_le_βIn _ _)
      (vIn_pos hg.mu_pos hg.sigma_pos) (vIn_le μ₀ σ₀) KcAbs_le_KcIn heps ℓ).2.2.2.1

theorem ae_actLen_shPair_ne_top (hg : GapLaw P g μ₀ σ₀ κ₀)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (ℓ : ℕ) :
    ∀ᵐ p ∂shP P, actLen eps (shPair P eps g ℓ) p ≠ ⊤ := by
  have hfin := (layerOK_all (layerOK_input hg) (bAbs_le_bIn μ₀ σ₀) (βAbs_le_βIn _ _)
    (vIn_pos hg.mu_pos hg.sigma_pos) (vIn_le μ₀ σ₀) KcAbs_le_KcIn heps ℓ).2.1
  have hp := (measurePreserving_fst : MeasurePreserving Prod.fst (shP P) P).quasiMeasurePreserving.ae
    hfin
  filter_upwards [hp] with p hp
  rwa [actLen_shPair_eq eps g ℓ (shMean_pos hg heps ℓ).ne']

theorem integrable_actLen_shPair (hg : GapLaw P g μ₀ σ₀ κ₀)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (ℓ : ℕ) :
    Integrable (fun p => ((actLen eps (shPair P eps g ℓ) p).toNat : ℝ)) (shP P) := by
  by_contra h
  exact (actMean_shPair_pos hg heps ℓ).ne' (integral_undef h)

theorem shCount_succ (hg : GapLaw P g μ₀ σ₀ κ₀)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (ℓ : ℕ) :
    shCount P eps g (ℓ + 1) = shCount P eps g ℓ * actMean eps (shP P) (shPair P eps g ℓ) := by
  rw [shCount_eq, shCount_eq, actMean_shPair_eq_segMean hg heps]
  exact (layerOK_all (layerOK_input hg) (bAbs_le_bIn μ₀ σ₀) (βAbs_le_βIn _ _)
    (vIn_pos hg.mu_pos hg.sigma_pos) (vIn_le μ₀ σ₀) KcAbs_le_KcIn heps ℓ).2.2.1

theorem shMean_succ (hg : GapLaw P g μ₀ σ₀ κ₀)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (ℓ : ℕ) :
    shMean P eps g (ℓ + 1) = shMean P eps g ℓ * actMean eps (shP P) (shPair P eps g ℓ) := by
  rw [shMean_eq, shMean_eq, actMean_shPair_eq_segMean hg heps]
  have hL := (layerOK_all (layerOK_input hg) (bAbs_le_bIn μ₀ σ₀) (βAbs_le_βIn _ _)
    (vIn_pos hg.mu_pos hg.sigma_pos) (vIn_le μ₀ σ₀) KcAbs_le_KcIn heps ℓ)
  have hC : 0 < segMean P eps (epLayerSeq eps g ℓ) := by
    rw [← actMean_shPair_eq_segMean hg heps]
    exact actMean_shPair_pos hg heps ℓ
  have hT : Integrable (fun ω => ((pairSegLen eps (seq (epLayerSeq eps g ℓ) ω)).toNat : ℝ)) P := by
    by_contra h
    exact hC.ne' (integral_undef h)
  change (∫ ω, (((nextLayer eps)^[ℓ + 1] (inputPairs g)) 0 ω).1 ∂P) = _
  rw [Function.iterate_succ_apply']
  exact integral_nextGap hL.1.iid hL.1.law hL.2.1 hT rfl

omit [MeasurableSpace Ω] in
theorem shTri_succ_zero (eps : ℝ) (g : ℕ → Ω → ℝ) (ℓ : ℕ) (p : Ω × (ℕ → ℝ)) :
    shTri eps g (ℓ + 1) 0 p = triBlock eps (seq (shTri eps g ℓ) p) := by
  change (triLayerMap eps)^[ℓ + 1] (seq (shInput g) p) 0 = _
  rw [Function.iterate_succ_apply']
  rfl

/-- The actual normalized shadow advances by summing both coordinates along the
active tree and dividing by that tree's mean segment length. -/
theorem shPair_succ_zero (hg : GapLaw P g μ₀ σ₀ κ₀)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps)
    (ℓ : ℕ) (p : Ω × (ℕ → ℝ)) :
    shPair P eps g (ℓ + 1) 0 p =
      (stopSum eps (fun t => (shPair P eps g ℓ t p).1) /
        actMean eps (shP P) (shPair P eps g ℓ),
      actSum eps (shPair P eps g ℓ) p / actMean eps (shP P) (shPair P eps g ℓ)) := by
  have hτ : triSegLen eps (seq (shTri eps g ℓ) p) =
      actLen eps (shPair P eps g ℓ) p := by
    rw [actLen_shPair_eq eps g ℓ (shMean_pos hg heps ℓ).ne']
    simp only [triSegLen, seq, shTri_fst_eq_actual]
    rfl
  have hx : stopSum eps (fun t => (shPair P eps g ℓ t p).1) =
      (shTri eps g (ℓ + 1) 0 p).1.1 / shMean P eps g ℓ := by
    rw [shTri_succ_zero]
    simp only [triBlock, Prod.fst_sum, hτ, seq]
    change (∑ t ∈ range (actLen eps (shPair P eps g ℓ) p).toNat,
      (shTri eps g ℓ t p).1.1 / shMean P eps g ℓ) = _
    rw [sum_div]
  have hy : actSum eps (shPair P eps g ℓ) p =
      (shTri eps g (ℓ + 1) 0 p).2 / shCount P eps g ℓ := by
    rw [shTri_succ_zero]
    simp only [triBlock, Prod.snd_sum, hτ, seq]
    change (∑ t ∈ range (actLen eps (shPair P eps g ℓ) p).toNat,
      (shTri eps g ℓ t p).2 / shCount P eps g ℓ) = _
    rw [sum_div]
  rw [hx, hy]
  change (_, _) = (_, _)
  rw [shMean_succ hg heps, shCount_succ hg heps, div_div, div_div]

/-! ## The two stopped sums realize the laws in the tree-switch coupling -/

theorem iidSeq_shPair_snd (hg : GapLaw P g μ₀ σ₀ κ₀)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (ℓ : ℕ) :
    IIDSeq (shP P) (fun t p => (shPair P eps g ℓ t p).2) := by
  have h := (iidSeqE_shPair hg heps ℓ).comp Prod.snd measurable_snd
  exact ⟨h.measurable, h.indep, h.ident⟩

theorem pasMean_shPair_eq_lawC (hg : GapLaw P g μ₀ σ₀ κ₀)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (ℓ : ℕ) :
    pasMean eps (shP P) (shPair P eps g ℓ) =
      lawC eps (shLawPM P hg.iid.measurable eps ℓ) := by
  have hν : (shLawPM P hg.iid.measurable eps ℓ : Measure ℝ) =
      (shP P).map (fun p => (shPair P eps g ℓ 0 p).2 / 1) := by
    simp only [div_one]
    rfl
  exact integral_gapSegLen_eq_lawC (iidSeq_shPair_snd hg heps ℓ) eps one_ne_zero
    (shLawPM P hg.iid.measurable eps ℓ) hν

/-- Summing passive coordinates on the actual active tree gives the next shadow law. -/
theorem shLaw_active_sum (hg : GapLaw P g μ₀ σ₀ κ₀)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (ℓ : ℕ) :
    (shP P).map (fun p => actSum eps (shPair P eps g ℓ) p /
      actMean eps (shP P) (shPair P eps g ℓ)) = shLaw P eps g (ℓ + 1) := by
  apply Measure.map_congr
  exact Filter.Eventually.of_forall fun p => (congrArg Prod.snd (shPair_succ_zero hg heps ℓ p)).symm

/-- Summing passive coordinates on their own tree gives the one-step image of the
current shadow law. This is the other marginal of the tree-switch coupling. -/
theorem shLaw_passive_sum (hg : GapLaw P g μ₀ σ₀ κ₀)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (ℓ : ℕ) :
    (shP P).map (fun p => pasSum eps (shPair P eps g ℓ) p /
      pasMean eps (shP P) (shPair P eps g ℓ)) =
      (lawPhi eps (shLawPM P hg.iid.measurable eps ℓ) : Measure ℝ) := by
  have hY := iidSeq_shPair_snd hg heps ℓ
  have hmap := map_seq_eq_iidLaw hY (shLawPM P hg.iid.measurable eps ℓ) rfl
  change (shP P).map (fun p => stopSum eps (seq (fun t p => (shPair P eps g ℓ t p).2) p) /
    pasMean eps (shP P) (shPair P eps g ℓ)) = _
  rw [pasMean_shPair_eq_lawC hg heps]
  change _ = (iidLaw (shLawPM P hg.iid.measurable eps ℓ)).map _
  rw [← hmap, Measure.map_map ((measurable_stopSum eps).div_const _) (measurable_seq hY.measurable)]
  rfl

/-- The actual stopped-sum construction witnesses `W2Le` with the defined `shW`.
Square integrability of the tree-switch difference is explicit: this statement
does not use the zero assigned to a nonintegrable real integral. -/
theorem shW_coupling (hg : GapLaw P g μ₀ σ₀ κ₀)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (ℓ : ℕ)
    (hI : Integrable (fun p =>
      (actSum eps (shPair P eps g ℓ) p / actMean eps (shP P) (shPair P eps g ℓ) -
        pasSum eps (shPair P eps g ℓ) p / pasMean eps (shP P) (shPair P eps g ℓ)) ^ 2) (shP P)) :
    W2Le (shLawPM P hg.iid.measurable eps (ℓ + 1))
      (lawPhi eps (shLawPM P hg.iid.measurable eps ℓ)) (shW P eps g ℓ) := by
  let A := fun p => actSum eps (shPair P eps g ℓ) p /
    actMean eps (shP P) (shPair P eps g ℓ)
  let B := fun p => pasSum eps (shPair P eps g ℓ) p /
    pasMean eps (shP P) (shPair P eps g ℓ)
  have hA : Measurable A := by
    have hEq : A = fun p => (shPair P eps g (ℓ + 1) 0 p).2 :=
      funext fun p => (congrArg Prod.snd (shPair_succ_zero hg heps ℓ p)).symm
    rw [hEq]
    exact (measurable_shPair hg.iid.measurable P eps (ℓ + 1) 0).snd
  have hB : Measurable B :=
    ((measurable_stopSum eps).comp
      (measurable_seq (iidSeq_shPair_snd hg heps ℓ).measurable)).div_const _
  have hAB := hA.prodMk hB
  have hF : Measurable (fun p : ℝ × ℝ => (p.1 - p.2) ^ 2) :=
    (measurable_fst.sub measurable_snd).pow_const 2
  refine ⟨(shP P).map (fun p => (A p, B p)),
    Measure.isProbabilityMeasure_map hAB.aemeasurable, ?_, ?_, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst hAB]
    exact shLaw_active_sum hg heps ℓ
  · rw [Measure.map_map measurable_snd hAB]
    exact shLaw_passive_sum hg heps ℓ
  · exact (integrable_map_measure hF.aestronglyMeasurable hAB.aemeasurable).mpr hI
  · rw [integral_map hAB.aemeasurable hF.aestronglyMeasurable]
    exact (Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)).ge

/-! ## Positive counts and passive support -/

theorem ae_one_le_epLayerSeq_count (hg : GapLaw P g μ₀ σ₀ κ₀)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (ℓ j : ℕ) :
    ∀ᵐ ω ∂P, 1 ≤ (epLayerSeq eps g ℓ j ω).2 := by
  have hall := layerOK_all (layerOK_input hg) (bAbs_le_bIn μ₀ σ₀) (βAbs_le_βIn _ _)
    (vIn_pos hg.mu_pos hg.sigma_pos) (vIn_le μ₀ σ₀) KcAbs_le_KcIn heps
  have hfin : ∀ᵐ ω ∂P, AllLayersFinite eps (seq (inputPairs g) ω) := by
    refine ae_allLayersFinite (IIDPairs.inputPairs hg.iid) eps fun k => ?_
    simpa only [seq_epLayerSeq] using (hall k).2.1
  filter_upwards [hfin] with ω hω
  rw [epLayerSeq_eq]
  exact pairLayer_pos (zero_le_one.trans ((one_le_epsZero _ _).trans heps))
    hω (fun _ => le_rfl) ℓ j

theorem ae_pos_shTri_mark (hg : GapLaw P g μ₀ σ₀ κ₀)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (ℓ j : ℕ) :
    ∀ᵐ p ∂shP P, 0 < (shTri eps g ℓ j p).2 := by
  have hmarks : ∀ᵐ ξ ∂expSeqMeasure, ∀ t, 0 < ξ t :=
    ae_all_iff.mpr fun t => iidSeq_expCoord.ae_pos_of_expMeasure_one (hasLaw_expCoord 0) t
  have hM := (measurePreserving_snd : MeasurePreserving Prod.snd (shP P) expSeqMeasure).quasiMeasurePreserving.ae
    hmarks
  have hN := (measurePreserving_fst : MeasurePreserving Prod.fst (shP P) P).quasiMeasurePreserving.ae
    (ae_one_le_epLayerSeq_count hg heps ℓ j)
  filter_upwards [hM, hN] with p hM hN
  rw [shTri_mark_eq_sum_range]
  apply Finset.sum_pos'
  · intro t _
    exact (hM _).le
  · exact ⟨0, Finset.mem_range.mpr (by omega), hM _⟩

theorem ae_pos_shPair_snd (hg : GapLaw P g μ₀ σ₀ κ₀)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (ℓ j : ℕ) :
    ∀ᵐ p ∂shP P, 0 < (shPair P eps g ℓ j p).2 := by
  filter_upwards [ae_pos_shTri_mark hg heps ℓ j] with p hp
  exact div_pos hp (shCount_pos hg heps ℓ)

theorem shLaw_pos (hg : GapLaw P g μ₀ σ₀ κ₀)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (ℓ : ℕ) :
    shLaw P eps g ℓ (Iic 0) = 0 := by
  rw [shLaw, Measure.map_apply (measurable_shPair hg.iid.measurable P eps ℓ 0).snd measurableSet_Iic]
  simpa only [Set.preimage, Set.mem_Iic, Set.compl_ofPred, not_lt] using
    (ae_iff.1 (ae_pos_shPair_snd hg heps ℓ 0))

end

end PGM
