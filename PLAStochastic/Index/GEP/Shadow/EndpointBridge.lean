import PLAStochastic.Index.GEP.Shadow.Defs

/-!
# The exponential shadow follows the actual endpoint tree

The triple hierarchy projects exactly to the existing `(gap, count)` hierarchy.
Its passive mark is the sum over the corresponding interval of original input
ranks. These identities are deterministic and require no finiteness hypothesis:
they preserve the `ENat.toNat` convention of both hierarchies.

For every fixed gap sample and every block, integrating over the independent
Exp(1) marks gives `E mark = count` and `E (mark - count)^2 = count`, with both
integrands proved integrable. Product-space transfer preserves the input gap law
and all actual layer means/counts, and identifies the initial shadow law.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Set

/-! ## Projection to the actual tree -/

theorem triShift_fst (eps : ℝ) (w : ℕ → Tri) :
    (fun t => (triShift eps w t).1) = pairShift eps (fun t => (w t).1) := rfl

theorem triShift_iterate_fst (eps : ℝ) (w : ℕ → Tri) (j : ℕ) :
    (fun t => ((triShift eps)^[j] w t).1) =
      (pairShift eps)^[j] (fun t => (w t).1) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', triShift_fst, ih]

theorem triBlock_fst (eps : ℝ) (w : ℕ → Tri) :
    (triBlock eps w).1 = firstBlock eps (fun t => (w t).1) := by
  simp only [triBlock, firstBlock, Prod.fst_sum, triSegLen]

theorem triLayerMap_fst (eps : ℝ) (w : ℕ → Tri) :
    (fun j => (triLayerMap eps w j).1) = layerMap eps (fun t => (w t).1) := by
  funext j
  rw [triLayerMap, triBlock_fst, triShift_iterate_fst]
  rfl

theorem triLayer_fst (eps : ℝ) (ℓ : ℕ) (w : ℕ → Tri) :
    (fun j => (triLayer eps ℓ w j).1) = pairLayer eps ℓ (fun t => (w t).1) := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih =>
    change (fun j => ((triLayerMap eps)^[ℓ + 1] w j).1) = _
    rw [Function.iterate_succ_apply', triLayerMap_fst, pairLayer_succ]
    change layerMap eps (fun j => (triLayer eps ℓ w j).1) = _
    rw [ih]

theorem triShift_iterate (eps : ℝ) (w : ℕ → Tri) (j : ℕ) :
    (triShift eps)^[j] w =
      fun t => w (blockStart eps (fun s => (w s).1) j + t) := by
  induction j with
  | zero => funext t; simp [blockStart]
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    funext t
    change (triShift eps)^[j] w
      ((pairSegLen eps (fun s => ((triShift eps)^[j] w s).1)).toNat + t) = _
    rw [triShift_iterate_fst, ih, blockStart_succ, Nat.add_assoc]

theorem triLayerMap_apply (eps : ℝ) (w : ℕ → Tri) (j : ℕ) :
    triLayerMap eps w j =
      ∑ t ∈ Ico (blockStart eps (fun s => (w s).1) j)
        (blockStart eps (fun s => (w s).1) (j + 1)), w t := by
  simp only [triLayerMap, triBlock, triSegLen, triShift_iterate_fst]
  rw [blockStart_succ, sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, triShift_iterate]

theorem sum_triLayerMap_marks (eps : ℝ) (w : ℕ → Tri) (j : ℕ) :
    ∑ i ∈ range j, (triLayerMap eps w i).2 =
      ∑ t ∈ range (blockStart eps (fun s => (w s).1) j), (w t).2 := by
  simp only [triLayerMap_apply, Prod.snd_sum]
  exact sum_blocks (fun t => (w t).2) _ (by simp [blockStart])
    (blockStart_mono eps _) j

/-! ## Original input ranks and passive marks -/

variable {Ω : Type*}

theorem epLayerSeq_shGap (eps : ℝ) (g : ℕ → Ω → ℝ) (ℓ j : ℕ)
    (p : Ω × (ℕ → ℝ)) :
    epLayerSeq eps (shGap g) ℓ j p = epLayerSeq eps g ℓ j p.1 := by
  rw [epLayerSeq_eq, epLayerSeq_eq]
  rfl

theorem shTri_fst (eps : ℝ) (g : ℕ → Ω → ℝ) (ℓ j : ℕ)
    (p : Ω × (ℕ → ℝ)) :
    (shTri eps g ℓ j p).1 = epLayerSeq eps (shGap g) ℓ j p := by
  change (triLayer eps ℓ (seq (shInput g) p) j).1 = _
  rw [congrFun (triLayer_fst eps ℓ (seq (shInput g) p)) j]
  rw [epLayerSeq_eq]
  rfl

theorem shTri_fst_eq_actual (eps : ℝ) (g : ℕ → Ω → ℝ) (ℓ j : ℕ)
    (p : Ω × (ℕ → ℝ)) :
    (shTri eps g ℓ j p).1 = epLayerSeq eps g ℓ j p.1 := by
  rw [shTri_fst, epLayerSeq_shGap]

/-- The cumulative passive marks use exactly the cumulative actual input count. -/
theorem sum_shTri_marks (eps : ℝ) (g : ℕ → Ω → ℝ) (ℓ j : ℕ)
    (p : Ω × (ℕ → ℝ)) :
    ∑ i ∈ range j, (shTri eps g ℓ i p).2 =
      ∑ t ∈ range (pairRank (seq (epLayerSeq eps g ℓ) p.1) j), p.2 t := by
  induction ℓ generalizing j with
  | zero => simp [shTri, triLayer, seq, shInput, epLayerSeq, inputPairs, pairRank]
  | succ ℓ ih =>
    have ht : shTri eps g (ℓ + 1) =
        fun i q => triLayerMap eps (seq (shTri eps g ℓ) q) i := by
      funext i q
      exact congrFun (Function.iterate_succ_apply' (triLayerMap eps) ℓ
        (seq (shInput g) q)) i
    have hp : (fun s => (seq (shTri eps g ℓ) p s).1) =
        seq (epLayerSeq eps g ℓ) p.1 := by
      funext s
      exact shTri_fst_eq_actual eps g ℓ s p
    rw [ht, sum_triLayerMap_marks, hp]
    change (∑ t ∈ range (blockStart eps (seq (epLayerSeq eps g ℓ) p.1) j),
      (shTri eps g ℓ t p).2) = _
    rw [ih, seq_epLayerSeq eps g p.1 (ℓ + 1), pairLayer_succ,
      pairRank_layerMap, ← seq_epLayerSeq]

/-- Each passive mark is the sum of independent input marks over the actual tree's
input-rank interval. In particular, the interval endpoints depend only on the gaps. -/
theorem shTri_mark_eq_sum (eps : ℝ) (g : ℕ → Ω → ℝ) (ℓ j : ℕ)
    (p : Ω × (ℕ → ℝ)) :
    (shTri eps g ℓ j p).2 =
      ∑ t ∈ Ico (pairRank (seq (epLayerSeq eps g ℓ) p.1) j)
        (pairRank (seq (epLayerSeq eps g ℓ) p.1) (j + 1)), p.2 t := by
  have hj := sum_shTri_marks eps g ℓ j p
  have hj1 := sum_shTri_marks eps g ℓ (j + 1) p
  rw [sum_range_succ, hj] at hj1
  have hadd := sum_range_add_sum_Ico (fun t => p.2 t)
    (pairRank_mono (seq (epLayerSeq eps g ℓ) p.1) (Nat.le_succ j))
  linarith

/-- The leading passive mark is the sum of precisely the leading block's input count. -/
theorem shTri_zero_mark_eq_sum (eps : ℝ) (g : ℕ → Ω → ℝ) (ℓ : ℕ)
    (p : Ω × (ℕ → ℝ)) :
    (shTri eps g ℓ 0 p).2 = ∑ t ∈ range (epLayerSeq eps g ℓ 0 p.1).2, p.2 t := by
  rw [shTri_mark_eq_sum, pairRank_zero, pairRank_one, Nat.Ico_zero_eq_range]
  rfl

/-- The passive sum has exactly the actual count many summands. -/
theorem shTri_mark_eq_sum_range (eps : ℝ) (g : ℕ → Ω → ℝ) (ℓ j : ℕ)
    (p : Ω × (ℕ → ℝ)) :
    (shTri eps g ℓ j p).2 = ∑ t ∈ range (epLayerSeq eps g ℓ j p.1).2,
      p.2 (pairRank (seq (epLayerSeq eps g ℓ) p.1) j + t) := by
  rw [shTri_mark_eq_sum]
  have hr : pairRank (seq (epLayerSeq eps g ℓ) p.1) (j + 1) =
      pairRank (seq (epLayerSeq eps g ℓ) p.1) j + (epLayerSeq eps g ℓ j p.1).2 := by
    simp only [pairRank, sum_range_succ, seq]
  rw [hr, sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]

/-! ## Moments conditional on the original gaps -/

theorem integrable_expCoord_sum (a n : ℕ) :
    Integrable (fun ξ : ℕ → ℝ => ∑ t ∈ range n, ξ (a + t)) expSeqMeasure :=
  integrable_finsetSum _ fun t _ =>
    (gapLaw_expCoord.memLp_three (a + t)).integrable (by norm_num)

theorem integral_expCoord_sum (a n : ℕ) :
    ∫ ξ, (∑ t ∈ range n, ξ (a + t)) ∂expSeqMeasure = (n : ℝ) := by
  change (∫ ξ, (∑ t ∈ range n, expCoord (a + t) ξ) ∂expSeqMeasure) = _
  rw [integral_finsetSum _ fun t _ =>
    (gapLaw_expCoord.memLp_three (a + t)).integrable (by norm_num)]
  have hm (t : ℕ) : ∫ ξ, expCoord t ξ ∂expSeqMeasure = 1 :=
    (iidSeq_expCoord.integral_eq t).trans gapLaw_expCoord.mean
  simp only [hm, sum_const, card_range, nsmul_eq_mul, mul_one]

theorem memLp_expCoord_sum_sub (a n : ℕ) :
    MemLp (fun ξ : ℕ → ℝ => (∑ t ∈ range n, ξ (a + t)) - (n : ℝ)) 2 expSeqMeasure := by
  have h := gapLaw_expCoord.shift a
  have hm : MemLp (fun ξ => ∑ t ∈ range n, centred (fun t => expCoord (a + t)) 1 t ξ)
      2 expSeqMeasure :=
    memLp_finsetSum _ fun t _ => (h.memLp_centred t).mono_exponent (by norm_num)
  simpa [centred, expCoord, sum_sub_distrib] using hm

/-- A deterministic interval of `n` independent Exp(1) marks has variance `n`. -/
theorem integral_expCoord_sum_sub_sq (a n : ℕ) :
    ∫ ξ, ((∑ t ∈ range n, ξ (a + t)) - (n : ℝ)) ^ 2 ∂expSeqMeasure = (n : ℝ) := by
  have h := gapLaw_expCoord.shift a
  have horth := integral_weightedSum_sq h.indepIncrements (PredictableWeight.one _)
    (fun t => (h.memLp_centred t).mono_exponent (by norm_num)) h.integral_centred n
  simp_rw [h.integral_centred_sq] at horth
  simpa [weightedSum, centred, expCoord, sum_sub_distrib] using horth

theorem integrable_shTri_mark_fiber (eps : ℝ) (g : ℕ → Ω → ℝ) (ℓ j : ℕ) (ω : Ω) :
    Integrable (fun ξ : ℕ → ℝ => (shTri eps g ℓ j (ω, ξ)).2) expSeqMeasure := by
  simp_rw [shTri_mark_eq_sum_range]
  exact integrable_expCoord_sum _ _

/-- Conditional on the original gaps, each passive mark has mean equal to its count. -/
theorem integral_shTri_mark_fiber (eps : ℝ) (g : ℕ → Ω → ℝ) (ℓ j : ℕ) (ω : Ω) :
    ∫ ξ, (shTri eps g ℓ j (ω, ξ)).2 ∂expSeqMeasure = (epLayerSeq eps g ℓ j ω).2 := by
  simp_rw [shTri_mark_eq_sum_range]
  exact integral_expCoord_sum _ _

theorem integrable_shTri_mark_sub_sq_fiber (eps : ℝ) (g : ℕ → Ω → ℝ)
    (ℓ j : ℕ) (ω : Ω) :
    Integrable (fun ξ : ℕ → ℝ =>
      ((shTri eps g ℓ j (ω, ξ)).2 - (epLayerSeq eps g ℓ j ω).2) ^ 2) expSeqMeasure := by
  simp_rw [shTri_mark_eq_sum_range]
  exact (memLp_expCoord_sum_sub _ _).integrable_sq

/-- Conditional on the original gaps, the centered passive mark has second moment
equal to the actual input count. This holds at every layer and for every block. -/
theorem integral_shTri_mark_sub_sq_fiber (eps : ℝ) (g : ℕ → Ω → ℝ)
    (ℓ j : ℕ) (ω : Ω) :
    ∫ ξ, ((shTri eps g ℓ j (ω, ξ)).2 - (epLayerSeq eps g ℓ j ω).2) ^ 2 ∂expSeqMeasure =
      (epLayerSeq eps g ℓ j ω).2 := by
  simp_rw [shTri_mark_eq_sum_range]
  exact integral_expCoord_sum_sub_sq _ _

/-! ## Product-space transfer -/

variable [MeasurableSpace Ω] {P : Measure Ω}

/-- An iid sequence remains iid after pullback by a measure-preserving map. -/
theorem IIDSeqE.comp_measurePreserving {E Ω' : Type*} [MeasurableSpace E]
    [MeasurableSpace Ω'] {Q : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {W : ℕ → Ω → E} (hW : IIDSeqE P W)
    {f : Ω' → Ω} (hf : MeasurePreserving f Q P) :
    IIDSeqE Q (fun t q => W t (f q)) := by
  have hmap (t : ℕ) : Q.map (fun q => W t (f q)) = P.map (W t) := by
    change Q.map (W t ∘ f) = _
    rw [← Measure.map_map (hW.measurable t) hf.measurable, hf.map_eq]
  refine ⟨fun t => (hW.measurable t).comp hf.measurable, ?_, fun t => ?_⟩
  · apply (iIndepFun_iff_map_fun_eq_infinitePi_map
      (fun t => (hW.measurable t).comp hf.measurable)).2
    change Q.map (seq W ∘ f) = _
    rw [← Measure.map_map (measurable_seq hW.measurable) hf.measurable, hf.map_eq]
    simp_rw [Function.comp_def, hmap]
    exact hW.indep.map_fun_eq_infinitePi_map hW.measurable
  · exact ⟨((hW.measurable t).comp hf.measurable).aemeasurable,
      ((hW.measurable 0).comp hf.measurable).aemeasurable,
      by rw [hmap t, hmap 0, (hW.ident t).map_eq]⟩

theorem iidSeq_shGap [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} (hg : IIDSeq P g) :
    IIDSeq (shP P) (shGap g) := by
  have h : IIDSeqE P g := ⟨hg.measurable, hg.indep, hg.ident⟩
  have h' := h.comp_measurePreserving
    (measurePreserving_fst : MeasurePreserving Prod.fst (shP P) P)
  exact ⟨h'.measurable, h'.indep, h'.ident⟩

theorem iidSeq_shMarks [IsProbabilityMeasure P] :
    IIDSeq (shP P) (fun t p => p.2 t) := by
  have h : IIDSeqE expSeqMeasure expCoord :=
    ⟨iidSeq_expCoord.measurable, iidSeq_expCoord.indep, iidSeq_expCoord.ident⟩
  have h' := h.comp_measurePreserving
    (measurePreserving_snd : MeasurePreserving Prod.snd (shP P) expSeqMeasure)
  exact ⟨h'.measurable, h'.indep, h'.ident⟩

/-- The entire gap path is independent of the entire input-mark path. -/
theorem indepFun_shGap_marks [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ}
    (hg : ∀ t, Measurable (g t)) :
    IndepFun (seq (shGap g)) (fun p : Ω × (ℕ → ℝ) => p.2) (shP P) :=
  indepFun_prod (measurable_seq hg) measurable_id

theorem gapLaw_shGap [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} {μ σ κ : ℝ}
    (hg : GapLaw P g μ σ κ) : GapLaw (shP P) (shGap g) μ σ κ where
  iid := iidSeq_shGap hg.iid
  memLp3 := hg.memLp3.comp_measurePreserving measurePreserving_fst
  mean := by simpa [shGap, shP, integral_fun_fst] using hg.mean
  var := by
    change (∫ p, (g 0 p.1 - μ) ^ 2 ∂P.prod expSeqMeasure) = _
    rw [integral_fun_fst (fun ω => (g 0 ω - μ) ^ 2)]
    simpa using hg.var
  third := by
    change (∫ p, |g 0 p.1 - μ| ^ 3 ∂P.prod expSeqMeasure) ≤ _
    rw [integral_fun_fst (fun ω => |g 0 ω - μ| ^ 3)]
    simpa using hg.third
  mu_pos := hg.mu_pos
  sigma_pos := hg.sigma_pos

/-- Adding independent marks leaves every actual layer mean unchanged. -/
theorem shMean_eq [IsProbabilityMeasure P] (eps : ℝ) (g : ℕ → Ω → ℝ) (ℓ : ℕ) :
    shMean P eps g ℓ = lmean P (epLayerSeq eps g ℓ) := by
  simp only [shMean, lmean, epLayerSeq_shGap, shP]
  rw [integral_fun_fst (fun ω => (epLayerSeq eps g ℓ 0 ω).1)]
  simp

/-- Adding independent marks leaves every actual expected input count unchanged. -/
theorem shCount_eq [IsProbabilityMeasure P] (eps : ℝ) (g : ℕ → Ω → ℝ) (ℓ : ℕ) :
    shCount P eps g ℓ = lcount P (epLayerSeq eps g ℓ) := by
  simp only [shCount, lcount, epLayerSeq_shGap, shP]
  rw [integral_fun_fst (fun ω => ((epLayerSeq eps g ℓ 0 ω).2 : ℝ))]
  simp

theorem shCount_zero [IsProbabilityMeasure P] (eps : ℝ) (g : ℕ → Ω → ℝ) :
    shCount P eps g 0 = 1 := by
  simp [shCount_eq, lcount, epLayerSeq, inputPairs]

/-- The passive coordinate at layer zero is exactly its independent Exp(1) mark. -/
theorem shPair_zero_snd [IsProbabilityMeasure P] (eps : ℝ) (g : ℕ → Ω → ℝ)
    (i : ℕ) (p : Ω × (ℕ → ℝ)) :
    (shPair P eps g 0 i p).2 = p.2 i := by
  simp [shPair, shTri, triLayer, shInput, seq, shCount_zero]

theorem shLaw_zero [IsProbabilityMeasure P] (eps : ℝ) (g : ℕ → Ω → ℝ) :
    shLaw P eps g 0 = expMeasure 1 := by
  simp only [shLaw, shPair_zero_snd]
  change (P.prod expSeqMeasure).map (expCoord 0 ∘ Prod.snd) = _
  rw [← Measure.map_map (measurable_expCoord 0) measurable_snd,
    (measurePreserving_snd : MeasurePreserving Prod.snd (shP P) expSeqMeasure).map_eq,
    (hasLaw_expCoord 0).map_eq]

end

end PGM
