import PLAStochastic.Index.GEP.Shadow.Regeneration
import PLAStochastic.Index.GEP.OrbitClosure.CyclicReduction

/-!
# Cyclic reduction for iid active/passive pairs

The active coordinate chooses the stopping time. The passive prefix sum is
invariant under simultaneous rotations of both coordinates, so the cyclic-two
bound transfers to their joint stopped law. No independence between the two
coordinates of a pair is required.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
variable {P : Measure Ω}

/-- Finite cyclic rotations preserve the joint law of an iid sequence. -/
theorem IIDSeqE.map_rot {W : ℕ → Ω → E} (hW : IIDSeqE P W) {t : ℕ} (r : Fin t) :
    P.map (fun ω (i : Fin t) => W ((i + r : Fin t) : ℕ) ω) =
      P.map (fun ω (i : Fin t) => W (i : ℕ) ω) := by
  have e1 := (hW.indep.precomp (g := fun i : Fin t => ((i + r : Fin t) : ℕ))
    (fun a b hab => add_right_cancel (Fin.val_injective hab))).map_fun_eq_pi_map
    (fun i => (hW.measurable _).aemeasurable)
  have e2 := (hW.indep.precomp (g := fun i : Fin t => (i : ℕ)) Fin.val_injective).map_fun_eq_pi_map
    (fun i => (hW.measurable _).aemeasurable)
  simp only [(hW.ident _).map_eq] at e1 e2
  exact e1.trans e2.symm

/-- Cyclic reduction with the passive prefix sum as rotation-invariant mark. -/
theorem IIDSeqE.actLen_sum_le_cyclic {V : ℕ → Ω → ℝ × ℝ} (hV : IIDSeqE P V)
    (hpos : ∀ᵐ ω ∂P, ∀ i, 0 < (V i ω).1)
    {eps : ℝ} (heps : 0 ≤ eps) {t : ℕ} (ht : 0 < t)
    {E : Set Ω} (hE : MeasurableSet E)
    (hsub : ∀ ω : Ω, (∀ i, 0 < (V i ω).1) →
      1 ≤ cyclicCount eps (fun i : Fin t => (V i ω).1) → ω ∈ E)
    {A : Set ℝ} (hA : MeasurableSet A) :
    P {ω | actLen eps V ω = (t : ℕ∞) ∧ gapKeys (fun i => (V i ω).2) t ∈ A} ≤
      2 / (t : ℝ≥0∞) * P (E ∩ {ω | gapKeys (fun i => (V i ω).2) t ∈ A}) := by
  classical
  have : NeZero t := ⟨ht.ne'⟩
  have hS : Measurable fun ω : Ω => gapKeys (fun i => (V i ω).2) t :=
    Finset.measurable_sum _ fun i _ => (hV.measurable i).snd
  have hSA : MeasurableSet {ω : Ω | gapKeys (fun i => (V i ω).2) t ∈ A} := hS hA
  have hstop : {ω : Ω | actLen eps V ω = (t : ℕ∞) ∧
      gapKeys (fun i => (V i ω).2) t ∈ A} =
      {ω : Ω | stopsAt eps (fun i : Fin t => (V i ω).1) ∧
        gapKeys (fun i => (V i ω).2) t ∈ A} := by
    ext ω
    have h := stopsAt_iff_segLen (eps := eps) (fun i => (V i ω).1) t
    change (_ ∧ _) ↔ (_ ∧ _)
    rw [h]
    rfl
  -- the rotated events
  set Ev : Set (Fin t → ℝ × ℝ) :=
    {v | stopsAt eps (fun i => (v i).1) ∧ ∑ i, (v i).2 ∈ A} with hEv
  have hEvm : MeasurableSet Ev :=
    ((measurable_pi_lambda _ fun i => (measurable_pi_apply i).fst)
      (measurableSet_stopsAt eps t)).inter ((Finset.measurable_sum _ fun i _ =>
      (measurable_pi_apply i).snd) hA)
  set R : Fin t → Ω → Fin t → ℝ × ℝ :=
    fun r ω i => V ((i + r : Fin t) : ℕ) ω with hR
  have hRm : ∀ r, Measurable (R r) := fun r => measurable_pi_lambda _ fun i =>
    hV.measurable _
  have hAm : ∀ r, MeasurableSet (R r ⁻¹' Ev) := fun r => hRm r hEvm
  have hsumrot : ∀ (g : Ω) (r : Fin t), ∑ i : Fin t, (R r g i).2 = gapKeys (fun i => (V i g).2) t := by
    intro g r
    rw [gapKeys, ← Fin.sum_univ_eq_sum_range (fun i => (V i g).2) t]
    exact Equiv.sum_comp (Equiv.addRight r) (fun i : Fin t => (V i g).2)
  have hmem : ∀ (g : Ω) (r : Fin t), g ∈ R r ⁻¹' Ev ↔
      stopsAt eps (rot (fun i : Fin t => (V i g).1) r) ∧ gapKeys (fun i => (V i g).2) t ∈ A := by
    intro g r
    simp only [Set.mem_preimage, hEv, Set.mem_ofPred_eq, hsumrot]
    rfl
  have hPA : ∀ r, P (R r ⁻¹' Ev) = P (R 0 ⁻¹' Ev) := by
    intro r
    rw [← Measure.map_apply (hRm r) hEvm, ← Measure.map_apply (hRm 0) hEvm,
      hV.map_rot r, hV.map_rot 0]
  have hA0 : R 0 ⁻¹' Ev = {g | stopsAt eps (fun i : Fin t => (V i g).1) ∧ gapKeys (fun i => (V i g).2) t ∈ A} := by
    ext g
    rw [hmem]
    have hrot0 : rot (fun i : Fin t => (V i g).1) 0 = fun i : Fin t => (V i g).1 :=
      funext fun i => by simp only [rot, add_zero]
    rw [hrot0]
    rfl
  -- the count is a sum of rotated indicators
  have hpt : ∀ g, {g : Ω | gapKeys (fun i => (V i g).2) t ∈ A}.indicator
      (fun g => (cyclicCount eps (fun i : Fin t => (V i g).1) : ℝ≥0∞)) g =
        ∑ r : Fin t, (R r ⁻¹' Ev).indicator 1 g := by
    intro g
    by_cases hk : gapKeys (fun i => (V i g).2) t ∈ A
    · rw [Set.indicator_of_mem (show g ∈ {g : Ω | gapKeys (fun i => (V i g).2) t ∈ A} from hk)]
      simp only [cyclicCount, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
        Nat.cast_zero]
      refine Finset.sum_congr rfl fun r _ => ?_
      by_cases hr : stopsAt eps (rot (fun i : Fin t => (V i g).1) r)
      · rw [if_pos hr, Set.indicator_of_mem ((hmem g r).2 ⟨hr, hk⟩), Pi.one_apply]
      · rw [if_neg hr, Set.indicator_of_notMem fun h => hr ((hmem g r).1 h).1]
    · rw [Set.indicator_of_notMem (show g ∉ {g : Ω | gapKeys (fun i => (V i g).2) t ∈ A} from hk)]
      symm
      refine Finset.sum_eq_zero fun r _ => ?_
      exact Set.indicator_of_notMem (fun h => hk ((hmem g r).1 h).2) _
  have hid : (t : ℝ≥0∞) * P (R 0 ⁻¹' Ev) = ∫⁻ g, {g : Ω | gapKeys (fun i => (V i g).2) t ∈ A}.indicator
      (fun g => (cyclicCount eps (fun i : Fin t => (V i g).1) : ℝ≥0∞)) g ∂P := by
    simp_rw [hpt]
    rw [lintegral_finsetSum _ fun r _ => measurable_one.indicator (hAm r)]
    simp_rw [lintegral_indicator_one (hAm _), hPA]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- positivity and the cyclic-two bound
  have hle : ∫⁻ g, {g : Ω | gapKeys (fun i => (V i g).2) t ∈ A}.indicator
      (fun g => (cyclicCount eps (fun i : Fin t => (V i g).1) : ℝ≥0∞)) g ∂P ≤
        ∫⁻ g, (E ∩ {g | gapKeys (fun i => (V i g).2) t ∈ A}).indicator (fun _ => (2 : ℝ≥0∞)) g ∂P := by
    refine lintegral_mono_ae (hpos.mono fun g hg => ?_)
    by_cases hk : g ∈ {g : Ω | gapKeys (fun i => (V i g).2) t ∈ A}
    · rw [Set.indicator_of_mem hk]
      by_cases hK : 1 ≤ cyclicCount eps (fun i : Fin t => (V i g).1)
      · rw [Set.indicator_of_mem (show g ∈ E ∩ {g | gapKeys (fun i => (V i g).2) t ∈ A} from ⟨hsub g hg hK, hk⟩)]
        exact_mod_cast cyclicCount_le_two heps (fun i => hg i)
      · have h0 : cyclicCount eps (fun i : Fin t => (V i g).1) = 0 := by omega
        rw [h0, Nat.cast_zero]
        exact zero_le
    · rw [Set.indicator_of_notMem hk]
      exact zero_le
  rw [lintegral_indicator_const (hE.inter hSA)] at hle
  rw [hstop, ← hA0]
  calc P (R 0 ⁻¹' Ev) = (t : ℝ≥0∞)⁻¹ * ((t : ℝ≥0∞) * P (R 0 ⁻¹' Ev)) := by
        rw [ENNReal.inv_mul_cancel_left (by exact_mod_cast ht.ne') (ENNReal.natCast_ne_top t)]
    _ ≤ (t : ℝ≥0∞)⁻¹ * (2 * P (E ∩ {g | gapKeys (fun i => (V i g).2) t ∈ A})) := by
        rw [hid]
        gcongr
    _ = 2 / (t : ℝ≥0∞) * P (E ∩ {g | gapKeys (fun i => (V i g).2) t ∈ A}) := by
        rw [div_eq_mul_inv]
        ring


/-- The cyclic bound for the passive sum evaluated at the active stopping time. -/
theorem IIDSeqE.actLen_actSum_le_cyclic {V : ℕ → Ω → ℝ × ℝ} (hV : IIDSeqE P V)
    (hpos : ∀ᵐ ω ∂P, ∀ i, 0 < (V i ω).1)
    {eps : ℝ} (heps : 0 ≤ eps) {t : ℕ} (ht : 0 < t)
    {E : Set Ω} (hE : MeasurableSet E)
    (hsub : ∀ ω : Ω, (∀ i, 0 < (V i ω).1) →
      1 ≤ cyclicCount eps (fun i : Fin t => (V i ω).1) → ω ∈ E)
    {A : Set ℝ} (hA : MeasurableSet A) :
    P {ω | actLen eps V ω = (t : ℕ∞) ∧ actSum eps V ω ∈ A} ≤
      2 / (t : ℝ≥0∞) * P (E ∩ {ω | gapKeys (fun i => (V i ω).2) t ∈ A}) := by
  have heq : {ω | actLen eps V ω = (t : ℕ∞) ∧ actSum eps V ω ∈ A} =
      {ω | actLen eps V ω = (t : ℕ∞) ∧ gapKeys (fun i => (V i ω).2) t ∈ A} := by
    ext ω
    by_cases hT : actLen eps V ω = (t : ℕ∞)
    · simp only [Set.mem_ofPred_eq, hT, true_and, actSum, ENat.toNat_natCast, gapKeys]
    · simp only [Set.mem_ofPred_eq, hT, false_and]
  rw [heq]
  exact hV.actLen_sum_le_cyclic hpos heps ht hE hsub hA

/-- Positive input gaps remain positive under finite deterministic coarsening. -/
theorem pairLayer_fst_pos {eps : ℝ} (heps : 0 ≤ eps) {z : ℕ → ℝ × ℕ}
    (hfin : AllLayersFinite eps z) (hpos : ∀ i, 0 < (z i).1) :
    ∀ ℓ j, 0 < (pairLayer eps ℓ z j).1 := by
  intro ℓ
  induction ℓ with
  | zero => exact hpos
  | succ ℓ ih =>
    intro j
    rw [pairLayer_succ, layerMap_apply, Prod.fst_sum]
    refine Finset.sum_pos' (fun i _ => (ih i).le) ?_
    exact ⟨blockStart eps (pairLayer eps ℓ z) j,
      Finset.mem_Ico.mpr ⟨le_rfl, blockStart_lt_succ heps (hfin ℓ) j⟩, ih _⟩

/-- Functions of disjoint finite sets of iid vector coordinates are independent. -/
theorem IIDSeqE.indepFun_of_disjoint {W : ℕ → Ω → E} (hW : IIDSeqE P W)
    {S T : Finset ℕ} (hST : Disjoint S T) {F G : Type*}
    [MeasurableSpace F] [MeasurableSpace G] {f : Ω → F} {g : Ω → G}
    (hf : Measurable[⨆ i ∈ (S : Set ℕ), MeasurableSpace.comap (W i) inferInstance] f)
    (hg : Measurable[⨆ i ∈ (T : Set ℕ), MeasurableSpace.comap (W i) inferInstance] g) :
    IndepFun f g P := by
  rw [IndepFun_iff_Indep]
  have hind := indep_iSup_of_disjoint (fun k => (hW.measurable k).comap_le) hW.indep.iIndep
    (Finset.disjoint_coe.mpr hST)
  exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hind hf.comap_le) hg.comap_le

/-- The law of a finite sum on an arbitrary iid space is its marginal convolution power. -/
theorem IIDSeq.map_gsum_eq_convPow [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ}
    (hY : IIDSeq P Y) (S : Finset ℕ) :
    P.map (gsum Y S) = convPow (P.map (Y 0)) S.card := by
  let ρ : ProbabilityMeasure ℝ :=
    ⟨P.map (Y 0), Measure.isProbabilityMeasure_map (hY.measurable 0).aemeasurable⟩
  have hmap := map_seq_eq_iidLaw hY ρ rfl
  calc
    P.map (gsum Y S) = (P.map (seq Y)).map (fun z => ∑ i ∈ S, z i) := by
      rw [Measure.map_map (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)
        (measurable_seq hY.measurable)]
      rfl
    _ = _ := by rw [hmap, map_sum_finset_eq_convPow]; rfl

/-- A block event of pairs factors from the passive sum outside that block.
The event may depend jointly on both coordinates inside the block. -/
theorem IIDSeqE.measure_block_inter_le [IsProbabilityMeasure P]
    {V : ℕ → Ω → ℝ × ℝ} (hV : IIDSeqE P V) {u m t : ℕ} (hut : u + m ≤ t)
    {E' : Set (Fin m → ℝ × ℝ)} (hE' : MeasurableSet E') {c : ℝ}
    (hc : LocBd c (convPow (P.map (fun ω => (V 0 ω).2)) (t - m)))
    {A : Set ℝ} (hA : MeasurableSet A) :
    P ({ω | (fun i : Fin m => V (u + i) ω) ∈ E'} ∩
      {ω | gapKeys (fun i => (V i ω).2) t ∈ A}) ≤
      P {ω | (fun i : Fin m => V (u + i) ω) ∈ E'} * (ENNReal.ofReal c * volume A) := by
  classical
  have hYseq : IIDSeq P (fun i ω => (V i ω).2) :=
    ⟨fun i => (hV.measurable i).snd, hV.indep.comp (fun _ => Prod.snd) (fun _ => measurable_snd),
      fun i => (hV.ident i).comp measurable_snd⟩
  set T : Finset ℕ := Finset.Ico u (u + m) with hT
  set S : Finset ℕ := Finset.range t \ T with hSdef
  have hTsub : T ⊆ Finset.range t := by
    intro i hi
    simp only [hT, Finset.mem_Ico] at hi
    simp only [Finset.mem_range]
    omega
  have hcard : S.card = t - m := by
    rw [hSdef, Finset.card_sdiff_of_subset hTsub, Finset.card_range, hT, Nat.card_Ico]
    omega
  set Y : Ω → ℝ := gsum (fun i ω => (V i ω).2) S with hY
  set W : Ω → Fin m → ℝ × ℝ := fun ω i => V (u + i) ω with hW
  have hYm : Measurable Y := measurable_gsum hYseq.measurable S
  have hWm : Measurable W := measurable_pi_lambda _ fun i => hV.measurable _
  have hind : IndepFun Y W P := by
    refine hV.indepFun_of_disjoint (S := S) (T := T) Finset.sdiff_disjoint ?_ ?_
    · refine Finset.measurable_sum S fun i hi => ?_
      exact (measurable_snd.comp (comap_measurable (V i))).mono
        (le_iSup₂ (f := fun i (_ : i ∈ (S : Set ℕ)) =>
          MeasurableSpace.comap (V i) inferInstance) i hi) le_rfl
    · refine @measurable_pi_lambda _ _ _
        (⨆ i ∈ (T : Set ℕ), MeasurableSpace.comap (V i) inferInstance) _ W fun i => ?_
      exact (comap_measurable (V (u + i))).mono
        (le_iSup₂ (f := fun i (_ : i ∈ (T : Set ℕ)) =>
          MeasurableSpace.comap (V i) inferInstance) (u + i) (by simp [hT])) le_rfl
  have hloc : ∀ B : Set ℝ, MeasurableSet B →
      P (Y ⁻¹' B) ≤ ENNReal.ofReal c * volume B := by
    intro B hB
    rw [← Measure.map_apply hYm hB]
    have hlaw : P.map Y = convPow (P.map (fun ω => (V 0 ω).2)) (t - m) := by
      rw [← hcard]
      exact hYseq.map_gsum_eq_convPow S
    rw [hlaw]
    exact hc B hB
  set F : Set (ℝ × (Fin m → ℝ × ℝ)) :=
    {p | p.2 ∈ E' ∧ p.1 + ∑ i, (p.2 i).2 ∈ A} with hF
  have hFm : MeasurableSet F :=
    (measurable_snd hE').inter ((measurable_fst.add (Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply i).comp measurable_snd).snd)) hA)
  have hkeys : ∀ ω : Ω, gapKeys (fun i => (V i ω).2) t = Y ω + ∑ i, (W ω i).2 := by
    intro ω
    have h1 : ∑ i : Fin m, (W ω i).2 = ∑ i ∈ T, (V i ω).2 := by
      rw [hT, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left,
        ← Fin.sum_univ_eq_sum_range (fun k => (V (u + k) ω).2) m]
    rw [h1, gapKeys]
    simp only [hY, gsum]
    exact (Finset.sum_sdiff hTsub).symm
  have hset : {ω | (fun i : Fin m => V (u + i) ω) ∈ E'} ∩
      {ω | gapKeys (fun i => (V i ω).2) t ∈ A} = (fun ω => (Y ω, W ω)) ⁻¹' F := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, hF, hkeys]
    rfl
  have key := measure_pair_le_lintegral hYm hWm hind hloc hFm
  have hslice : ∀ w : Fin m → ℝ × ℝ,
      volume ((fun x => (x, w)) ⁻¹' F) = E'.indicator (fun _ => volume A) w := by
    intro w
    by_cases hw : w ∈ E'
    · rw [Set.indicator_of_mem hw]
      have e : (fun x => (x, w)) ⁻¹' F = (fun x => x + ∑ i, (w i).2) ⁻¹' A := by
        ext x
        simp [hF, hw]
      rw [e, measure_preimage_add_right]
    · rw [Set.indicator_of_notMem hw]
      have e : (fun x => (x, w)) ⁻¹' F = ∅ := by
        ext x
        simp [hF, hw]
      rw [e, measure_empty]
  simp_rw [hslice] at key
  rw [lintegral_indicator_const hE', Measure.map_apply hWm hE'] at key
  rw [hset]
  refine key.trans (le_of_eq ?_)
  rw [show W ⁻¹' E' = {ω | (fun i : Fin m => V (u + i) ω) ∈ E'} from rfl]
  ring

/-- Block factorisation for an event reading only the active coordinates. -/
theorem IIDSeqE.measure_active_block_inter_le [IsProbabilityMeasure P]
    {V : ℕ → Ω → ℝ × ℝ} (hV : IIDSeqE P V) {u m t : ℕ} (hut : u + m ≤ t)
    {E' : Set (Fin m → ℝ)} (hE' : MeasurableSet E') {c : ℝ}
    (hc : LocBd c (convPow (P.map (fun ω => (V 0 ω).2)) (t - m)))
    {A : Set ℝ} (hA : MeasurableSet A) :
    P ({ω | (fun i : Fin m => (V (u + i) ω).1) ∈ E'} ∩
      {ω | gapKeys (fun i => (V i ω).2) t ∈ A}) ≤
      P {ω | (fun i : Fin m => (V (u + i) ω).1) ∈ E'} * (ENNReal.ofReal c * volume A) :=
  hV.measure_block_inter_le hut
    (E' := (fun v : Fin m → ℝ × ℝ => fun i => (v i).1) ⁻¹' E')
    ((measurable_pi_lambda _ fun i => (measurable_pi_apply i).fst) hE') hc hA

variable [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} {μ₀ σ₀ κ₀ eps : ℝ}

/-- Actual layer gaps are positive when the original gap law is supported on `(0,∞)`.
This support condition is separate from `GapLaw`, which only requires a positive mean. -/
theorem ae_pos_epLayerSeq_gap (hg : GapLaw P g μ₀ σ₀ κ₀)
    (hpos : ∀ᵐ ω ∂P, 0 < g 0 ω)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (ℓ j : ℕ) :
    ∀ᵐ ω ∂P, 0 < (epLayerSeq eps g ℓ j ω).1 := by
  have hall := layerOK_all (layerOK_input hg) (bAbs_le_bIn μ₀ σ₀) (βAbs_le_βIn _ _)
    (vIn_pos hg.mu_pos hg.sigma_pos) (vIn_le μ₀ σ₀) KcAbs_le_KcIn heps
  have hfin : ∀ᵐ ω ∂P, AllLayersFinite eps (seq (inputPairs g) ω) := by
    refine ae_allLayersFinite (IIDPairs.inputPairs hg.iid) eps fun k => ?_
    simpa only [seq_epLayerSeq] using (hall k).2.1
  have hposall : ∀ᵐ ω ∂P, ∀ i, 0 < g i ω :=
    ae_all_iff.mpr fun i => (hg.iid.ident i).symm.ae_snd measurableSet_Ioi hpos
  filter_upwards [hfin, hposall] with ω hω hp
  rw [epLayerSeq_eq]
  exact pairLayer_fst_pos (zero_le_one.trans ((one_le_epsZero _ _).trans heps)) hω hp ℓ j

/-- Positivity of the actual normalized active coordinate. -/
theorem ae_pos_shPair_fst (hg : GapLaw P g μ₀ σ₀ κ₀)
    (hpos : ∀ᵐ ω ∂P, 0 < g 0 ω)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (ℓ j : ℕ) :
    ∀ᵐ p ∂shP P, 0 < (shPair P eps g ℓ j p).1 := by
  have hp := (measurePreserving_fst : MeasurePreserving Prod.fst (shP P) P).quasiMeasurePreserving.ae
    (ae_pos_epLayerSeq_gap hg hpos heps ℓ j)
  filter_upwards [hp] with p hp
  simpa only [shPair, shTri_fst_eq_actual] using div_pos hp (shMean_pos hg heps ℓ)

/-- Cyclic reduction on the actual normalized shadow pairs. -/
theorem shPair_actLen_actSum_le_cyclic (hg : GapLaw P g μ₀ σ₀ κ₀)
    (hpos : ∀ᵐ ω ∂P, 0 < g 0 ω)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps)
    (ℓ : ℕ) {t : ℕ} (ht : 0 < t) {E : Set (Ω × (ℕ → ℝ))} (hE : MeasurableSet E)
    (hsub : ∀ p, (∀ i, 0 < (shPair P eps g ℓ i p).1) →
      1 ≤ cyclicCount eps (fun i : Fin t => (shPair P eps g ℓ i p).1) → p ∈ E)
    {A : Set ℝ} (hA : MeasurableSet A) :
    shP P {p | actLen eps (shPair P eps g ℓ) p = (t : ℕ∞) ∧
      actSum eps (shPair P eps g ℓ) p ∈ A} ≤
      2 / (t : ℝ≥0∞) * shP P (E ∩
        {p | gapKeys (fun i => (shPair P eps g ℓ i p).2) t ∈ A}) :=
  (iidSeqE_shPair hg heps ℓ).actLen_actSum_le_cyclic
    (ae_all_iff.mpr fun i => ae_pos_shPair_fst hg hpos heps ℓ i)
    (zero_le_one.trans ((one_le_epsZero _ _).trans heps)) ht hE hsub hA


/-- Active-block factorisation with the actual shadow law as passive marginal. -/
theorem shPair_measure_active_block_inter_le (hg : GapLaw P g μ₀ σ₀ κ₀)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps)
    (ℓ : ℕ) {u m t : ℕ} (hut : u + m ≤ t)
    {E' : Set (Fin m → ℝ)} (hE' : MeasurableSet E') {c : ℝ}
    (hc : LocBd c (convPow (shLaw P eps g ℓ) (t - m)))
    {A : Set ℝ} (hA : MeasurableSet A) :
    shP P ({p | (fun i : Fin m => (shPair P eps g ℓ (u + i) p).1) ∈ E'} ∩
      {p | gapKeys (fun i => (shPair P eps g ℓ i p).2) t ∈ A}) ≤
      shP P {p | (fun i : Fin m => (shPair P eps g ℓ (u + i) p).1) ∈ E'} *
        (ENNReal.ofReal c * volume A) :=
  (iidSeqE_shPair hg heps ℓ).measure_active_block_inter_le hut hE' hc hA

end

end PGM
