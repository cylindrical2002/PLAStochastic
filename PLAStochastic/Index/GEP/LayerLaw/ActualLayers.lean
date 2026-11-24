import PLAStochastic.Index.GEP.LayerLaw.Defs

/-!
# WP1: the actual endpoint layers are the orbit of the law map

For a Model G input `g` (`GapLaw`) and `eps ≥ epsZero …`, the normalised law of the
layer-`j` gap is `Φ_ε^j ν₀`, where `ν₀` is the normalised input law, and the actual mean
segment length of layer `j` is `C_ε(Φ_ε^j ν₀)`:

* `lawC_eq_segMean`: `lawC` is `segMean` on the canonical iid space;
* `gapLaw_iidLaw`: the canonical iid sequence of a law with three moments is a `GapLaw`;
* `lawC_map_mul`: `C_ε` is invariant under positive scaling of the gap law;
* `lawMean_lawPhi`: `Φ_ε` keeps mean one (Wald);
* `layer_law_orbit`: the identification of the actual layers with the orbit.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- The coordinate process of the canonical gap space. -/
def gapCoord (t : ℕ) (g : ℕ → ℝ) : ℝ := g t

/-! ## Scale invariance of the first segment -/

theorem gapKeys_const_mul (g : ℕ → ℝ) (c : ℝ) (t : ℕ) :
    gapKeys (fun s => c * g s) t = c * gapKeys g t := by
  simp [gapKeys, Finset.mul_sum]

/-- Scaling the gaps by `c ≠ 0` does not change the first segment length. -/
theorem gapSegLen_const_mul (eps : ℝ) (g : ℕ → ℝ) {c : ℝ} (hc : c ≠ 0) :
    gapSegLen eps (fun t => c * g t) = gapSegLen eps g := by
  have h := segLen_affine (eps := eps) (p := gapKeys g) (s := c) (c := 0) hc
  simp only [add_zero] at h
  show segLen eps (gapKeys fun t => c * g t) = segLen eps (gapKeys g)
  rw [← h]
  congr 1
  funext i
  exact gapKeys_const_mul g c i

theorem stopSum_const_mul (eps : ℝ) (g : ℕ → ℝ) {c : ℝ} (hc : c ≠ 0) :
    stopSum eps (fun t => c * g t) = c * stopSum eps g := by
  rw [stopSum, stopSum, gapSegLen_const_mul eps g hc, gapKeys_const_mul]

/-- The stopped sum of the gap components is the gap of the first block. -/
theorem stopSum_fst (eps : ℝ) (z : ℕ → ℝ × ℕ) :
    stopSum eps (fun t => (z t).1) = (firstBlock eps z).1 := by
  simp only [stopSum, firstBlock, Prod.fst_sum]
  rfl

theorem measurable_toNat_gapSegLen (eps : ℝ) :
    Measurable fun g : ℕ → ℝ => ((gapSegLen eps g).toNat : ℝ) :=
  (Measurable.of_discrete (f := fun n : ℕ∞ => (n.toNat : ℝ))).comp
    (isStoppingRule_gapSegLen eps).measurable

/-! ## Transfer of the law of an iid sequence -/

/-- The law of the path of an iid sequence is the canonical iid law of its marginal. -/
theorem map_seq_eq_iidLaw {X : ℕ → Ω → ℝ} (hX : IIDSeq P X) (ν : ProbabilityMeasure ℝ)
    (hν : (ν : Measure ℝ) = P.map (X 0)) : P.map (seq X) = iidLaw ν := by
  rw [iidLaw]
  change P.map (fun ω i => X i ω) = _
  rw [hX.indep.map_fun_eq_infinitePi_map hX.measurable]
  congr 1
  funext t
  rw [(hX.ident t).map_eq, hν]

theorem IIDSeq.div_const {X : ℕ → Ω → ℝ} (hX : IIDSeq P X) (m : ℝ) :
    IIDSeq P (fun t ω => X t ω / m) where
  measurable t := (hX.measurable t).div_const m
  indep := hX.indep.comp (fun _ x => x / m) (fun _ => measurable_id.div_const m)
  ident t := (hX.ident t).comp (measurable_id.div_const m)

/-- The mean first segment length of iid gaps is `C_ε` of their normalised law. -/
theorem integral_gapSegLen_eq_lawC {X : ℕ → Ω → ℝ} (hX : IIDSeq P X) (eps : ℝ) {m : ℝ}
    (hm : m ≠ 0) (ν : ProbabilityMeasure ℝ)
    (hν : (ν : Measure ℝ) = P.map (fun ω => X 0 ω / m)) :
    ∫ ω, ((gapSegLen eps (seq X ω)).toNat : ℝ) ∂P = lawC eps ν := by
  have hX' := hX.div_const m
  rw [lawC, ← map_seq_eq_iidLaw hX' ν hν, integral_map
    (measurable_seq hX'.measurable).aemeasurable
    (measurable_toNat_gapSegLen eps).aestronglyMeasurable]
  congr 1
  funext ω
  have : seq (fun t ω => X t ω / m) ω = fun t => m⁻¹ * seq X ω t := by
    funext t; simp [seq, div_eq_inv_mul]
  rw [this, gapSegLen_const_mul eps _ (inv_ne_zero hm)]

theorem lawC_eq_segMean (eps : ℝ) (ν : ProbabilityMeasure ℝ) :
    lawC eps ν = segMean (iidLaw ν) eps (inputPairs gapCoord) := by
  rfl

theorem iidSeq_gapCoord (ν : ProbabilityMeasure ℝ) : IIDSeq (iidLaw ν) gapCoord where
  measurable t := measurable_pi_apply t
  indep := iIndepFun_infinitePi (P := fun _ : ℕ => (ν : Measure ℝ)) (X := fun _ x => x)
    (fun _ => measurable_id)
  ident t := ⟨(measurable_pi_apply t).aemeasurable, (measurable_pi_apply 0).aemeasurable, by
    change (iidLaw ν).map (fun g => g t) = (iidLaw ν).map (fun g => g 0)
    rw [iidLaw, Measure.infinitePi_map_eval, Measure.infinitePi_map_eval]⟩

theorem map_gapCoord_zero (ν : ProbabilityMeasure ℝ) :
    (iidLaw ν).map (gapCoord 0) = (ν : Measure ℝ) :=
  Measure.infinitePi_map_eval _ 0

theorem integral_gapCoord_zero (ν : ProbabilityMeasure ℝ) {F : ℝ → ℝ} (hF : Measurable F) :
    ∫ g, F (gapCoord 0 g) ∂(iidLaw ν) = ∫ x, F x ∂(ν : Measure ℝ) := by
  rw [← map_gapCoord_zero ν, integral_map (φ := gapCoord 0) (f := F)
    (measurable_pi_apply 0).aemeasurable hF.aestronglyMeasurable]

theorem gapLaw_iidLaw {ν : ProbabilityMeasure ℝ} {μ σ κ : ℝ}
    (h3 : MemLp id 3 (ν : Measure ℝ)) (hμ : lawMean ν = μ) (hμpos : 0 < μ)
    (hσ : lawVar ν = σ ^ 2) (hσpos : 0 < σ)
    (hκ : ∫ x, |x - μ| ^ 3 ∂(ν : Measure ℝ) ≤ κ) :
    GapLaw (iidLaw ν) gapCoord μ σ κ where
  iid := iidSeq_gapCoord ν
  memLp3 := h3.comp_measurePreserving (measurePreserving_eval_infinitePi _ 0)
  mean := by
    rw [integral_gapCoord_zero ν (F := fun x => x) measurable_id]
    exact hμ
  var := by
    rw [integral_gapCoord_zero ν (F := fun x => (x - μ) ^ 2) (by fun_prop), ← hσ, lawVar, hμ]
  third := by
    rw [integral_gapCoord_zero ν (F := fun x => |x - μ| ^ 3) (by fun_prop)]
    exact hκ
  mu_pos := hμpos
  sigma_pos := hσpos

theorem lawC_map_mul (eps : ℝ) (ν : ProbabilityMeasure ℝ) {c : ℝ} (hc : 0 < c) :
    lawC eps (ν.map (measurable_const_mul c).aemeasurable) = lawC eps ν := by
  have h := integral_gapSegLen_eq_lawC (iidSeq_gapCoord ν) eps (inv_ne_zero hc.ne')
    (ν.map (measurable_const_mul c).aemeasurable) (by
      rw [ProbabilityMeasure.toMeasure_map]
      have : (fun g : ℕ → ℝ => gapCoord 0 g / c⁻¹) = (fun x => c * x) ∘ gapCoord 0 := by
        funext g; simp [div_inv_eq_mul, mul_comm]
      rw [this, ← Measure.map_map (measurable_const_mul c) (measurable_pi_apply 0),
        map_gapCoord_zero])
  rw [← h]
  rfl

/-- `Φ_ε` keeps mean one: Wald's identity, for a mean-one law whose first segment has
finite mean length. -/
theorem lawMean_lawPhi {eps : ℝ} {ν : ProbabilityMeasure ℝ} {σ κ : ℝ}
    (hν : GapLaw (iidLaw ν) gapCoord 1 σ κ) (hfin : ∀ᵐ g ∂(iidLaw ν), gapSegLen eps g ≠ ⊤)
    (hint : Integrable (fun g => ((gapSegLen eps g).toNat : ℝ)) (iidLaw ν))
    (hpos : 0 < lawC eps ν) :
    lawMean (lawPhi eps ν) = 1 := by
  have hZ : IIDPairs (iidLaw ν) (inputPairs gapCoord) := IIDPairs.inputPairs hν.iid
  have hW := integral_nextGap (eps := eps) (C := lawC eps ν) hZ hν hfin hint rfl
  have hS : ∫ g, stopSum eps g ∂(iidLaw ν) = lawC eps ν := by
    rw [← one_mul (lawC eps ν), ← hW]
    exact integral_congr_ae (Eventually.of_forall fun g =>
      stopSum_fst eps (seq (inputPairs gapCoord) g))
  unfold lawMean lawPhi
  rw [ProbabilityMeasure.coe_mk, integral_map (f := fun x : ℝ => x)
    ((measurable_stopSum eps).div_const _).aemeasurable aestronglyMeasurable_id, integral_div,
    hS, div_self hpos.ne']

/-- **The actual layers are the orbit of the law map.**  `ν₀` is the normalised input law. -/
theorem layer_law_orbit [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} {μ₀ σ₀ κ₀ : ℝ}
    (hg : GapLaw P g μ₀ σ₀ κ₀) {eps : ℝ}
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps)
    (ν₀ : ProbabilityMeasure ℝ) (hν₀ : (ν₀ : Measure ℝ) = P.map (fun ω => g 0 ω / μ₀))
    (j : ℕ) :
    (((lawPhi eps)^[j] ν₀ : ProbabilityMeasure ℝ) : Measure ℝ) =
        P.map (fun ω => (epLayerSeq eps g j 0 ω).1 / lmean P (epLayerSeq eps g j)) ∧
      segMean P eps (epLayerSeq eps g j) = lawC eps ((lawPhi eps)^[j] ν₀) := by
  have hμ := hg.mu_pos
  have hσ := hg.sigma_pos
  have hall := layerOK_all (layerOK_input hg) (bAbs_le_bIn μ₀ σ₀) (βAbs_le_βIn _ _)
    (vIn_pos hμ hσ) (vIn_le μ₀ σ₀) KcAbs_le_KcIn heps
  have hbpos : 0 < bIn μ₀ σ₀ := lt_of_lt_of_le bAbs_pos (bAbs_le_bIn μ₀ σ₀)
  have heps1 : 1 ≤ eps := le_trans (one_le_epsZero _ _) heps
  have hB : ∀ k (ν : ProbabilityMeasure ℝ), (ν : Measure ℝ) =
      P.map (fun ω => (epLayerSeq eps g k 0 ω).1 / lmean P (epLayerSeq eps g k)) →
      segMean P eps (epLayerSeq eps g k) = lawC eps ν := fun k ν hν =>
    integral_gapSegLen_eq_lawC (hall k).1.iid.fst eps (hall k).1.law.mu_pos.ne' ν hν
  have hA : ∀ k, (((lawPhi eps)^[k] ν₀ : ProbabilityMeasure ℝ) : Measure ℝ) =
      P.map (fun ω => (epLayerSeq eps g k 0 ω).1 / lmean P (epLayerSeq eps g k)) := by
    intro k
    induction k with
    | zero =>
      rw [show lmean P (epLayerSeq eps g 0) = μ₀ from hg.mean, Function.iterate_zero_apply]
      exact hν₀
    | succ k ih =>
      have hL := (hall k).1
      have hm : 0 < lmean P (epLayerSeq eps g k) := hL.law.mu_pos
      have hC := hB k _ ih
      have hCpos : 0 < segMean P eps (epLayerSeq eps g k) :=
        lt_of_lt_of_le (by positivity) (hall k).2.2.2.1
      have hint : Integrable (fun ω =>
          ((pairSegLen eps (seq (epLayerSeq eps g k) ω)).toNat : ℝ)) P := by
        by_contra hni
        have h0 : segMean P eps (epLayerSeq eps g k) = 0 := integral_undef hni
        linarith
      have hZ1 : epLayerSeq eps g (k + 1) = nextLayer eps (epLayerSeq eps g k) := by
        simp only [epLayerSeq, Function.iterate_succ_apply']
      have hm1 : lmean P (epLayerSeq eps g (k + 1)) =
          lmean P (epLayerSeq eps g k) * segMean P eps (epLayerSeq eps g k) := by
        rw [hZ1]
        exact integral_nextGap hL.iid hL.law (hall k).2.1 hint rfl
      have hmap := map_seq_eq_iidLaw (hL.iid.fst.div_const (lmean P (epLayerSeq eps g k)))
        ((lawPhi eps)^[k] ν₀) ih
      rw [Function.iterate_succ_apply']
      change (iidLaw ((lawPhi eps)^[k] ν₀)).map
        (fun h => stopSum eps h / lawC eps ((lawPhi eps)^[k] ν₀)) = _
      rw [← hmap, Measure.map_map ((measurable_stopSum eps).div_const _)
        (measurable_seq (hL.iid.fst.div_const _).measurable), ← hC, hm1]
      congr 1
      funext ω
      have hs : seq (fun t ω => (epLayerSeq eps g k t ω).1 / lmean P (epLayerSeq eps g k)) ω =
          fun t => (lmean P (epLayerSeq eps g k))⁻¹ * (seq (epLayerSeq eps g k) ω t).1 := by
        funext t; simp [seq, div_eq_inv_mul]
      simp only [Function.comp_apply]
      rw [hs, stopSum_const_mul eps _ (inv_ne_zero hm.ne'), stopSum_fst, hZ1]
      change _ = (firstBlock eps (seq (epLayerSeq eps g k) ω)).1 / _
      field_simp
  exact ⟨hA j, hB j _ (hA j)⟩

end

end PGM
