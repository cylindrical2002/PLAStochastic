import PLAStochastic.Index.Endpoint.ReferenceNodes
import PLAStochastic.Index.OneLayer.ThresholdMargin
import PLAStochastic.Index.Endpoint.GammaClosure
import PLAStochastic.Index.KEP.PathwiseCoupling
import PLAStochastic.Index.LocalCount.MaximalBernstein

/-!
# The reference good event of the pathwise coupling

For iid `Exp(1)` input gaps `g`, write `z' = seq (inputPairs g) ω` for the reference base pair
sequence and `W ℓ = epLayerSeq eps g ℓ` for layer `ℓ` of its endpoint hierarchy, so that
`pairLayer eps ℓ z' = seq (W ℓ) ω` (`seq_epLayerSeq`).  The reference good event `refGood`
is the conjunction, for `z'`, of the hypothesis families (M), (T), (G) of
`layerPivot_coupling_of_le` and the rank-span family (R) (every block ends at a rank `≤ d`).

* Deterministic block identities (`blockPivots_zero_eq`, `blockPivots_len_eq`,
  `blockKeySpan_eq`, `feasible_blockKeys_iff`): the reference layer-`ℓ` block `k` starts at the
  layer-`(ℓ+1)` pivot `k` and ends at the layer-`(ℓ+1)` pivot `k + 1`, its key span is the
  gap `(pairLayer eps (ℓ+1) z' k).1`, and its keys are a translate of the keys of the restarted
  layer-`ℓ` sequence `(pairShift eps)^[k] (pairLayer eps ℓ z')`.
* Per-block tails: margin failure (`measureReal_refMarginFail_le`, from `hier_margin` with the
  segment tail `measure_feasible_layer_le` derived from `refLen`), key span
  (`measureReal_refKeySpan_gt_le`, from `lcbb_lintegral_exp_fst_le`, `hyperexp_all` and Markov).
* `refGood_of_forall`: pathwise, if at most `R ℓ` layer-`ℓ` blocks start before `s` and the
  first `R ℓ` blocks of every layer `ℓ < L_top` have no stopped near-tie (`marginFail`), a short
  first segment, a small gap and a small count, the good event holds.
* `measureReal_not_refGood_le`: the union bound over the blocks `k < R ℓ` of the layers
  `ℓ < L_top`; the margin term `refMargin vmin eps (refK P eps g ℓ) (u ℓ)` keeps the local
  constant `K_ℓ = refK P eps g ℓ` symbolic.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Filter
open scoped ENNReal

/-! ## Deterministic block identities -/

section Blocks

variable {eps : ℝ} {z : ℕ → ℝ × ℕ}

/-- Block `k` of layer `ℓ` starts at the layer-`(ℓ+1)` pivot `k`. -/
theorem blockPivots_zero_eq (eps : ℝ) (z : ℕ → ℝ × ℕ) (ℓ k : ℕ) :
    blockPivots eps z ℓ k 0 = layerPivot eps z (ℓ + 1) k := by
  rw [layerPivot_succ]
  rfl

/-- Block `k` of layer `ℓ` ends at the layer-`(ℓ+1)` pivot `k + 1`. -/
theorem blockPivots_len_eq (eps : ℝ) (z : ℕ → ℝ × ℕ) (ℓ k : ℕ) :
    blockPivots eps z ℓ k (layerBlockLen eps z ℓ k) = layerPivot eps z (ℓ + 1) (k + 1) := by
  rw [layerPivot_succ, blockStart_succ]
  rfl

/-- Consecutive layer pivots differ by the count of the pair between them. -/
theorem layerPivot_succ_right (eps : ℝ) (z : ℕ → ℝ × ℕ) (ℓ k : ℕ) :
    layerPivot eps z ℓ (k + 1) = layerPivot eps z ℓ k + (pairLayer eps ℓ z k).2 := by
  simp only [layerPivot, pairRank, sum_range_succ]

/-- The key span of block `k` of layer `ℓ` is the layer-`(ℓ+1)` gap `k`. -/
theorem blockKeySpan_eq (hz : ∀ t, (z t).2 = 1) (ℓ k : ℕ) :
    pairKeys z (blockPivots eps z ℓ k (layerBlockLen eps z ℓ k)) -
      pairKeys z (blockPivots eps z ℓ k 0) = (pairLayer eps (ℓ + 1) z k).1 := by
  rw [blockPivots_len_eq, blockPivots_zero_eq, ← pairKeys_pairLayer hz,
    ← pairKeys_pairLayer hz]
  simp only [pairKeys, sum_range_succ]
  ring

/-- The keys of block `k` of layer `ℓ` are a translate of the keys of the restarted
layer-`ℓ` sequence, so they have the same feasibility. -/
theorem feasible_blockKeys_iff (hz : ∀ t, (z t).2 = 1) (θ : ℝ) (ℓ k n : ℕ) :
    prefixAffineFeasible θ (fun i => pairKeys z (blockPivots eps z ℓ k i)) n ↔
      prefixAffineFeasible θ (pairKeys ((pairShift eps)^[k] (pairLayer eps ℓ z))) n := by
  have h : (fun i => pairKeys z (blockPivots eps z ℓ k i)) = fun i =>
      1 * pairKeys ((pairShift eps)^[k] (pairLayer eps ℓ z)) i +
        pairKeys (pairLayer eps ℓ z) (blockStart eps (pairLayer eps ℓ z) k) := by
    funext i
    rw [pairShift_iterate, pairKeys_shift, blockPivots, ← pairKeys_pairLayer hz]
    ring
  rw [h, prefixAffineFeasible_affine_iff one_ne_zero]

/-- Block `k` of layer `ℓ` ends `(pairLayer eps (ℓ+1) z k).2` base ranks after its start. -/
theorem blockPivots_len_eq_add (eps : ℝ) (z : ℕ → ℝ × ℕ) (ℓ k : ℕ) :
    blockPivots eps z ℓ k (layerBlockLen eps z ℓ k) =
      blockPivots eps z ℓ k 0 + (pairLayer eps (ℓ + 1) z k).2 := by
  rw [blockPivots_len_eq, blockPivots_zero_eq, layerPivot_succ_right]

/-- Stopped near-tie event of a pair sequence: at the first failure `t` of `eps`-feasibility,
the first `t` or the first `t + 1` keys are a near-tie of tolerance `u`. -/
def marginFail (eps u : ℝ) : Set (ℕ → ℝ × ℕ) :=
  {v | ∃ t, firstFailureAt eps (pairKeys v) t ∧
    (nearTie eps u (pairKeys v) t ∨ nearTie eps u (pairKeys v) (t + 1))}

/-- **Margin of one block.**  If the restarted layer-`ℓ` sequence at block `k` has a finite
first segment and no stopped near-tie, block `k` has the margin (M) of
`layerPivot_coupling_of_le`. -/
theorem blockMargin_of_not_mem (hz : ∀ t, (z t).2 = 1) {u : ℝ} (hu : 0 ≤ u) {ℓ k : ℕ}
    (hfin : pairSegLen eps ((pairShift eps)^[k] (pairLayer eps ℓ z)) ≠ ⊤)
    (hM : (pairShift eps)^[k] (pairLayer eps ℓ z) ∉ marginFail eps u) :
    prefixAffineFeasible (eps - u) (fun i => pairKeys z (blockPivots eps z ℓ k i))
        (layerBlockLen eps z ℓ k) ∧
      ¬ prefixAffineFeasible (eps + u) (fun i => pairKeys z (blockPivots eps z ℓ k i))
        (layerBlockLen eps z ℓ k + 1) := by
  rw [feasible_blockKeys_iff hz, feasible_blockKeys_iff hz]
  have hT : pairSegLen eps ((pairShift eps)^[k] (pairLayer eps ℓ z)) =
      (layerBlockLen eps z ℓ k : ℕ∞) := (ENat.natCast_toNat hfin).symm
  have hff : firstFailureAt eps (pairKeys ((pairShift eps)^[k] (pairLayer eps ℓ z)))
      (layerBlockLen eps z ℓ k) := firstFailureAt_iff_segLen_eq.2 hT
  constructor
  · by_contra h
    exact hM ⟨_, hff, Or.inl ⟨prefixAffineFeasible_of_le hff.1 (by linarith), h⟩⟩
  · intro h
    exact hM ⟨_, hff, Or.inr ⟨h, fun h' => hff.2 (prefixAffineFeasible_of_le h' (by linarith))⟩⟩

/-- A block whose restarted sequence has first segment at most `N` has at most `N` keys. -/
theorem layerBlockLen_le_of_le {ℓ k N : ℕ}
    (h : pairSegLen eps ((pairShift eps)^[k] (pairLayer eps ℓ z)) ≤ (N : ℕ∞)) :
    layerBlockLen eps z ℓ k ≤ N :=
  ENat.toNat_le_of_le_natCast h

end Blocks

/-! ## The reference good event -/

section Event

variable {Ω : Type*}

/-- **The reference good event**: the hypothesis families (M) margin, (T) block length and
(G) key span of `layerPivot_coupling_of_le`, together with (R) rank span (the block ends at a
rank `≤ d`), for the reference base pair sequence `z' = seq (inputPairs g) ω`, for the blocks
of the layers `ℓ < L_top` starting before `s`. -/
def refGood (eps : ℝ) (g : ℕ → Ω → ℝ) (L_top s d Tmax : ℕ) (u Gmax : ℕ → ℝ) (ω : Ω) : Prop :=
  (∀ ℓ < L_top, ∀ k, blockPivots eps (seq (inputPairs g) ω) ℓ k 0 < s →
    prefixAffineFeasible (eps - u ℓ)
        (fun i => pairKeys (seq (inputPairs g) ω) (blockPivots eps (seq (inputPairs g) ω) ℓ k i))
        (layerBlockLen eps (seq (inputPairs g) ω) ℓ k) ∧
      ¬ prefixAffineFeasible (eps + u ℓ)
        (fun i => pairKeys (seq (inputPairs g) ω) (blockPivots eps (seq (inputPairs g) ω) ℓ k i))
        (layerBlockLen eps (seq (inputPairs g) ω) ℓ k + 1)) ∧
  (∀ ℓ < L_top, ∀ k, blockPivots eps (seq (inputPairs g) ω) ℓ k 0 < s →
    layerBlockLen eps (seq (inputPairs g) ω) ℓ k ≤ Tmax) ∧
  (∀ ℓ < L_top, ∀ k, blockPivots eps (seq (inputPairs g) ω) ℓ k 0 < s →
    pairKeys (seq (inputPairs g) ω) (blockPivots eps (seq (inputPairs g) ω) ℓ k
        (layerBlockLen eps (seq (inputPairs g) ω) ℓ k)) -
      pairKeys (seq (inputPairs g) ω) (blockPivots eps (seq (inputPairs g) ω) ℓ k 0) ≤ Gmax ℓ) ∧
  (∀ ℓ < L_top, ∀ k, blockPivots eps (seq (inputPairs g) ω) ℓ k 0 < s →
    blockPivots eps (seq (inputPairs g) ω) ℓ k (layerBlockLen eps (seq (inputPairs g) ω) ℓ k) ≤ d)

/-- The segment-tail rate `c₀ = 1 / (72 (5185 / vmin + 1))`, uniform over the layers. -/
def refRate (vmin : ℝ) : ℝ := 1 / (72 * (5185 / vmin + 1))

/-- The right side of `hier_margin` for the constant `K`, tolerance `u`, the rate
`c₀ = refRate vmin` and `C₀ = 2`. -/
def refMargin (vmin eps K u : ℝ) : ℝ :=
  64 * (1 / refRate vmin + 2) ^ 5 * K * eps ^ 10 * u * (1 + Real.log (1 / u)) ^ 5 + 2 * u

theorem refRate_pos {vmin : ℝ} (hv : 0 < vmin) : 0 < refRate vmin := by
  unfold refRate
  positivity

theorem refMargin_nonneg {vmin eps K u : ℝ} (hv : 0 < vmin) (hK : 0 ≤ K) (hu : 0 < u)
    (hu2 : u ≤ 1 / 2) : 0 ≤ refMargin vmin eps K u := by
  have hlog : 0 ≤ Real.log (1 / u) := Real.log_nonneg (by rw [le_div_iff₀ hu]; linarith)
  have hr := refRate_pos hv
  have he : 0 ≤ eps ^ 10 := by positivity
  unfold refMargin
  positivity

end Event

/-! ## Measurability and positivity -/

theorem measurable_pairKeys : Measurable (pairKeys : (ℕ → ℝ × ℕ) → ℕ → ℝ) :=
  measurable_pi_lambda _ fun _ =>
    Finset.measurable_sum _ fun s _ => measurable_fst.comp (measurable_pi_apply s)

theorem measurableSet_marginFail (eps u : ℝ) : MeasurableSet (marginFail eps u) := by
  have hF : ∀ θ n, MeasurableSet {v : ℕ → ℝ × ℕ | prefixAffineFeasible θ (pairKeys v) n} :=
    fun θ n => measurable_pairKeys (measurableSet_prefixAffineFeasible θ n)
  have hN : ∀ n, MeasurableSet {v : ℕ → ℝ × ℕ | nearTie eps u (pairKeys v) n} :=
    fun n => (hF _ n).inter (hF _ n).compl
  have hFF : ∀ t, MeasurableSet {v : ℕ → ℝ × ℕ | firstFailureAt eps (pairKeys v) t} :=
    fun t => (hF _ t).inter (hF _ (t + 1)).compl
  have e : marginFail eps u = ⋃ t : ℕ, ({v | firstFailureAt eps (pairKeys v) t} ∩
      ({v | nearTie eps u (pairKeys v) t} ∪ {v | nearTie eps u (pairKeys v) (t + 1)})) := by
    ext v
    simp only [marginFail, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_union]
  rw [e]
  exact MeasurableSet.iUnion fun t => (hFF t).inter ((hN t).union (hN (t + 1)))

/-- The Gamma laws put no mass on `(-∞, 0]`. -/
theorem gammaMeasure_Iic_zero (a : ℝ) : gammaMeasure a 1 (Set.Iic 0) = 0 := by
  rw [gammaMeasure, withDensity_apply _ measurableSet_Iic, setLIntegral_congr Iio_ae_eq_Iic.symm]
  exact lintegral_gammaPDF_of_nonpos le_rfl

section Prob

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Under the Gamma kernel with positive counts the gap is almost surely positive. -/
theorem ae_gap_pos {Z : ℕ → Ω → ℝ × ℕ} (hK : GammaKernel P Z)
    (hpos : ∀ᵐ ω ∂P, 1 ≤ (Z 0 ω).2) : ∀ᵐ ω ∂P, 0 < (Z 0 ω).1 := by
  have h0 := measure_count_eq_zero hpos
  rw [ae_iff]
  have e : {ω | ¬ 0 < (Z 0 ω).1} ⊆
      ⋃ m : ℕ, {ω | (Z 0 ω).1 ∈ Set.Iic 0 ∧ (Z 0 ω).2 = m} := by
    intro ω hω
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_Iic]
    exact ⟨_, not_lt.1 hω, rfl⟩
  refine measure_mono_null e (measure_iUnion_null fun m => ?_)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact measure_mono_null (fun ω hω => hω.2) h0
  · rw [hK m _ measurableSet_Iic hm, gammaMeasure_Iic_zero, mul_zero]

variable {g : ℕ → Ω → ℝ} {b β vmin Kc eps : ℝ}

theorem refLen_pos (H : RefHyp P g b β vmin Kc eps) : 0 < refLen eps vmin := by
  have h1 := H.one_le_eps
  have hv := H.hvmin0
  unfold refLen
  exact Nat.ceil_pos.2 (by positivity)

/-- The geometric tail at the scale `refLen` in the form `C₀ exp(-c₀ R / eps²)`. -/
theorem geom_le_refRate (H : RefHyp P g b β vmin Kc eps) (R : ℕ) :
    (71 / 72 : ℝ) ^ (R / refLen eps vmin) ≤ 2 * Real.exp (-(refRate vmin * R / eps ^ 2)) := by
  have hL := refLen_pos H
  have hLr := refLen_le H
  have hv := H.hvmin0
  have h1 := H.one_le_eps
  set L := refLen eps vmin with hLdef
  set q := R / L with hqdef
  set A : ℝ := 5185 / vmin + 1 with hAdef
  have hA : 0 < A := by positivity
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have he2 : 0 < eps ^ 2 := by positivity
  -- `R < (q + 1) L`
  have hq : (R : ℝ) < ((q : ℝ) + 1) * L := by
    have h1 := Nat.div_add_mod R L
    have h2 := Nat.mod_lt R hL
    have h3 : (R : ℝ) = L * q + (R % L : ℕ) := by exact_mod_cast h1.symm
    have h4 : ((R % L : ℕ) : ℝ) < L := by exact_mod_cast h2
    rw [h3]
    nlinarith
  -- `(71/72)^q ≤ exp(-q/72)`
  have hg : (71 / 72 : ℝ) ^ q ≤ Real.exp (-((q : ℝ) / 72)) := by
    have h5 : (71 / 72 : ℝ) ≤ Real.exp (-(1 / 72)) := by
      have := Real.add_one_le_exp (-(1 / 72) : ℝ)
      linarith
    calc (71 / 72 : ℝ) ^ q ≤ Real.exp (-(1 / 72)) ^ q := pow_le_pow_left₀ (by norm_num) h5 q
      _ = Real.exp (-((q : ℝ) / 72)) := by rw [← Real.exp_nat_mul]; ring_nf
  -- `q/72 ≥ c₀ R / eps² - 1/72`
  have hc : refRate vmin * R / eps ^ 2 ≤ R / (72 * L) := by
    have e : refRate vmin * R / eps ^ 2 = R / (72 * (A * eps ^ 2)) := by
      rw [refRate, hAdef]
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) (by linarith)
  have hRq : (R : ℝ) / (72 * L) < ((q : ℝ) + 1) / 72 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hexp : Real.exp (1 / 72) ≤ 2 := by
    have h := Real.exp_bound_div_one_sub_of_interval (x := 1 / 72) (by norm_num) (by norm_num)
    have : (1 : ℝ) / (1 - 1 / 72) ≤ 2 := by norm_num
    linarith
  calc (71 / 72 : ℝ) ^ q ≤ Real.exp (-((q : ℝ) / 72)) := hg
    _ ≤ Real.exp (1 / 72 + -(refRate vmin * R / eps ^ 2)) := by
        apply Real.exp_le_exp.2
        have : (q : ℝ) / 72 = ((q : ℝ) + 1) / 72 - 1 / 72 := by ring
        linarith
    _ = Real.exp (1 / 72) * Real.exp (-(refRate vmin * R / eps ^ 2)) := Real.exp_add _ _
    _ ≤ 2 * Real.exp (-(refRate vmin * R / eps ^ 2)) := by gcongr

/-- **Segment tail of every layer** in the form required by `hier_margin`:
`P(the first R + 1 layer-ℓ keys are eps-feasible) ≤ 2 exp(-c₀ R / eps²)`, `c₀ = refRate vmin`. -/
theorem measure_feasible_layer_le [IsProbabilityMeasure P] (H : RefHyp P g b β vmin Kc eps)
    (ℓ R : ℕ) :
    P {ω | prefixAffineFeasible eps (pairKeys (seq (epLayerSeq eps g ℓ) ω)) (R + 1)} ≤
      ENNReal.ofReal (2 * Real.exp (-(refRate vmin * R / eps ^ 2))) := by
  have hsub : {ω | prefixAffineFeasible eps (pairKeys (seq (epLayerSeq eps g ℓ) ω)) (R + 1)} ⊆
      {ω | (((R / refLen eps vmin) * refLen eps vmin : ℕ) : ℕ∞) <
        pairSegLen eps (seq (epLayerSeq eps g ℓ) ω)} := by
    intro ω hω
    have h1 : (R : ℕ∞) < pairSegLen eps (seq (epLayerSeq eps g ℓ) ω) := (lt_segLen_iff R).2 hω
    refine lt_of_le_of_lt ?_ h1
    exact_mod_cast Nat.div_mul_le_self R _
  calc P {ω | prefixAffineFeasible eps (pairKeys (seq (epLayerSeq eps g ℓ) ω)) (R + 1)}
      ≤ P {ω | (((R / refLen eps vmin) * refLen eps vmin : ℕ) : ℕ∞) <
          pairSegLen eps (seq (epLayerSeq eps g ℓ) ω)} := measure_mono hsub
    _ = ENNReal.ofReal (P.real {ω | (((R / refLen eps vmin) * refLen eps vmin : ℕ) : ℕ∞) <
          pairSegLen eps (seq (epLayerSeq eps g ℓ) ω)}) := by rw [ofReal_measureReal]
    _ ≤ ENNReal.ofReal ((71 / 72 : ℝ) ^ (R / refLen eps vmin)) :=
        ENNReal.ofReal_le_ofReal (measureReal_segLen_gt_le H ℓ _)
    _ ≤ ENNReal.ofReal (2 * Real.exp (-(refRate vmin * R / eps ^ 2))) :=
        ENNReal.ofReal_le_ofReal (geom_le_refRate H R)

/-- The local-bound constant `K_ℓ = m_ℓ · sup_m P(N⁽ℓ⁾ = m)` of layer `ℓ` (kept symbolic). -/
def refK (P : Measure Ω) (eps : ℝ) (g : ℕ → Ω → ℝ) (ℓ : ℕ) : ℝ :=
  lcount P (epLayerSeq eps g ℓ) * (⨆ m, P {ω | (epLayerSeq eps g ℓ 0 ω).2 = m}).toReal

theorem refK_nonneg [IsProbabilityMeasure P] (H : RefHyp P g b β vmin Kc eps) (ℓ : ℕ) :
    0 ≤ refK P eps g ℓ :=
  mul_nonneg (H.lcount_pos ℓ).le ENNReal.toReal_nonneg

/-- **Hierarchy margin of layer `ℓ`** (`hier_margin` at layer `ℓ`): the stopped near-tie event
of the layer-`ℓ` sequence has probability at most `refMargin vmin eps K_ℓ u`. -/
theorem measure_marginFail_le (hg : IIDSeq P g) (hlaw : HasLaw (g 0) (expMeasure 1) P)
    (H : RefHyp P g b β vmin Kc eps) (ℓ : ℕ) {u : ℝ} (hu : 0 < u) (hu2 : u ≤ 1 / 2) :
    P {ω | seq (epLayerSeq eps g ℓ) ω ∈ marginFail eps u} ≤
      ENNReal.ofReal (refMargin vmin eps (refK P eps g ℓ) u) := by
  have := isProbabilityMeasure_of_hasLaw_exp hlaw
  have heps0 : 0 ≤ eps := by linarith [H.one_le_eps]
  obtain ⟨hiid, hK, hpos, -⟩ := gammaClosure_epLayerSeq hg hlaw heps0 ℓ
  exact hier_margin (g := fun t ω => (epLayerSeq eps g ℓ t ω).1)
    (N := fun ω => (epLayerSeq eps g ℓ 0 ω).2) hiid.fst (ae_gap_pos hK hpos)
    (lmean_eq_lcount_epLayerSeq hg hlaw heps0 ℓ) (H.lcount_pos ℓ)
    (measure_count_eq_zero hpos) (fun m hm A hA => hK m A hA hm) H.one_le_eps hu hu2
    (by norm_num : (0 : ℝ) ≤ 2) (refRate_pos H.hvmin0)
    (fun R _ => measure_feasible_layer_le H ℓ R)

/-- **Margin failure of block `k`**: by regeneration it has the probability of block `0`. -/
theorem measureReal_refMarginFail_le (hg : IIDSeq P g) (hlaw : HasLaw (g 0) (expMeasure 1) P)
    (H : RefHyp P g b β vmin Kc eps) (ℓ k : ℕ) {u : ℝ} (hu : 0 < u) (hu2 : u ≤ 1 / 2) :
    P.real {ω | (pairShift eps)^[k] (seq (epLayerSeq eps g ℓ) ω) ∈ marginFail eps u} ≤
      refMargin vmin eps (refK P eps g ℓ) u := by
  have := isProbabilityMeasure_of_hasLaw_exp hlaw
  rw [measureReal_refShift_mem H ℓ k (measurableSet_marginFail eps u)]
  exact ENNReal.toReal_le_of_le_ofReal
    (refMargin_nonneg H.hvmin0 (refK_nonneg H ℓ) hu hu2) (measure_marginFail_le hg hlaw H ℓ hu hu2)

/-- The mean count of every layer is at least `1`. -/
theorem one_le_lcount_epLayerSeq (hg : IIDSeq P g) (hlaw : HasLaw (g 0) (expMeasure 1) P)
    (H : RefHyp P g b β vmin Kc eps) (ℓ : ℕ) : 1 ≤ lcount P (epLayerSeq eps g ℓ) := by
  have := isProbabilityMeasure_of_hasLaw_exp hlaw
  have heps0 : 0 ≤ eps := by linarith [H.one_le_eps]
  obtain ⟨-, -, hpos, -⟩ := gammaClosure_epLayerSeq hg hlaw heps0 ℓ
  have hint : Integrable (fun ω => ((epLayerSeq eps g ℓ 0 ω).2 : ℝ)) P :=
    (H.layerOK ℓ).cnt2.integrable one_le_two
  calc (1 : ℝ) = ∫ _, (1 : ℝ) ∂P := by simp
    _ ≤ ∫ ω, ((epLayerSeq eps g ℓ 0 ω).2 : ℝ) ∂P :=
        integral_mono_ae (integrable_const 1) hint
          (hpos.mono fun ω h => by
            show (1 : ℝ) ≤ ((epLayerSeq eps g ℓ 0 ω).2 : ℝ)
            exact_mod_cast h)

/-- **Key spans**: the layer-`(ℓ+1)` gap `k` (the key span of block `k` of layer `ℓ`)
satisfies `P(gap > λ m_{ℓ+1}) ≤ CK exp(-θK λ / 2)`. -/
theorem measureReal_refKeySpan_gt_le (hg : IIDSeq P g) (hlaw : HasLaw (g 0) (expMeasure 1) P)
    (H : RefHyp P g b β vmin Kc eps) (ℓ k : ℕ) (lam : ℝ) :
    P.real {ω | lam * lcount P (epLayerSeq eps g (ℓ + 1)) < (epLayerSeq eps g (ℓ + 1) k ω).1} ≤
      CK * Real.exp (-(θK * lam / 2)) := by
  have := isProbabilityMeasure_of_hasLaw_exp hlaw
  have heps0 : 0 ≤ eps := by linarith [H.one_le_eps]
  obtain ⟨hiid, hK, hpos, -⟩ := gammaClosure_epLayerSeq hg hlaw heps0 (ℓ + 1)
  have hm1 := one_le_lcount_epLayerSeq hg hlaw H (ℓ + 1)
  set Z := epLayerSeq eps g (ℓ + 1) with hZ
  set m := lcount P Z with hmdef
  have hm : 0 < m := by linarith
  -- reduce to the first pair
  have hid : IdentDistrib (fun ω => (Z k ω).1) (fun ω => (Z 0 ω).1) P P :=
    (hiid.ident k).comp measurable_fst
  have he := hid.measure_mem_eq (measurableSet_Ioi (a := lam * m))
  have he' : P.real {ω | lam * m < (Z k ω).1} = P.real {ω | lam * m < (Z 0 ω).1} := by
    simp only [measureReal_def]
    exact congrArg ENNReal.toReal he
  rw [he']
  -- the Gamma-kernel transfer `E exp(θK gap / (2m)) ≤ E exp(θK N / m) ≤ CK`
  have hθK := θK_pos
  have hθ1 := θK_le_one
  have hgam : ∀ (n : ℕ) (A : Set ℝ), MeasurableSet A →
      P {ω | (Z 0 ω).1 ∈ A ∧ (Z 0 ω).2 = n} = P {ω | (Z 0 ω).2 = n} * gammaMeasure n 1 A := by
    intro n A hA
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h0 := measure_count_eq_zero hpos
      rw [h0, zero_mul]
      exact measure_mono_null (fun ω hω => hω.2) h0
    · exact hK n A hA hn
  have hu0 : 0 ≤ θK / (2 * m) := by positivity
  have hu : θK / (2 * m) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hc : 2 * (θK / (2 * m)) ≤ θK / m := by
    rw [show 2 * (θK / (2 * m)) = θK / m by field_simp]
  have hL := lcbb_lintegral_exp_fst_le (hiid.measurable 0) hpos hgam hu0 hu hc
  obtain ⟨hint, hle⟩ := hyperexp_all H.input H.hb H.hβ H.hvmin0 H.hvmin H.hKc H.heps H.hepsK
    (ℓ + 1)
  have hR : ∫⁻ ω, ENNReal.ofReal (Real.exp (θK / m * (Z 0 ω).2)) ∂P ≤ ENNReal.ofReal CK := by
    have e : ∀ ω, θK / m * ((Z 0 ω).2 : ℝ) = θK * ((Z 0 ω).2 : ℝ) / m := fun ω => by ring
    simp_rw [e]
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ fun ω => (Real.exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal hle
  -- Markov
  set a : ℝ := θK * lam / 2 with hadef
  have hfm : AEMeasurable (fun ω => ENNReal.ofReal (Real.exp (θK / (2 * m) * (Z 0 ω).1))) P :=
    (((hiid.measurable 0).fst.const_mul _).exp.ennreal_ofReal).aemeasurable
  have hmark := mul_meas_ge_le_lintegral₀ hfm (ENNReal.ofReal (Real.exp a))
  have hsub : {ω | lam * m < (Z 0 ω).1} ⊆
      {ω | ENNReal.ofReal (Real.exp a) ≤ ENNReal.ofReal (Real.exp (θK / (2 * m) * (Z 0 ω).1))} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have e : a = θK / (2 * m) * (lam * m) := by rw [hadef]; field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left hω.le hu0
  have h1 : ENNReal.ofReal (Real.exp a) * P {ω | lam * m < (Z 0 ω).1} ≤ ENNReal.ofReal CK :=
    ((mul_le_mul_of_nonneg_left (measure_mono hsub) zero_le).trans hmark).trans (hL.trans hR)
  have h2 : P {ω | lam * m < (Z 0 ω).1} ≤ ENNReal.ofReal (CK * Real.exp (-a)) := by
    calc P {ω | lam * m < (Z 0 ω).1}
        = ENNReal.ofReal (Real.exp (-a)) * ENNReal.ofReal (Real.exp a) *
            P {ω | lam * m < (Z 0 ω).1} := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, neg_add_cancel,
            Real.exp_zero, ENNReal.ofReal_one, one_mul]
      _ = ENNReal.ofReal (Real.exp (-a)) *
            (ENNReal.ofReal (Real.exp a) * P {ω | lam * m < (Z 0 ω).1}) := mul_assoc _ _ _
      _ ≤ ENNReal.ofReal (Real.exp (-a)) * ENNReal.ofReal CK := by gcongr
      _ = ENNReal.ofReal (CK * Real.exp (-a)) := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm]
  exact ENNReal.toReal_le_of_le_ofReal (by have := CK_pos; positivity) h2

end Prob

/-! ## The union bound -/

section Main

variable {Ω : Type*} {g : ℕ → Ω → ℝ} {eps : ℝ}

/-- **Pathwise reduction.**  If at most `R ℓ` layer-`ℓ` blocks start before `s`
(`s < pairRank (seq (W (ℓ+1)) ω) (R ℓ)`) and each of the first `R ℓ` blocks has no stopped
near-tie, at most `Tmax` keys, key span at most `Gmax ℓ` and count span at most `d - s`, then
the reference good event holds. -/
theorem refGood_of_forall {L_top s d Tmax : ℕ} {u Gmax : ℕ → ℝ} {R : ℕ → ℕ} {ω : Ω}
    (hu : ∀ ℓ < L_top, 0 ≤ u ℓ)
    (h : ∀ ℓ < L_top, s < pairRank (seq (epLayerSeq eps g (ℓ + 1)) ω) (R ℓ) ∧ ∀ k < R ℓ,
      (pairShift eps)^[k] (seq (epLayerSeq eps g ℓ) ω) ∉ marginFail eps (u ℓ) ∧
      pairSegLen eps ((pairShift eps)^[k] (seq (epLayerSeq eps g ℓ) ω)) ≤ (Tmax : ℕ∞) ∧
      (epLayerSeq eps g (ℓ + 1) k ω).1 ≤ Gmax ℓ ∧
      s + (epLayerSeq eps g (ℓ + 1) k ω).2 ≤ d) :
    refGood eps g L_top s d Tmax u Gmax ω := by
  have hz : ∀ t, (seq (inputPairs g) ω t).2 = 1 := fun t => rfl
  have hw : ∀ ℓ, pairLayer eps ℓ (seq (inputPairs g) ω) = seq (epLayerSeq eps g ℓ) ω :=
    fun ℓ => (seq_epLayerSeq eps g ω ℓ).symm
  have hk : ∀ ℓ < L_top, ∀ k, blockPivots eps (seq (inputPairs g) ω) ℓ k 0 < s → k < R ℓ := by
    intro ℓ hℓ k h0
    rw [blockPivots_zero_eq] at h0
    have h0' : pairRank (seq (epLayerSeq eps g (ℓ + 1)) ω) k < s := by
      rw [← hw]
      exact h0
    by_contra hkR
    exact absurd ((pairRank_mono _ (not_lt.1 hkR)).trans_lt h0') (not_lt.2 (h ℓ hℓ).1.le)
  refine ⟨fun ℓ hℓ k h0 => ?_, fun ℓ hℓ k h0 => ?_, fun ℓ hℓ k h0 => ?_, fun ℓ hℓ k h0 => ?_⟩
  · obtain ⟨hM, hT, -, -⟩ := (h ℓ hℓ).2 k (hk ℓ hℓ k h0)
    rw [← hw] at hM hT
    exact blockMargin_of_not_mem hz (hu ℓ hℓ)
      (ne_top_of_le_ne_top (ENat.natCast_ne_top _) hT) hM
  · obtain ⟨-, hT, -, -⟩ := (h ℓ hℓ).2 k (hk ℓ hℓ k h0)
    rw [← hw] at hT
    exact layerBlockLen_le_of_le hT
  · obtain ⟨-, -, hG, -⟩ := (h ℓ hℓ).2 k (hk ℓ hℓ k h0)
    rw [blockKeySpan_eq hz, hw]
    exact hG
  · obtain ⟨-, -, -, hR⟩ := (h ℓ hℓ).2 k (hk ℓ hℓ k h0)
    rw [blockPivots_len_eq_add, hw]
    change blockPivots eps (seq (inputPairs g) ω) ℓ k 0 + (epLayerSeq eps g (ℓ + 1) k ω).2 ≤ d
    omega

variable [MeasurableSpace Ω] {P : Measure Ω} {b β vmin Kc : ℝ}

/-- **The reference good event has high probability.**  For iid `Exp(1)` input gaps under
`RefHyp`, write `m_ℓ = lcount P (epLayerSeq eps g ℓ)`.  Assume for every layer `ℓ < L_top`:
`0 < u ℓ ≤ 1/2`; `32 Kc s ≤ R ℓ · m_{ℓ+1}` (at most `R ℓ` layer-`ℓ` blocks start before `s`,
except with probability `exp(-R ℓ / (16 Kc))`); `λG m_{ℓ+1} ≤ Gmax ℓ`;
`s + λN m_{ℓ+1} ≤ d`; and `j · refLen eps vmin ≤ Tmax`.  Then the reference good event fails
with probability at most `∑_{ℓ < L_top} (exp(-R ℓ / (16 Kc)) + R ℓ (margin_ℓ + (71/72)^j +
CK e^{-θK λG / 2} + CK e^{-θK λN}))`, where `margin_ℓ = refMargin vmin eps K_ℓ (u ℓ)` is the right side of `hier_margin` at layer `ℓ`
with `K_ℓ = refK P eps g ℓ`, `c₀ = refRate vmin`, `C₀ = 2`. -/
theorem measureReal_not_refGood_le [IsProbabilityMeasure P] (hg : IIDSeq P g)
    (hlaw : HasLaw (g 0) (expMeasure 1) P) (H : RefHyp P g b β vmin Kc eps)
    {L_top s d Tmax j : ℕ} {u Gmax : ℕ → ℝ} {R : ℕ → ℕ} {lamG lamN : ℝ}
    (hu : ∀ ℓ < L_top, 0 < u ℓ ∧ u ℓ ≤ 1 / 2)
    (hRs : ∀ ℓ < L_top, 32 * Kc * s ≤ R ℓ * lcount P (epLayerSeq eps g (ℓ + 1)))
    (hTmax : j * refLen eps vmin ≤ Tmax)
    (hGmax : ∀ ℓ < L_top, lamG * lcount P (epLayerSeq eps g (ℓ + 1)) ≤ Gmax ℓ)
    (hd : ∀ ℓ < L_top, (s : ℝ) + lamN * lcount P (epLayerSeq eps g (ℓ + 1)) ≤ d) :
    P.real {ω | ¬ refGood eps g L_top s d Tmax u Gmax ω} ≤
      ∑ ℓ ∈ range L_top, (Real.exp (-(R ℓ / (16 * Kc))) +
        R ℓ * (refMargin vmin eps (refK P eps g ℓ) (u ℓ) + (71 / 72 : ℝ) ^ j +
          CK * Real.exp (-(θK * lamG / 2)) + CK * Real.exp (-(θK * lamN)))) := by
  -- the failure events
  let A0 : ℕ → Set Ω := fun ℓ => {ω | pairRank (seq (epLayerSeq eps g (ℓ + 1)) ω) (R ℓ) ≤ s}
  let AM : ℕ → ℕ → Set Ω := fun ℓ k =>
    {ω | (pairShift eps)^[k] (seq (epLayerSeq eps g ℓ) ω) ∈ marginFail eps (u ℓ)}
  let AT : ℕ → ℕ → Set Ω := fun ℓ k =>
    {ω | ((j * refLen eps vmin : ℕ) : ℕ∞) <
      pairSegLen eps ((pairShift eps)^[k] (seq (epLayerSeq eps g ℓ) ω))}
  let AG : ℕ → ℕ → Set Ω := fun ℓ k =>
    {ω | lamG * lcount P (epLayerSeq eps g (ℓ + 1)) < (epLayerSeq eps g (ℓ + 1) k ω).1}
  let AN : ℕ → ℕ → Set Ω := fun ℓ k =>
    {ω | lamN * lcount P (epLayerSeq eps g (ℓ + 1)) < ((epLayerSeq eps g (ℓ + 1) k ω).2 : ℝ)}
  let B : ℕ → Set Ω := fun ℓ =>
    A0 ℓ ∪ ⋃ k ∈ range (R ℓ), (AM ℓ k ∪ AT ℓ k ∪ AG ℓ k ∪ AN ℓ k)
  -- off the failure events the good event holds
  have hsub : {ω | ¬ refGood eps g L_top s d Tmax u Gmax ω} ⊆ ⋃ ℓ ∈ range L_top, B ℓ := by
    intro ω hω
    by_contra hno
    apply hω
    refine refGood_of_forall (R := R) (fun ℓ hℓ => (hu ℓ hℓ).1.le) (fun ℓ hℓ => ?_)
    have h1 : ω ∉ B ℓ := fun hB => hno (Set.mem_iUnion₂.2 ⟨ℓ, mem_range.2 hℓ, hB⟩)
    refine ⟨not_le.1 fun h => h1 (Or.inl h), fun k hk => ?_⟩
    have h2 : ω ∉ AM ℓ k ∪ AT ℓ k ∪ AG ℓ k ∪ AN ℓ k :=
      fun h => h1 (Or.inr (Set.mem_iUnion₂.2 ⟨k, mem_range.2 hk, h⟩))
    have hM : ω ∉ AM ℓ k := fun h => h2 (Or.inl (Or.inl (Or.inl h)))
    have hT : ¬ ((j * refLen eps vmin : ℕ) : ℕ∞) <
        pairSegLen eps ((pairShift eps)^[k] (seq (epLayerSeq eps g ℓ) ω)) :=
      fun h => h2 (Or.inl (Or.inl (Or.inr h)))
    have hG : ¬ lamG * lcount P (epLayerSeq eps g (ℓ + 1)) < (epLayerSeq eps g (ℓ + 1) k ω).1 :=
      fun h => h2 (Or.inl (Or.inr h))
    have hN : ¬ lamN * lcount P (epLayerSeq eps g (ℓ + 1)) <
        ((epLayerSeq eps g (ℓ + 1) k ω).2 : ℝ) := fun h => h2 (Or.inr h)
    refine ⟨hM, (not_lt.1 hT).trans (by exact_mod_cast hTmax),
      (not_lt.1 hG).trans (hGmax ℓ hℓ), ?_⟩
    have h3 := not_lt.1 hN
    have h4 := hd ℓ hℓ
    have h5 : ((s + (epLayerSeq eps g (ℓ + 1) k ω).2 : ℕ) : ℝ) ≤ d := by
      push_cast
      linarith
    exact_mod_cast h5
  -- the bound for one layer
  have hB : ∀ ℓ < L_top, P.real (B ℓ) ≤ Real.exp (-(R ℓ / (16 * Kc))) +
      R ℓ * (refMargin vmin eps (refK P eps g ℓ) (u ℓ) + (71 / 72 : ℝ) ^ j +
        CK * Real.exp (-(θK * lamG / 2)) + CK * Real.exp (-(θK * lamN))) := by
    intro ℓ hℓ
    have hk : ∀ k, P.real (AM ℓ k ∪ AT ℓ k ∪ AG ℓ k ∪ AN ℓ k) ≤
        refMargin vmin eps (refK P eps g ℓ) (u ℓ) + (71 / 72 : ℝ) ^ j +
          CK * Real.exp (-(θK * lamG / 2)) + CK * Real.exp (-(θK * lamN)) := by
      intro k
      have hM : P.real (AM ℓ k) ≤ refMargin vmin eps (refK P eps g ℓ) (u ℓ) :=
        measureReal_refMarginFail_le hg hlaw H ℓ k (hu ℓ hℓ).1 (hu ℓ hℓ).2
      have hT : P.real (AT ℓ k) ≤ (71 / 72 : ℝ) ^ j := measureReal_refSegLen_gt_le H ℓ k j
      have hG : P.real (AG ℓ k) ≤ CK * Real.exp (-(θK * lamG / 2)) :=
        measureReal_refKeySpan_gt_le hg hlaw H ℓ k lamG
      have hN : P.real (AN ℓ k) ≤ CK * Real.exp (-(θK * lamN)) :=
        measureReal_refSpan_gt_le H (ℓ + 1) k lamN
      calc P.real (AM ℓ k ∪ AT ℓ k ∪ AG ℓ k ∪ AN ℓ k)
          ≤ P.real (AM ℓ k ∪ AT ℓ k ∪ AG ℓ k) + P.real (AN ℓ k) := measureReal_union_le _ _
        _ ≤ P.real (AM ℓ k ∪ AT ℓ k) + P.real (AG ℓ k) + P.real (AN ℓ k) := by
            gcongr
            exact measureReal_union_le _ _
        _ ≤ P.real (AM ℓ k) + P.real (AT ℓ k) + P.real (AG ℓ k) + P.real (AN ℓ k) := by
            gcongr
            exact measureReal_union_le _ _
        _ ≤ _ := by gcongr
    calc P.real (B ℓ)
        ≤ P.real (A0 ℓ) + P.real (⋃ k ∈ range (R ℓ), (AM ℓ k ∪ AT ℓ k ∪ AG ℓ k ∪ AN ℓ k)) :=
          measureReal_union_le _ _
      _ ≤ Real.exp (-(R ℓ / (16 * Kc))) +
            ∑ k ∈ range (R ℓ), P.real (AM ℓ k ∪ AT ℓ k ∪ AG ℓ k ∪ AN ℓ k) :=
          add_le_add (measureReal_pairRank_le_of_le H (ℓ + 1) (R ℓ) s (hRs ℓ hℓ))
            (measureReal_biUnion_finset_le _ _)
      _ ≤ Real.exp (-(R ℓ / (16 * Kc))) +
            ∑ _k ∈ range (R ℓ), (refMargin vmin eps (refK P eps g ℓ) (u ℓ) +
              (71 / 72 : ℝ) ^ j + CK * Real.exp (-(θK * lamG / 2)) +
              CK * Real.exp (-(θK * lamN))) :=
          add_le_add le_rfl (sum_le_sum fun k _ => hk k)
      _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]
  calc P.real {ω | ¬ refGood eps g L_top s d Tmax u Gmax ω}
      ≤ P.real (⋃ ℓ ∈ range L_top, B ℓ) := measureReal_mono hsub (measure_ne_top P _)
    _ ≤ ∑ ℓ ∈ range L_top, P.real (B ℓ) := measureReal_biUnion_finset_le _ _
    _ ≤ _ := sum_le_sum fun ℓ hℓ => hB ℓ (mem_range.1 hℓ)

end Main

end

end PGM
