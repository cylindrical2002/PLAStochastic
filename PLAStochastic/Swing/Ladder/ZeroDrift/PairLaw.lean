import PLAStochastic.Swing.Ladder.ZeroDrift.AgeResidualTail

/-!
# The equilibrium age/residual pair, the size-biased law and the entrance law

For a law `ν` on `[0,∞)` with mean `0 < E H < ∞`:

* `sizeBiasedLaw ν = h ν(dh) / E H` is a probability law;
* `equilibriumPairLaw ν`, the image of `sizeBiasedLaw ν ⊗ Unif[0,1]` under
  `(h,v) ↦ ((1-v)h, vh)`, is a probability law with joint survival function
  `P(U > u, O > o) = Q̄(u + o)` for `u, o ≥ 0`, where `Q̄` is the equilibrium overshoot tail;
* both marginals of the pair are `equilibriumOvershootLaw ν`, and the law of `U + O` is
  `sizeBiasedLaw ν`.

For the zero-drift ladder law `ν₀` all hypotheses hold, and the entrance law
`ρ = θ Law(-O) + (1-θ) Law(-(U+O))` is a probability law because `θ` is a probability.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical MeasureTheory
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

instance isProbabilityMeasure_volume_restrict_Icc_zero_one :
    IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
  ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc, sub_zero, ENNReal.ofReal_one]⟩

/-- The map `(h, v) ↦ ((1-v)h, vh)` defining the equilibrium pair. -/
theorem measurable_equilibriumPairMap :
    Measurable (fun p : ℝ × ℝ => ((1 - p.2) * p.1, p.2 * p.1)) := by fun_prop

/-- The size-biased law is a probability law. -/
theorem sizeBiasedLaw_isProbabilityMeasure (ν : Measure ℝ) (h0 : ladderMeanENN ν ≠ 0)
    (htop : ladderMeanENN ν ≠ ⊤) : IsProbabilityMeasure (sizeBiasedLaw ν) := by
  constructor
  rw [sizeBiasedLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  simp_rw [ENNReal.div_eq_inv_mul]
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr h0), ← ladderMeanENN,
    ENNReal.inv_mul_cancel h0 htop]

theorem equilibriumPairLaw_isProbabilityMeasure (ν : Measure ℝ) (h0 : ladderMeanENN ν ≠ 0)
    (htop : ladderMeanENN ν ≠ ⊤) : IsProbabilityMeasure (equilibriumPairLaw ν) := by
  have := sizeBiasedLaw_isProbabilityMeasure ν h0 htop
  exact Measure.isProbabilityMeasure_map measurable_equilibriumPairMap.aemeasurable

/-- The uniform mass of `{v ∈ [0,1] : (1-v)h > u, vh > o}`. -/
theorem volume_pairSlice {h u o : ℝ} (hu : 0 ≤ u) (ho : 0 ≤ o) :
    volume ({v : ℝ | u < (1 - v) * h ∧ o < v * h} ∩ Icc 0 1) =
      if 0 < h then ENNReal.ofReal ((h - (u + o)) / h) else 0 := by
  split_ifs with hh
  · have hset : {v : ℝ | u < (1 - v) * h ∧ o < v * h} ∩ Icc 0 1 = Ioo (o / h) (1 - u / h) := by
      ext v
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Icc, Set.mem_Ioo]
      rw [div_lt_iff₀ hh, sub_eq_add_neg, ← sub_eq_add_neg, lt_sub_iff_add_lt, ← lt_sub_iff_add_lt',
        div_lt_iff₀ hh]
      constructor
      · rintro ⟨⟨h1, h2⟩, -⟩
        constructor <;> nlinarith
      · rintro ⟨h1, h2⟩
        have hou : 0 ≤ o / h := div_nonneg ho hh.le
        have hv0 : 0 ≤ v := by nlinarith
        refine ⟨⟨by nlinarith, by nlinarith⟩, hv0, ?_⟩
        nlinarith
    rw [hset, Real.volume_Ioo]
    congr 1
    field_simp
    ring
  · refine le_antisymm ?_ bot_le
    have hempty : {v : ℝ | u < (1 - v) * h ∧ o < v * h} ∩ Icc 0 1 = ∅ := by
      ext v
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Icc, Set.mem_empty_iff_false,
        iff_false, not_and]
      intro h1 _ hv1
      have : (1 - v) * h ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (not_lt.mp hh)
      linarith [h1.1]
    rw [hempty, measure_empty]

/-- **The joint survival function of the equilibrium pair**: for `u, o ≥ 0`,
`P(U > u, O > o) = Q̄(u + o)`. -/
theorem equilibriumPairLaw_Ioi_prod_Ioi (ν : Measure ℝ) [SFinite ν] {u o : ℝ} (hu : 0 ≤ u)
    (ho : 0 ≤ o) :
    equilibriumPairLaw ν (Ioi u ×ˢ Ioi o) = equilibriumOvershootTail ν (u + o) := by
  set s := u + o with hsdef
  have hS : MeasurableSet (Ioi u ×ˢ Ioi o) := measurableSet_Ioi.prod measurableSet_Ioi
  have hpre : MeasurableSet ((fun p : ℝ × ℝ => ((1 - p.2) * p.1, p.2 * p.1)) ⁻¹'
      (Ioi u ×ˢ Ioi o)) := measurable_equilibriumPairMap hS
  rw [equilibriumPairLaw, Measure.map_apply measurable_equilibriumPairMap hS,
    Measure.prod_apply hpre]
  set g : ℝ → ℝ≥0∞ := fun h => if 0 < h then ENNReal.ofReal ((h - s) / h) else 0 with hgdef
  have hslice : ∀ h : ℝ, (volume.restrict (Icc (0 : ℝ) 1))
      (Prod.mk h ⁻¹' ((fun p : ℝ × ℝ => ((1 - p.2) * p.1, p.2 * p.1)) ⁻¹' (Ioi u ×ˢ Ioi o))) =
      g h := by
    intro h
    have hmeas : MeasurableSet
        (Prod.mk h ⁻¹' ((fun p : ℝ × ℝ => ((1 - p.2) * p.1, p.2 * p.1)) ⁻¹'
          (Ioi u ×ˢ Ioi o))) := measurable_prodMk_left hpre
    rw [Measure.restrict_apply hmeas]
    rw [show Prod.mk h ⁻¹' ((fun p : ℝ × ℝ => ((1 - p.2) * p.1, p.2 * p.1)) ⁻¹'
        (Ioi u ×ˢ Ioi o)) = {v : ℝ | u < (1 - v) * h ∧ o < v * h} from rfl]
    exact volume_pairSlice hu ho
  simp_rw [hslice]
  have hgmeas : Measurable g :=
    Measurable.ite measurableSet_Ioi
      (ENNReal.measurable_ofReal.comp ((measurable_id.sub_const s).div measurable_id))
      measurable_const
  have hdmeas : Measurable (fun h : ℝ => ENNReal.ofReal h / ladderMeanENN ν) :=
    ENNReal.measurable_ofReal.div_const _
  rw [sizeBiasedLaw, lintegral_withDensity_eq_lintegral_mul ν hdmeas hgmeas,
    equilibriumOvershootTail_eq_lintegral]
  simp_rw [ENNReal.div_eq_inv_mul]
  have hm : Measurable (fun h : ℝ => ENNReal.ofReal (h - s)) := by fun_prop
  rw [← lintegral_const_mul _ hm]
  refine lintegral_congr fun h => ?_
  simp only [Pi.mul_apply, hgdef]
  split_ifs with hh
  · rw [mul_assoc, ← ENNReal.ofReal_mul hh.le]
    congr 2
    field_simp
  · rw [mul_zero, ENNReal.ofReal_of_nonpos (by linarith [not_lt.mp hh]), mul_zero]

theorem equilibriumOvershootTail_zero_eq_one (ν : Measure ℝ) [SFinite ν]
    (h0 : ladderMeanENN ν ≠ 0) (htop : ladderMeanENN ν ≠ ⊤) :
    equilibriumOvershootTail ν 0 = 1 := by
  rw [equilibriumOvershootTail_eq_lintegral]
  simp_rw [sub_zero]
  exact ENNReal.div_self h0 htop

/-- The equilibrium pair lives on the open positive quadrant. -/
theorem equilibriumPairLaw_quadrant_compl (ν : Measure ℝ) [SFinite ν]
    (h0 : ladderMeanENN ν ≠ 0) (htop : ladderMeanENN ν ≠ ⊤) :
    equilibriumPairLaw ν (Ioi 0 ×ˢ Ioi 0)ᶜ = 0 := by
  have := equilibriumPairLaw_isProbabilityMeasure ν h0 htop
  rw [measure_compl (measurableSet_Ioi.prod measurableSet_Ioi) (measure_ne_top _ _), measure_univ,
    equilibriumPairLaw_Ioi_prod_Ioi ν le_rfl le_rfl, add_zero,
    equilibriumOvershootTail_zero_eq_one ν h0 htop, tsub_self]

theorem equilibriumPairLaw_ae_pos (ν : Measure ℝ) [SFinite ν]
    (h0 : ladderMeanENN ν ≠ 0) (htop : ladderMeanENN ν ≠ ⊤) :
    ∀ᵐ p ∂equilibriumPairLaw ν, 0 < p.1 ∧ 0 < p.2 := by
  rw [ae_iff]
  convert equilibriumPairLaw_quadrant_compl ν h0 htop using 2
  ext p
  simp [Set.mem_prod]


/-- The second marginal of the equilibrium pair is the equilibrium overshoot law. -/
theorem equilibriumPairLaw_map_snd (ν : Measure ℝ) [SFinite ν] (hnn : 0 ≤ᵐ[ν] fun x : ℝ => x)
    (h0 : ladderMeanENN ν ≠ 0) (htop : ladderMeanENN ν ≠ ⊤) :
    (equilibriumPairLaw ν).map Prod.snd = equilibriumOvershootLaw ν := by
  have hπ := equilibriumPairLaw_isProbabilityMeasure ν h0 htop
  have hQ := equilibriumOvershootLaw_isProbabilityMeasure ν hnn h0 htop
  have hπs : IsProbabilityMeasure ((equilibriumPairLaw ν).map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have key : ∀ t : ℝ, 0 ≤ t →
      equilibriumPairLaw ν (Prod.snd ⁻¹' Ioi t) = equilibriumOvershootLaw ν (Ioi t) := by
    intro t ht
    have h1 : equilibriumPairLaw ν (Prod.snd ⁻¹' Ioi t) = equilibriumPairLaw ν (Ioi 0 ×ˢ Ioi t) := by
      refine measure_congr ?_
      filter_upwards [equilibriumPairLaw_ae_pos ν h0 htop] with p hp
      refine propext ?_
      show p.2 ∈ Ioi t ↔ p ∈ Ioi 0 ×ˢ Ioi t
      simp [Set.mem_prod, hp.1]
    rw [h1, equilibriumPairLaw_Ioi_prod_Ioi ν le_rfl ht, zero_add, equilibriumOvershootLaw_Ioi ν h0 ht]
  have hQ0 : equilibriumOvershootLaw ν (Ioi 0) = 1 := by
    rw [equilibriumOvershootLaw_Ioi ν h0 le_rfl, equilibriumOvershootTail_zero_eq_one ν h0 htop]
  refine ext_of_generate_finite (range Ioi)
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Ioi ℝ)) isPiSystem_Ioi ?_
    (by rw [measure_univ, measure_univ])
  rintro _ ⟨t, rfl⟩
  rw [Measure.map_apply measurable_snd measurableSet_Ioi]
  rcases le_or_gt 0 t with ht | ht
  · exact key t ht
  · have e1 : equilibriumPairLaw ν (Prod.snd ⁻¹' Ioi t) = 1 := by
      refine le_antisymm prob_le_one ?_
      rw [← hQ0, ← key 0 le_rfl]
      exact measure_mono (Set.preimage_mono (Ioi_subset_Ioi ht.le))
    have e2 : equilibriumOvershootLaw ν (Ioi t) = 1 := by
      refine le_antisymm prob_le_one ?_
      rw [← hQ0]
      exact measure_mono (Ioi_subset_Ioi ht.le)
    rw [e1, e2]

/-- The first marginal of the equilibrium pair is also the equilibrium overshoot law. -/
theorem equilibriumPairLaw_map_fst (ν : Measure ℝ) [SFinite ν] (hnn : 0 ≤ᵐ[ν] fun x : ℝ => x)
    (h0 : ladderMeanENN ν ≠ 0) (htop : ladderMeanENN ν ≠ ⊤) :
    (equilibriumPairLaw ν).map Prod.fst = equilibriumOvershootLaw ν := by
  have hπ := equilibriumPairLaw_isProbabilityMeasure ν h0 htop
  have hQ := equilibriumOvershootLaw_isProbabilityMeasure ν hnn h0 htop
  have hπs : IsProbabilityMeasure ((equilibriumPairLaw ν).map Prod.fst) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have key : ∀ t : ℝ, 0 ≤ t →
      equilibriumPairLaw ν (Prod.fst ⁻¹' Ioi t) = equilibriumOvershootLaw ν (Ioi t) := by
    intro t ht
    have h1 : equilibriumPairLaw ν (Prod.fst ⁻¹' Ioi t) = equilibriumPairLaw ν (Ioi t ×ˢ Ioi 0) := by
      refine measure_congr ?_
      filter_upwards [equilibriumPairLaw_ae_pos ν h0 htop] with p hp
      refine propext ?_
      show p.1 ∈ Ioi t ↔ p ∈ Ioi t ×ˢ Ioi 0
      simp [Set.mem_prod, hp.2]
    rw [h1, equilibriumPairLaw_Ioi_prod_Ioi ν ht le_rfl, add_zero, equilibriumOvershootLaw_Ioi ν h0 ht]
  have hQ0 : equilibriumOvershootLaw ν (Ioi 0) = 1 := by
    rw [equilibriumOvershootLaw_Ioi ν h0 le_rfl, equilibriumOvershootTail_zero_eq_one ν h0 htop]
  refine ext_of_generate_finite (range Ioi)
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Ioi ℝ)) isPiSystem_Ioi ?_
    (by rw [measure_univ, measure_univ])
  rintro _ ⟨t, rfl⟩
  rw [Measure.map_apply measurable_fst measurableSet_Ioi]
  rcases le_or_gt 0 t with ht | ht
  · exact key t ht
  · have e1 : equilibriumPairLaw ν (Prod.fst ⁻¹' Ioi t) = 1 := by
      refine le_antisymm prob_le_one ?_
      rw [← hQ0, ← key 0 le_rfl]
      exact measure_mono (Set.preimage_mono (Ioi_subset_Ioi ht.le))
    have e2 : equilibriumOvershootLaw ν (Ioi t) = 1 := by
      refine le_antisymm prob_le_one ?_
      rw [← hQ0]
      exact measure_mono (Ioi_subset_Ioi ht.le)
    rw [e1, e2]

/-- The law of `U + O` under the equilibrium pair is the size-biased law. -/
theorem equilibriumPairLaw_map_add (ν : Measure ℝ) :
    (equilibriumPairLaw ν).map (fun p : ℝ × ℝ => p.1 + p.2) = sizeBiasedLaw ν := by
  rw [equilibriumPairLaw, Measure.map_map (by fun_prop) measurable_equilibriumPairMap]
  have hcomp : ((fun p : ℝ × ℝ => p.1 + p.2) ∘ fun p : ℝ × ℝ => ((1 - p.2) * p.1, p.2 * p.1)) =
      Prod.fst := by
    funext p
    simp only [Function.comp_apply]
    ring
  rw [hcomp, Measure.map_fst_prod, measure_univ, one_smul]

/-! ### The zero-drift instance and the entrance law -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

theorem gaussianZeroLadder_sizeBiased_isProbabilityMeasure
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    IsProbabilityMeasure (sizeBiasedLaw (gaussianAscendingLadderLaw X μ 0)) :=
  have h := gaussianAscendingLadderLaw_zero_spreadOut hX hi hG
  sizeBiasedLaw_isProbabilityMeasure _ h.mean_ne_zero h.mean_ne_top

theorem gaussianZeroLadder_equilibrium_isProbabilityMeasure
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    IsProbabilityMeasure (equilibriumOvershootLaw (gaussianAscendingLadderLaw X μ 0)) :=
  (gaussianAscendingLadderLaw_zero_spreadOut hX hi hG).equilibrium_isProbabilityMeasure

theorem gaussianZeroLadder_pair_isProbabilityMeasure
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    IsProbabilityMeasure (equilibriumPairLaw (gaussianAscendingLadderLaw X μ 0)) :=
  have h := gaussianAscendingLadderLaw_zero_spreadOut hX hi hG
  equilibriumPairLaw_isProbabilityMeasure _ h.mean_ne_zero h.mean_ne_top

/-- The second marginal of the zero-drift equilibrium pair is the equilibrium overshoot law
of `ν₀`. -/
theorem gaussianZeroLadder_pair_map_snd
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    (equilibriumPairLaw (gaussianAscendingLadderLaw X μ 0)).map Prod.snd =
      equilibriumOvershootLaw (gaussianAscendingLadderLaw X μ 0) :=
  have h := gaussianAscendingLadderLaw_zero_spreadOut hX hi hG
  have := h.isProbabilityMeasure
  equilibriumPairLaw_map_snd _ h.ae_nonneg h.mean_ne_zero h.mean_ne_top

/-- The law of `U + O` under the zero-drift equilibrium pair is `sizeBiasedLaw ν₀`. -/
theorem gaussianZeroLadder_pair_map_add (X : ℕ → Ω → ℝ) (μ : Measure Ω) :
    (equilibriumPairLaw (gaussianAscendingLadderLaw X μ 0)).map (fun p : ℝ × ℝ => p.1 + p.2) =
      sizeBiasedLaw (gaussianAscendingLadderLaw X μ 0) :=
  equilibriumPairLaw_map_add _

theorem entranceSelectionProb_nonneg : 0 ≤ entranceSelectionProb := measureReal_nonneg

theorem entranceSelectionProb_le_one : entranceSelectionProb ≤ 1 := measureReal_le_one

/-- **The entrance law is a probability law.** -/
theorem entranceLaw_isProbabilityMeasure
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    IsProbabilityMeasure (entranceLaw X μ) := by
  have hQ := gaussianZeroLadder_equilibrium_isProbabilityMeasure hX hi hG
  have hsb := gaussianZeroLadder_sizeBiased_isProbabilityMeasure hX hi hG
  have hθ0 := entranceSelectionProb_nonneg
  have hθ1 := entranceSelectionProb_le_one
  constructor
  rw [entranceLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply (by fun_prop) MeasurableSet.univ,
    Measure.map_apply (by fun_prop) MeasurableSet.univ, Set.preimage_univ, measure_univ,
    measure_univ, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
    ← ENNReal.ofReal_add hθ0 (by linarith), add_sub_cancel, ENNReal.ofReal_one]

end SwingRepair
